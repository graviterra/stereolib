import TetraStereo.OneCenter.LocalizedRule3ShortCircuitExecutable
import TetraStereo.OneCenter.LocalizedRule3PhysicalTopologyExecutable
import TetraStereo.OneCenter.LocalizedCompoundReachableReadCongruence
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

















































































namespace CertifiedLocalizedCIPInput

/-! ## Carrier-parent geometry -/

/-- Exact root/address facts of a member of the cipher carrier-parent list. -/
theorem rule3ActualCarrierParentFrame_facts
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (child parent : input.LocalizedCIPOccurrenceFrame)
    (present : parent ∈ input.localizedCarrierParentFrames (fuel := fuel) child) :
    parent.root = child.root ∧
      (parent.address.length + 1 = child.address.length ∧
        parent.address = child.address.dropLast) := by
  rw [localizedCarrierParentFrames, List.mem_filter] at present
  rcases present with ⟨_present, conditions⟩
  simp only [Bool.and_eq_true, beq_iff_eq] at conditions
  exact ⟨conditions.1.1, conditions.1.2, conditions.2⟩

/-- A carrier parent is an uncut tree neighbor of its child. -/
theorem rule3ActualCarrierParent_mem_neighborFrames
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (child parent : input.LocalizedCIPOccurrenceFrame)
    (present : parent ∈ input.localizedCarrierParentFrames (fuel := fuel) child) :
    parent ∈ input.localizedRerootNeighborFrames (fuel := fuel) child := by
  unfold localizedRerootNeighborFrames
  exact List.mem_append_left _ present

/-! ## Selected reference cursors -/

/-- A reference cursor selected by the actual executable selector is an executable child of the
endpoint cursor, records the endpoint occurrence as its cut, and carries the requested atom. -/
theorem rule3ActualReferenceCursor_child
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor cursor : input.LocalizedRerootCursor fuel)
    (reference : input.Atom)
    (selected : input.localizedRule3ReferenceCursorExec?
      endpointCursor reference = some cursor) :
    cursor ∈ input.executableLocalizedRerootChildren endpointCursor ∧
      cursor.previous? = some endpointCursor.occurrence ∧
      cursor.occurrence.1.node.current? = some reference := by
  have original : input.localizedRule3ReferenceCursor?
      endpointCursor reference = some cursor := by
    rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
    exact selected
  have canonical := (input.localizedRule3ReferenceCursor?_eq_some_iff
    endpointCursor cursor reference).mp original
  rcases canonical with ⟨children, childrenComputed, _derived, cursorPresent,
    cursorCurrent, _cursorPhysical, cursorPrevious, _unique⟩
  have executableEq : children =
      input.executableLocalizedRerootChildren endpointCursor := by
    have someEq : some children =
        some (input.executableLocalizedRerootChildren endpointCursor) :=
      childrenComputed.symm.trans
        (input.localizedRerootChildren?_eq_some_executable endpointCursor)
    exact Option.some.inj someEq
  refine ⟨?_, cursorPrevious, cursorCurrent⟩
  rw [← executableEq]
  exact cursorPresent

/-! ## Right endpoint: strict depth and whole-state support -/

/-- **Right-endpoint support.**  When the endpoint cursor is the recovered right cursor
`{occurrence := occurrence, previous? := some parent}`, every selected reference cursor is a
strict depth dependency of the physical occurrence, records the occurrence as its incoming cut,
is path-valid, and is an outward cursor of the occurrence. -/
theorem rule3ActualReferenceCursor_right_strict
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec?
      occurrence = some frame)
    (reference : input.Atom)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      frame.rightCursor reference = some cursor) :
    input.LocalizedDepthDependency cursor.occurrence occurrence ∧
      cursor.previous? = some occurrence ∧
      input.LocalizedRerootCursorValid cursor ∧
      input.OutwardRerootCursor occurrence cursor := by
  have declarative :=
    input.localizedRule3PhysicalEndpointCursorFrameExec?_sound occurrence frame computed
  rcases declarative with
    ⟨_real, _current, _parent, _bond, parentPresent, _leftCurrent, _leftPrevious,
      rightOcc, rightPrevious⟩
  have parentFacts := input.rule3ActualCarrierParentFrame_facts occurrence.1
    frame.leftCursor.occurrence.1 parentPresent
  have parentNeighbor : frame.leftCursor.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) occurrence.1 :=
    input.rule3ActualCarrierParent_mem_neighborFrames occurrence.1
      frame.leftCursor.occurrence.1 parentPresent
  have occurrenceNeighbor : occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel)
        frame.leftCursor.occurrence.1 :=
    input.mem_localizedRerootNeighborFrames_symm occurrence
      frame.leftCursor.occurrence.1 parentNeighbor
  have rightValid : input.LocalizedRerootCursorValid frame.rightCursor := by
    unfold LocalizedRerootCursorValid
    rw [rightPrevious, rightOcc]
    exact occurrenceNeighbor
  have referenceFacts := input.rule3ActualReferenceCursor_child
    frame.rightCursor cursor reference selected
  rcases referenceFacts with ⟨cursorChild, _cursorPrevious, _cursorCurrent⟩
  have parentShorter : frame.leftCursor.occurrence.1.address.length <
      occurrence.1.address.length := by
    omega
  have parentShorterHere : frame.leftCursor.occurrence.1.address.length <
      frame.rightCursor.occurrence.1.address.length := by
    rw [rightOcc]
    exact parentShorter
  obtain ⟨_dropLast, lengthEq, rootEq, previousEq, cursorValid⟩ :=
    input.outward_edge frame.rightCursor cursor rightValid
      frame.leftCursor.occurrence rightPrevious parentShorterHere cursorChild
  have cursorRoot : cursor.occurrence.1.root = occurrence.1.root := by
    rw [rightOcc] at rootEq
    exact rootEq
  have cursorDeeper : occurrence.1.address.length <
      cursor.occurrence.1.address.length := by
    rw [rightOcc] at lengthEq
    omega
  refine ⟨⟨cursorRoot, cursorDeeper⟩, ?_, cursorValid, ?_⟩
  · rw [previousEq, rightOcc]
  · exact ⟨cursorValid, ⟨cursorRoot, cursorDeeper⟩, occurrence,
      by rw [previousEq, rightOcc], cursorDeeper⟩

/-- Every cursor reachable from a right-endpoint reference cursor is a strict depth dependency of
the physical occurrence and is path-valid. -/
theorem rule3ActualReferenceCursor_right_reachable_dependency
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec?
      occurrence = some frame)
    (reference : input.Atom)
    (cursor child : input.LocalizedRerootCursor carrierFuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      frame.rightCursor reference = some cursor)
    (reachable : Relation.ReflTransGen (E input) cursor child) :
    input.LocalizedDepthDependency child.occurrence occurrence ∧
      input.LocalizedRerootCursorValid child := by
  have outward : input.OutwardRerootCursor occurrence cursor :=
    (input.rule3ActualReferenceCursor_right_strict occurrence frame computed
      reference cursor selected).2.2.2
  have allOutward :=
    input.outward_reachable_cursor occurrence cursor child outward reachable
  exact ⟨allOutward.2.1, allOutward.1⟩

/-- On the right-endpoint reference subtree the restricted dependency read equals the unrestricted
whole-state read at every reachable cursor. -/
theorem rule3ActualReferenceCursor_right_reachable_label_eq_state
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec?
      occurrence = some frame)
    (reference : input.Atom)
    (cursor child : input.LocalizedRerootCursor carrierFuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      frame.rightCursor reference = some cursor)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (reachable : Relation.ReflTransGen (E input) cursor child) :
    input.localizedDependencyLabel occurrence
        (input.localizedDependencyView state occurrence) child =
      state child.occurrence := by
  have dependency :=
    (input.rule3ActualReferenceCursor_right_reachable_dependency occurrence frame computed
      reference cursor child selected reachable).1
  exact input.localizedDependencyLabel_eq_state_of_dependency occurrence state child dependency

/-- **Physical right-endpoint compound-key locality.**  The whole-state through-Rule-5 compound
build at a reference cursor selected from the recovered right cursor is exactly the shipped
restricted compound build for the physical occurrence.  Both the fail-closed `none` outcome and the
computed key are covered by the full `Option` equality; no deeper-read or cycle hypothesis is
assumed. -/
theorem rule3ActualReferenceCursor_right_compound_eq_restricted
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec?
      occurrence = some frame)
    (reference : input.Atom)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      frame.rightCursor reference = some cursor)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (fuel : Nat) :
    input.buildLocalizedRerootCompoundRule45KeyWithRead?
        (fun cursor => state cursor.occurrence) fuel cursor =
      input.buildLocalizedRerootCompoundRule45Key?
        occurrence (input.localizedDependencyView state occurrence) fuel cursor := by
  calc
    input.buildLocalizedRerootCompoundRule45KeyWithRead?
        (fun cursor => state cursor.occurrence) fuel cursor =
        input.buildLocalizedRerootCompoundRule45KeyWithRead?
          (fun cursor => input.localizedDependencyLabel occurrence
            (input.localizedDependencyView state occurrence) cursor) fuel cursor :=
      input.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_of_readersAgreeOnReachable
        (fun cursor => state cursor.occurrence)
        (fun cursor => input.localizedDependencyLabel occurrence
          (input.localizedDependencyView state occurrence) cursor)
        cursor
        (by
          intro child reachable
          exact (input.rule3ActualReferenceCursor_right_reachable_label_eq_state
            occurrence frame computed reference cursor child selected state reachable).symm)
        fuel
    _ = input.buildLocalizedRerootCompoundRule45Key?
          occurrence (input.localizedDependencyView state occurrence) fuel cursor :=
      input.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel
        occurrence (input.localizedDependencyView state occurrence) fuel cursor

/-- The same physical right-endpoint locality against the executable shipped builder actually
invoked by `buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?`. -/
theorem rule3ActualReferenceCursor_right_compound_eq_restrictedExec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec?
      occurrence = some frame)
    (reference : input.Atom)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      frame.rightCursor reference = some cursor)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (fuel : Nat) :
    input.buildLocalizedRerootCompoundRule45KeyWithRead?
        (fun cursor => state cursor.occurrence) fuel cursor =
      input.buildLocalizedRerootCompoundRule45KeyExec?
        occurrence (input.localizedDependencyView state occurrence) fuel cursor := by
  rw [input.rule3ActualReferenceCursor_right_compound_eq_restricted
        occurrence frame computed reference cursor selected state fuel,
    input.buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?]

/-! ## Left endpoint: exact depth classification -/

/-- **Left-endpoint classification.**  A reference cursor selected from the recovered left cursor
`{occurrence := parent, previous? := some occurrence}` has the occurrence root and is either at
exactly the occurrence depth (outward sibling of the occurrence), or exactly two levels shallower
(the carrier parent's own parent).  It can therefore leave the physical occurrence's outward
subtree. -/
theorem rule3ActualReferenceCursor_left_depth_cases
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec?
      occurrence = some frame)
    (reference : input.Atom)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      frame.leftCursor reference = some cursor) :
    cursor.occurrence.1.root = occurrence.1.root ∧
      (cursor.occurrence.1.address.length = occurrence.1.address.length ∨
        cursor.occurrence.1.address.length + 2 = occurrence.1.address.length) := by
  have declarative :=
    input.localizedRule3PhysicalEndpointCursorFrameExec?_sound occurrence frame computed
  rcases declarative with
    ⟨_real, _current, _parent, _bond, parentPresent, _leftCurrent, _leftPrevious,
      _rightOcc, _rightPrevious⟩
  have parentFacts := input.rule3ActualCarrierParentFrame_facts occurrence.1
    frame.leftCursor.occurrence.1 parentPresent
  have referenceFacts := input.rule3ActualReferenceCursor_child
    frame.leftCursor cursor reference selected
  rcases referenceFacts with ⟨cursorChild, _cursorPrevious, _cursorCurrent⟩
  have childrenDerived : input.DeclarativeLocalizedRerootChildren frame.leftCursor
      (input.executableLocalizedRerootChildren frame.leftCursor) :=
    input.executableLocalizedRerootChildren_declarative frame.leftCursor
  have cursorIntended : cursor.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames frame.leftCursor := by
    rw [← childrenDerived.1]
    exact List.mem_map.mpr ⟨cursor, cursorChild, rfl⟩
  have neighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended
    frame.leftCursor cursor.occurrence.1 cursorIntended
  have adjacent :=
    (input.mem_localizedRerootNeighborFrames_iff
      frame.leftCursor.occurrence.1 cursor.occurrence.1).mp neighbor |>.2
  rcases adjacent with ⟨cursorRoot, parentBranch | outwardBranch⟩
  · refine ⟨cursorRoot.trans parentFacts.1, Or.inr ?_⟩
    omega
  · refine ⟨cursorRoot.trans parentFacts.1, Or.inl ?_⟩
    omega

/-- In the ancestor branch the selected reference is strictly shallower than the physical
occurrence, so the compound builder's root read is not even an occurrence-depth read. -/
theorem rule3ActualReferenceCursor_left_ancestor_not_strict
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (ancestor : cursor.occurrence.1.address.length + 2 =
      occurrence.1.address.length) :
    ¬ input.LocalizedDepthDependency cursor.occurrence occurrence := by
  intro dependency
  unfold LocalizedDepthDependency at dependency
  omega

/-! ## Outward propagation from an arbitrary cut cursor -/

/-- A cursor reached outward from an arbitrary starting cursor: it stays path-valid, keeps the
start root, never goes above the start depth, and still records a strictly shallower incoming
coordinate.  Unlike `OutwardRerootCursor` this does not require the start to be a strict dependency
of a separate target, which is exactly what the left sibling branch needs. -/
def Rule3ActualOutwardFrom
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (start cursor : input.LocalizedRerootCursor fuel) : Prop :=
  input.LocalizedRerootCursorValid cursor ∧
    cursor.occurrence.1.root = start.occurrence.1.root ∧
    start.occurrence.1.address.length ≤ cursor.occurrence.1.address.length ∧
    ∃ previous, cursor.previous? = some previous ∧
      previous.1.address.length < cursor.occurrence.1.address.length

/-- The induction invariant for outward propagation from a fixed start: the reached cursor is
outward from the start and is either the start itself or strictly deeper than it. -/
def Rule3ActualOutwardProperty
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (start cursor : input.LocalizedRerootCursor fuel) : Prop :=
  input.Rule3ActualOutwardFrom start cursor ∧
    (cursor = start ∨
      start.occurrence.1.address.length < cursor.occurrence.1.address.length)

/-- Outward propagation from an arbitrary cut cursor, with the exact depth dichotomy: the reached
cursor is the start itself or is strictly deeper than it. -/
theorem rule3ActualOutwardFrom_reachable
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (start child : input.LocalizedRerootCursor fuel)
    (startOutward : input.Rule3ActualOutwardFrom start start)
    (reachable : Relation.ReflTransGen (E input) start child) :
    input.Rule3ActualOutwardFrom start child ∧
      (child = start ∨
        start.occurrence.1.address.length < child.occurrence.1.address.length) := by
  refine (Relation.ReflTransGen.trans_induction_on (r := E input)
    (motive := fun {a b} (_path : Relation.ReflTransGen (E input) a b) =>
      input.Rule3ActualOutwardProperty start a →
        input.Rule3ActualOutwardProperty start b)
    reachable ?_ ?_ ?_) ⟨startOutward, Or.inl rfl⟩
  · intro a property
    exact property
  · intro a b edge property
    rcases property with ⟨outward, _dichotomy⟩
    rcases outward with ⟨valid, root, le, previous, previousEq, previousShorter⟩
    obtain ⟨_dropLast, lengthEq, rootEq, childPrevious, childValid⟩ :=
      input.outward_edge a b valid previous previousEq previousShorter edge
    exact ⟨⟨childValid, rootEq.trans root, by omega, a.occurrence, childPrevious,
        by omega⟩, Or.inr (by omega)⟩
  · intro a b c first second ihFirst ihSecond property
    exact ihSecond (ihFirst property)

/-- **Left sibling support at the physical occurrence.**  If the selected left reference is at
exactly the occurrence depth, then every executable-reachable cursor is either that reference
cursor itself or a strict depth dependency of the occurrence.  The compound-key root read at the
reference is therefore the *only* non-deeper read demanded by the whole reachable subtree relative
to the physical occurrence.  Relative to the actual descriptor target this read is deeper as well;
see the descriptor section below. -/
theorem rule3ActualReferenceCursor_left_sibling_support
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec?
      occurrence = some frame)
    (reference : input.Atom)
    (cursor child : input.LocalizedRerootCursor carrierFuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      frame.leftCursor reference = some cursor)
    (sibling : cursor.occurrence.1.address.length = occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) cursor child) :
    child = cursor ∨
      input.LocalizedDepthDependency child.occurrence occurrence := by
  have classification := input.rule3ActualReferenceCursor_left_depth_cases
    occurrence frame computed reference cursor selected
  have parentFacts : frame.leftCursor.occurrence.1.root = occurrence.1.root ∧
      (frame.leftCursor.occurrence.1.address.length + 1 =
          occurrence.1.address.length ∧
        frame.leftCursor.occurrence.1.address = occurrence.1.address.dropLast) := by
    have declarative :=
      input.localizedRule3PhysicalEndpointCursorFrameExec?_sound occurrence frame computed
    exact input.rule3ActualCarrierParentFrame_facts occurrence.1
      frame.leftCursor.occurrence.1 declarative.2.2.2.2.1
  have referenceFacts := input.rule3ActualReferenceCursor_child
    frame.leftCursor cursor reference selected
  rcases referenceFacts with ⟨cursorChild, cursorPrevious, _cursorCurrent⟩
  have childrenDerived : input.DeclarativeLocalizedRerootChildren frame.leftCursor
      (input.executableLocalizedRerootChildren frame.leftCursor) :=
    input.executableLocalizedRerootChildren_declarative frame.leftCursor
  have cursorValid : input.LocalizedRerootCursorValid cursor :=
    input.localizedRerootChild_valid frame.leftCursor cursor
      (input.executableLocalizedRerootChildren frame.leftCursor)
      childrenDerived cursorChild
  have incomingShorter : frame.leftCursor.occurrence.1.address.length <
      cursor.occurrence.1.address.length := by
    omega
  have startOutward : input.Rule3ActualOutwardFrom cursor cursor :=
    ⟨cursorValid, rfl, le_rfl, frame.leftCursor.occurrence, cursorPrevious,
      incomingShorter⟩
  have propagated := input.rule3ActualOutwardFrom_reachable cursor child startOutward reachable
  rcases propagated with ⟨childOutward, childDichotomy⟩
  rcases childOutward with ⟨_childValid, childRoot, _childLe, _previous, _previousEq,
    _previousShorter⟩
  rcases childDichotomy with same | deeper
  · exact Or.inl same
  · refine Or.inr ⟨?_, ?_⟩
    · exact childRoot.trans classification.1
    · omega

/-- Reader support on the physical left sibling branch: every reachable read is either the
reference root itself or agrees with the whole-state read of the physical occurrence. -/
theorem rule3ActualReferenceCursor_left_sibling_reader_support
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec?
      occurrence = some frame)
    (reference : input.Atom)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      frame.leftCursor reference = some cursor)
    (sibling : cursor.occurrence.1.address.length = occurrence.1.address.length)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (child : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) cursor child) :
    child = cursor ∨
      input.localizedDependencyLabel occurrence
          (input.localizedDependencyView state occurrence) child =
        state child.occurrence := by
  rcases input.rule3ActualReferenceCursor_left_sibling_support
    occurrence frame computed reference cursor child selected sibling reachable with
    root | dependency
  · exact Or.inl root
  · exact Or.inr
      (input.localizedDependencyLabel_eq_state_of_dependency occurrence state child dependency)

/-- At a cursor of exactly the reader target's depth the restricted reader is literally `none`,
because that cursor is not a strict dependency of the reader target. -/
theorem rule3ActualReferenceCursor_left_sibling_label_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readerTarget : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (sibling : cursor.occurrence.1.address.length = readerTarget.1.address.length)
    (view : input.LocalizedDependencyView readerTarget) :
    input.localizedDependencyLabel readerTarget view cursor = none := by
  have notDependency : ¬ input.LocalizedDepthDependency cursor.occurrence readerTarget := by
    intro dependency
    unfold LocalizedDepthDependency at dependency
    omega
  unfold localizedDependencyLabel
  rw [dif_neg notDependency]

/-- **Reader-level difference, not an endpoint counterexample.**  For a reader whose *own* target
is at exactly the reference depth there is a whole state whose stored label at the reference
differs from the restricted dependency read.  This is a statement about the reader target being the
physical occurrence (or any same-depth cursor); it is *not* the descriptor target of the actual
call.  Under the actual bridge the left sibling is strictly deeper than the descriptor target and
the two readers agree (see
`rule3ActualReferenceCursor_left_sibling_reachable_label_eq_state_of_descriptor`). -/
theorem rule3ActualReferenceCursor_left_sibling_reader_difference
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readerTarget : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (sibling : cursor.occurrence.1.address.length = readerTarget.1.address.length) :
    ∃ state : input.LocalizedAuxiliaryState carrierFuel,
      state cursor.occurrence ≠
        input.localizedDependencyLabel readerTarget
          (input.localizedDependencyView state readerTarget) cursor := by
  refine ⟨fun _ => some (.chiral .R), ?_⟩
  rw [input.rule3ActualReferenceCursor_left_sibling_label_none readerTarget cursor sibling
    (input.localizedDependencyView (fun _ => some (.chiral .R)) readerTarget)]
  simp

/-! ## Actual spatial-unit call: descriptor target versus physical occurrence -/

/-- Strict depth dependencies compose along a common root. -/
theorem rule3ActualDepthDependency_trans
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {first second third : input.LocalizedCIPOccurrence fuel}
    (firstSecond : input.LocalizedDepthDependency first second)
    (secondThird : input.LocalizedDepthDependency second third) :
    input.LocalizedDepthDependency first third := by
  unfold LocalizedDepthDependency at firstSecond secondThird ⊢
  rcases firstSecond with ⟨firstRoot, secondShorter⟩
  rcases secondThird with ⟨secondRoot, thirdShorter⟩
  exact ⟨firstRoot.trans secondRoot, by omega⟩

/-- **Actual right endpoint relative to the descriptor target.**  A reference selected from the
right endpoint cursor of the physical occurrence is a strict dependency of the original descriptor
target whenever the occurrence itself is. -/
theorem rule3ActualReferenceCursor_right_strict_of_descriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec?
      occurrence = some frame)
    (descriptor : input.LocalizedDepthDependency occurrence target)
    (reference : input.Atom)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      frame.rightCursor reference = some cursor) :
    input.LocalizedDepthDependency cursor.occurrence target := by
  have physical :=
    (input.rule3ActualReferenceCursor_right_strict occurrence frame computed
      reference cursor selected).1
  exact input.rule3ActualDepthDependency_trans physical descriptor

/-- On the actual right-reference subtree the descriptor-target restricted read equals the
unrestricted whole-state read. -/
theorem rule3ActualReferenceCursor_right_reachable_label_eq_state_of_descriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec?
      occurrence = some frame)
    (descriptor : input.LocalizedDepthDependency occurrence target)
    (reference : input.Atom)
    (cursor child : input.LocalizedRerootCursor carrierFuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      frame.rightCursor reference = some cursor)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (reachable : Relation.ReflTransGen (E input) cursor child) :
    input.localizedDependencyLabel target
        (input.localizedDependencyView state target) child =
      state child.occurrence := by
  have physical :=
    (input.rule3ActualReferenceCursor_right_reachable_dependency occurrence frame computed
      reference cursor child selected reachable).1
  have descriptorDependency : input.LocalizedDepthDependency child.occurrence target :=
    input.rule3ActualDepthDependency_trans physical descriptor
  exact input.localizedDependencyLabel_eq_state_of_dependency target state child
    descriptorDependency

/-- **Actual descriptor-target right-endpoint compound-key locality.**  The whole-state
through-Rule-5 compound build at a reference cursor selected from the right endpoint of the
physical occurrence is exactly the shipped restricted compound build for the original descriptor
target.  This is the descriptor-level statement consumed by the actual endpoint compiler; the only
geometric input is `LocalizedDepthDependency occurrence target`. -/
theorem rule3ActualReferenceCursor_right_compound_eq_restricted_of_descriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec?
      occurrence = some frame)
    (descriptor : input.LocalizedDepthDependency occurrence target)
    (reference : input.Atom)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      frame.rightCursor reference = some cursor)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (fuel : Nat) :
    input.buildLocalizedRerootCompoundRule45KeyWithRead?
        (fun cursor => state cursor.occurrence) fuel cursor =
      input.buildLocalizedRerootCompoundRule45Key?
        target (input.localizedDependencyView state target) fuel cursor := by
  calc
    input.buildLocalizedRerootCompoundRule45KeyWithRead?
        (fun cursor => state cursor.occurrence) fuel cursor =
        input.buildLocalizedRerootCompoundRule45KeyWithRead?
          (fun cursor => input.localizedDependencyLabel target
            (input.localizedDependencyView state target) cursor) fuel cursor :=
      input.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_of_readersAgreeOnReachable
        (fun cursor => state cursor.occurrence)
        (fun cursor => input.localizedDependencyLabel target
          (input.localizedDependencyView state target) cursor)
        cursor
        (by
          intro child reachable
          exact (input.rule3ActualReferenceCursor_right_reachable_label_eq_state_of_descriptor
            occurrence target frame computed descriptor reference cursor child selected state
            reachable).symm)
        fuel
    _ = input.buildLocalizedRerootCompoundRule45Key?
          target (input.localizedDependencyView state target) fuel cursor :=
      input.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel
        target (input.localizedDependencyView state target) fuel cursor

/-- The descriptor-level locality against the executable shipped builder actually invoked by
`buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?`. -/
theorem rule3ActualReferenceCursor_right_compound_eq_restrictedExec_of_descriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec?
      occurrence = some frame)
    (descriptor : input.LocalizedDepthDependency occurrence target)
    (reference : input.Atom)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      frame.rightCursor reference = some cursor)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (fuel : Nat) :
    input.buildLocalizedRerootCompoundRule45KeyWithRead?
        (fun cursor => state cursor.occurrence) fuel cursor =
      input.buildLocalizedRerootCompoundRule45KeyExec?
        target (input.localizedDependencyView state target) fuel cursor := by
  rw [input.rule3ActualReferenceCursor_right_compound_eq_restricted_of_descriptor
        occurrence target frame computed descriptor reference cursor selected state fuel,
    input.buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?]

/-- **Actual left sibling relative to the descriptor target.**  Under the bridge, a left reference
at the physical occurrence depth is a strict dependency of the original descriptor target. -/
theorem rule3ActualReferenceCursor_left_sibling_strict_of_descriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec?
      occurrence = some frame)
    (descriptor : input.LocalizedDepthDependency occurrence target)
    (reference : input.Atom)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      frame.leftCursor reference = some cursor)
    (sibling : cursor.occurrence.1.address.length = occurrence.1.address.length) :
    input.LocalizedDepthDependency cursor.occurrence target := by
  have classification := input.rule3ActualReferenceCursor_left_depth_cases
    occurrence frame computed reference cursor selected
  rcases descriptor with ⟨occurrenceRoot, targetShorter⟩
  exact ⟨classification.1.trans occurrenceRoot, by omega⟩

/-- **Entire left outward sibling subtree is safe relative to the descriptor target.**  Every
executable-reachable cursor below the selected left sibling is a strict dependency of the original
descriptor target. -/
theorem rule3ActualReferenceCursor_left_sibling_subtree_strict_of_descriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec?
      occurrence = some frame)
    (descriptor : input.LocalizedDepthDependency occurrence target)
    (reference : input.Atom)
    (cursor child : input.LocalizedRerootCursor carrierFuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      frame.leftCursor reference = some cursor)
    (sibling : cursor.occurrence.1.address.length = occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) cursor child) :
    input.LocalizedDepthDependency child.occurrence target := by
  have siblingStrict :=
    input.rule3ActualReferenceCursor_left_sibling_strict_of_descriptor
      occurrence target frame computed descriptor reference cursor selected sibling
  rcases input.rule3ActualReferenceCursor_left_sibling_support
    occurrence frame computed reference cursor child selected sibling reachable with
    rfl | physicalDependency
  · exact siblingStrict
  · exact input.rule3ActualDepthDependency_trans physicalDependency descriptor

/-- On the actual left sibling subtree the descriptor-target restricted read equals the
unrestricted whole-state read at every reachable cursor. -/
theorem rule3ActualReferenceCursor_left_sibling_reachable_label_eq_state_of_descriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec?
      occurrence = some frame)
    (descriptor : input.LocalizedDepthDependency occurrence target)
    (reference : input.Atom)
    (cursor child : input.LocalizedRerootCursor carrierFuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      frame.leftCursor reference = some cursor)
    (sibling : cursor.occurrence.1.address.length = occurrence.1.address.length)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (reachable : Relation.ReflTransGen (E input) cursor child) :
    input.localizedDependencyLabel target
        (input.localizedDependencyView state target) child =
      state child.occurrence := by
  have dependency :=
    input.rule3ActualReferenceCursor_left_sibling_subtree_strict_of_descriptor
      occurrence target frame computed descriptor reference cursor child selected sibling reachable
  exact input.localizedDependencyLabel_eq_state_of_dependency target state child dependency

/-- **Exact residual of the left endpoint.**  A left reference that is *not* a strict dependency of
the descriptor target must be the ancestor branch, and then the physical occurrence is only one or
two levels below the descriptor target.  In the sibling branch the reference is always strict under
the bridge. -/
theorem rule3ActualReferenceCursor_left_nonstrict_descriptor_is_ancestor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec?
      occurrence = some frame)
    (descriptor : input.LocalizedDepthDependency occurrence target)
    (reference : input.Atom)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      frame.leftCursor reference = some cursor)
    (notStrict : ¬ input.LocalizedDepthDependency cursor.occurrence target) :
    cursor.occurrence.1.address.length + 2 = occurrence.1.address.length ∧
      (occurrence.1.address.length = target.1.address.length + 1 ∨
        occurrence.1.address.length = target.1.address.length + 2) := by
  have classification := input.rule3ActualReferenceCursor_left_depth_cases
    occurrence frame computed reference cursor selected
  rcases classification with ⟨cursorRoot, sibling | ancestor⟩
  · exfalso
    rcases descriptor with ⟨occurrenceRoot, targetShorter⟩
    exact notStrict ⟨cursorRoot.trans occurrenceRoot, by omega⟩
  · refine ⟨ancestor, ?_⟩
    have notTargetDeeper : ¬ target.1.address.length <
        cursor.occurrence.1.address.length := by
      intro deeper
      rcases descriptor with ⟨occurrenceRoot, _occurrenceShorter⟩
      exact notStrict ⟨cursorRoot.trans occurrenceRoot, deeper⟩
    rcases descriptor with ⟨_occurrenceRoot, occurrenceShorter⟩
    omega

/-- **Ancestor branch with a genuine gap is safe.**  If the physical occurrence is at least three
levels below the descriptor target, the ancestor reference (two levels below the occurrence) is
still a strict dependency of the descriptor target. -/
theorem rule3ActualReferenceCursor_left_ancestor_strict_of_descriptor_of_gap
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec?
      occurrence = some frame)
    (descriptor : input.LocalizedDepthDependency occurrence target)
    (reference : input.Atom)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      frame.leftCursor reference = some cursor)
    (ancestor : cursor.occurrence.1.address.length + 2 = occurrence.1.address.length)
    (gap : target.1.address.length + 2 < occurrence.1.address.length) :
    input.LocalizedDepthDependency cursor.occurrence target := by
  have classification := input.rule3ActualReferenceCursor_left_depth_cases
    occurrence frame computed reference cursor selected
  rcases descriptor with ⟨occurrenceRoot, targetShorter⟩
  exact ⟨classification.1.trans occurrenceRoot, by omega⟩

/-! ## Constitutional insulation of the strict Rule-3 branch -/

/-- The complete occurrence comparison is `compareLex` with the Rule-3 spatial key first.  A strict
Rule-3 component comparison is decisive and the Rule-4/5 key is never consulted. -/
theorem compareLocalizedOccurrenceRule3Through5Keys_of_rule3_ne_eq
    (input : CertifiedLocalizedCIPInput)
    (first second : input.LocalizedOccurrenceRule3Through5Key)
    (strict : input.compareLocalizedRerootRecursiveRule3SpatialKeys
      first.rule3 second.rule3 ≠ Ordering.eq) :
    input.compareLocalizedOccurrenceRule3Through5Keys first second =
      input.compareLocalizedRerootRecursiveRule3SpatialKeys first.rule3 second.rule3 := by
  unfold compareLocalizedOccurrenceRule3Through5Keys
  exact localizedCompareLex_eq_left_of_ne (by simpa only [Ordering.byKey] using strict)

/-- **Insulation core.**  Endpoint frames that agree on both atoms and both Rule-3 spatial keys
have the same endpoint priority whenever the Rule-3 comparison is strict, regardless of their
two Rule-4/5 compound keys.  In particular, any difference produced by non-deeper compound-label
reads is invisible in the strict Rule-3 branch. -/
theorem localizedRule3EndpointPriority_eq_of_rule3_keys
    (input : CertifiedLocalizedCIPInput)
    (first second : input.Atom)
    (firstRule3 secondRule3 : input.LocalizedRerootRecursiveRule3SpatialKey)
    (firstRule45 firstRule45' secondRule45 secondRule45' :
      input.LocalizedRerootCompoundRule45Key)
    (strict : input.compareLocalizedRerootRecursiveRule3SpatialKeys
      firstRule3 secondRule3 ≠ Ordering.eq) :
    input.localizedRule3EndpointPriority
        { first := first, second := second,
          firstKey := { rule3 := firstRule3, rule45 := firstRule45 },
          secondKey := { rule3 := secondRule3, rule45 := secondRule45 } } =
      input.localizedRule3EndpointPriority
        { first := first, second := second,
          firstKey := { rule3 := firstRule3, rule45 := firstRule45' },
          secondKey := { rule3 := secondRule3, rule45 := secondRule45' } } := by
  have decisive : ∀ (left right : input.LocalizedRerootCompoundRule45Key),
      input.compareLocalizedOccurrenceRule3Through5Keys
          { rule3 := firstRule3, rule45 := left }
          { rule3 := secondRule3, rule45 := right } =
        input.compareLocalizedRerootRecursiveRule3SpatialKeys firstRule3 secondRule3 := by
    intro left right
    exact input.compareLocalizedOccurrenceRule3Through5Keys_of_rule3_ne_eq
      _ _ strict
  unfold localizedRule3EndpointPriority
  rw [decisive firstRule45 secondRule45, decisive firstRule45' secondRule45']

/-- Frame-level form of the insulation: equal atoms and equal Rule-3 keys force equal endpoint
priority in the strict Rule-3 branch, for arbitrary Rule-4/5 keys. -/
theorem localizedRule3EndpointPriority_eq_of_rule3_eq
    (input : CertifiedLocalizedCIPInput)
    (f g : input.LocalizedRule3EndpointKeyFrame)
    (firstEq : f.first = g.first)
    (secondEq : f.second = g.second)
    (firstRule3Eq : f.firstKey.rule3 = g.firstKey.rule3)
    (secondRule3Eq : f.secondKey.rule3 = g.secondKey.rule3)
    (strict : input.compareLocalizedRerootRecursiveRule3SpatialKeys
      f.firstKey.rule3 f.secondKey.rule3 ≠ Ordering.eq) :
    input.localizedRule3EndpointPriority f =
      input.localizedRule3EndpointPriority g := by
  cases f with
  | mk fFirst fSecond fFirstKey fSecondKey =>
    cases g with
    | mk gFirst gSecond gFirstKey gSecondKey =>
      dsimp only at firstEq secondEq
      cases fFirstKey with
      | mk fRule3 fRule45 =>
        cases gFirstKey with
        | mk gRule3 gRule45 =>
          cases fSecondKey with
          | mk fSecondRule3 fSecondRule45 =>
            cases gSecondKey with
            | mk gSecondRule3 gSecondRule45 =>
              dsimp only at firstRule3Eq secondRule3Eq strict ⊢
              rw [← firstEq, ← secondEq, ← firstRule3Eq, ← secondRule3Eq]
              exact input.localizedRule3EndpointPriority_eq_of_rule3_keys
                fFirst fSecond fRule3 fSecondRule3
                fRule45 gRule45 fSecondRule45 gSecondRule45 strict

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualCarrierParentFrame_facts
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualCarrierParent_mem_neighborFrames
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_child
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_right_strict
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_right_reachable_dependency
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_right_reachable_label_eq_state
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_right_compound_eq_restricted
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_right_compound_eq_restrictedExec
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_left_depth_cases
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_left_ancestor_not_strict
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.Rule3ActualOutwardFrom
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.Rule3ActualOutwardProperty
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualOutwardFrom_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_left_sibling_support
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_left_sibling_reader_support
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_left_sibling_label_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_left_sibling_reader_difference
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualDepthDependency_trans
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_right_strict_of_descriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_right_reachable_label_eq_state_of_descriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_right_compound_eq_restricted_of_descriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_right_compound_eq_restrictedExec_of_descriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_left_sibling_strict_of_descriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_left_sibling_subtree_strict_of_descriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_left_sibling_reachable_label_eq_state_of_descriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_left_nonstrict_descriptor_is_ancestor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualReferenceCursor_left_ancestor_strict_of_descriptor_of_gap
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedOccurrenceRule3Through5Keys_of_rule3_ne_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3EndpointPriority_eq_of_rule3_keys
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3EndpointPriority_eq_of_rule3_eq
