import TetraStereo.OneCenter.LocalizedRule3ShortCircuitOddNode
import TetraStereo.OneCenter.LocalizedRule3CumulatedChainExecutable
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-!
# Recognition completeness for the ordinary and odd Rule-3 route detectors

The production classifiers `localizedRule3OrdinaryRouteCertificate?` and
`localizedRule3OddRouteCertificate?` decide route membership by runtime topology inspection.
This module proves the exact converses of the existing certificate-soundness directions:

* `localizedRule3OddRoute_iff_certificate?_isSome`: the odd detector succeeds iff the independent
  `LocalizedRule3OddRoute` holds.
* `localizedRule3OrdinaryRoute_iff_certificate?_isSome`: the ordinary detector succeeds iff the
  independent `LocalizedRule3OrdinaryRoute` holds.

The central construction is `…?_eq_some_of_declarative`: from an independent declarative route
(physical endpoint frame, declarative parent-side topology and declarative axis walk) we *compute*
the executable endpoint frame and the executable walk at
`localizedRule3CumulatedTraversalFuel carrierFuel`.  The only supplementary input is the proved
zipper-diameter bound on cursor budgets; no executable success is assumed and no canonical
self-answer is fed back in.

The repaired `DeclarativeLocalizedRule3AxisTopology.branched` constructor carries the
nondegeneracy `first ≠ second`, supplied in the core from the duplicate-freedom of the executable
continuation filter.  Consequently the literal `.branched` entry disjunct of
`LocalizedRule3OrdinaryRoute` is already nondegenerate, and the unmodified route is exactly the
recognized language.  Reflection below only recovers the *topology category* (terminal / linear /
branched); it never claims that an arbitrary declarative `rest` list equals the executable filter,
so membership-only freedom inside `rest` is immaterial to the route category.
-/

/-! ## The carrier parent is unique -/

/-- The certified shorter-address parent list of a carrier frame is a singleton whenever it is
nonempty.  Root plus address is a functional coordinate of the deduplicated occurrence carrier. -/
theorem localizedCarrierParentFrames_eq_singleton_of_mem
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {source parent : input.LocalizedCIPOccurrenceFrame}
    (present : parent ∈ input.localizedCarrierParentFrames (fuel := fuel) source) :
    input.localizedCarrierParentFrames (fuel := fuel) source = [parent] := by
  have parentInFrames := present
  rw [localizedCarrierParentFrames, List.mem_filter] at present
  obtain ⟨parentPresent, parentConditions⟩ := present
  simp only [Bool.and_eq_true, beq_iff_eq] at parentConditions
  have parentDerived := (input.mem_localizedOccurrences_iff fuel parent).mp parentPresent
  have onlyParent : ∀ candidate,
      candidate ∈ input.localizedCarrierParentFrames (fuel := fuel) source →
        candidate = parent := by
    intro candidate candidatePresent
    rw [localizedCarrierParentFrames, List.mem_filter] at candidatePresent
    obtain ⟨candidatePresent, candidateConditions⟩ := candidatePresent
    simp only [Bool.and_eq_true, beq_iff_eq] at candidateConditions
    have candidateDerived :=
      (input.mem_localizedOccurrences_iff fuel candidate).mp candidatePresent
    exact input.declarativeLocalizedOccurrence_functional_at_root_address
      candidateDerived parentDerived
      (candidateConditions.1.1.trans parentConditions.1.1.symm)
      (candidateConditions.2.trans parentConditions.2.symm)
  have parentNodup :
      (input.localizedCarrierParentFrames (fuel := fuel) source).Nodup := by
    unfold localizedCarrierParentFrames
    exact (input.localizedOccurrences_nodup fuel).filter _
  have sameMembers : ∀ candidate,
      candidate ∈ input.localizedCarrierParentFrames (fuel := fuel) source ↔
        candidate ∈ [parent] := by
    intro candidate
    constructor
    · intro candidatePresent
      simp [onlyParent candidate candidatePresent]
    · intro candidatePresent
      simp only [List.mem_singleton] at candidatePresent
      subst candidate
      exact parentInFrames
  have permutation :
      List.Perm (input.localizedCarrierParentFrames (fuel := fuel) source) [parent] :=
    (List.perm_ext_iff_of_nodup parentNodup (by simp)).mpr sameMembers
  exact List.perm_singleton.mp permutation

/-- The executable singleton carrier-parent selection succeeds at any certified parent frame. -/
theorem localizedRule3CarrierParentFrame?_eq_some_of_mem
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (parent : input.LocalizedCIPOccurrenceFrame)
    (present : parent ∈ input.localizedCarrierParentFrames (fuel := fuel) occurrence.1) :
    input.localizedRule3CarrierParentFrame? occurrence = some parent := by
  have singleton := localizedCarrierParentFrames_eq_singleton_of_mem input present
  simp [localizedRule3CarrierParentFrame?, singleton]

/-- Executable parent-occurrence recovery succeeds at the declarative carrier parent. -/
theorem localizedRule3CarrierParentOccurrence?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence parent : input.LocalizedCIPOccurrence fuel)
    (decl : input.DeclarativeLocalizedRule3CarrierParentOccurrence occurrence parent) :
    input.localizedRule3CarrierParentOccurrence? occurrence = some parent := by
  classical
  have frameComputed : input.localizedRule3CarrierParentFrame? occurrence = some parent.1 :=
    localizedRule3CarrierParentFrame?_eq_some_of_mem input occurrence parent.1 decl
  unfold localizedRule3CarrierParentOccurrence?
  rw [frameComputed]
  dsimp only
  rw [dif_pos parent.2]

/-- Executable twin of parent-occurrence recovery at the declarative carrier parent. -/
theorem localizedRule3CarrierParentOccurrenceExec?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence parent : input.LocalizedCIPOccurrence fuel)
    (decl : input.DeclarativeLocalizedRule3CarrierParentOccurrence occurrence parent) :
    input.localizedRule3CarrierParentOccurrenceExec? occurrence = some parent := by
  rw [localizedRule3CarrierParentOccurrenceExec?_eq_original input occurrence]
  exact localizedRule3CarrierParentOccurrence?_eq_some_of_declarative input occurrence parent decl

/-! ## The physical endpoint frame is computed from its declarative meaning -/

/-- Every declarative physical endpoint frame is returned by the executable physical endpoint
recovery.  This is the constructive converse of
`localizedRule3PhysicalEndpointCursorFrame?_sound`. -/
theorem localizedRule3PhysicalEndpointCursorFrame?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame fuel)
    (decl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame occurrence frame) :
    input.localizedRule3PhysicalEndpointCursorFrame? occurrence = some frame := by
  rcases decl with ⟨real, currentEq, parentEq, bondEq, carrierDecl, leftCurrent,
    leftPrevious, rightOccurrence, rightPrevious⟩
  unfold localizedRule3PhysicalEndpointCursorFrame?
  rw [if_pos real]
  simp only [currentEq, parentEq]
  try dsimp only
  rw [if_pos bondEq]
  rw [localizedRule3CarrierParentOccurrence?_eq_some_of_declarative
    input occurrence frame.leftCursor.occurrence carrierDecl]
  simp only [bind, Option.bind_some]
  rw [if_pos leftCurrent]
  simp only [Option.some.injEq]
  rw [← leftPrevious, ← rightOccurrence, ← rightPrevious]

/-- Executable twin of physical endpoint completeness. -/
theorem localizedRule3PhysicalEndpointCursorFrameExec?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame fuel)
    (decl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame occurrence frame) :
    input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some frame := by
  rw [localizedRule3PhysicalEndpointCursorFrameExec?_eq_original input occurrence]
  exact localizedRule3PhysicalEndpointCursorFrame?_eq_some_of_declarative
    input occurrence frame decl

/-! ## Reflecting declarative physical topology into the executable classifier -/

/-- The executable continuation computation over one certified children list is exactly the
physical filter of that list. -/
theorem localizedRule3AxisPhysicalContinuationCursors?_eq_some_filter
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren? cursor = some children) :
    input.localizedRule3AxisPhysicalContinuationCursors? cursor =
      some (input.localizedRule3AxisPhysicalContinuationCursors cursor children) := by
  simp [localizedRule3AxisPhysicalContinuationCursors?, computed]

/-- A declarative terminal continuation list forces the executable physical filter to be empty. -/
theorem localizedRule3AxisPhysicalContinuationCursors_eq_nil_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {children : List (input.LocalizedRerootCursor carrierFuel)}
    (childrenComputed : input.localizedRerootChildren? cursor = some children)
    (derived : input.DeclarativeLocalizedRule3AxisPhysicalContinuationCursors cursor []) :
    input.localizedRule3AxisPhysicalContinuationCursors cursor children = [] := by
  rcases derived with ⟨declared, declaredComputed, _exactChildren, membership⟩
  have declaredEq : declared = children :=
    Option.some.inj (declaredComputed.symm.trans childrenComputed)
  subst declared
  unfold localizedRule3AxisPhysicalContinuationCursors
  apply List.filter_eq_nil_iff.mpr
  intro child childPresent
  by_cases physical : input.LocalizedRule3AxisPhysicalContinuation cursor child
  · exfalso
    have member : child ∈ ([] : List (input.LocalizedRerootCursor carrierFuel)) :=
      (membership child).mpr ⟨childPresent, physical⟩
    exact List.not_mem_nil member
  · simp [physical]

/-- A declarative linear continuation list forces the executable physical filter to be exactly
that singleton. -/
theorem localizedRule3AxisPhysicalContinuationCursors_eq_singleton_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor next : input.LocalizedRerootCursor carrierFuel}
    {children : List (input.LocalizedRerootCursor carrierFuel)}
    (childrenComputed : input.localizedRerootChildren? cursor = some children)
    (derived :
      input.DeclarativeLocalizedRule3AxisPhysicalContinuationCursors cursor [next]) :
    input.localizedRule3AxisPhysicalContinuationCursors cursor children = [next] := by
  rcases derived with ⟨declared, declaredComputed, exactChildren, membership⟩
  have same : declared = children :=
    Option.some.inj (declaredComputed.symm.trans childrenComputed)
  subst declared
  have nextInFilter :
      next ∈ input.localizedRule3AxisPhysicalContinuationCursors cursor children := by
    rw [input.mem_localizedRule3AxisPhysicalContinuationCursors_iff]
    exact (membership next).mp (by simp)
  have onlyNext : ∀ candidate,
      candidate ∈ input.localizedRule3AxisPhysicalContinuationCursors cursor children →
        candidate = next := by
    intro candidate candidatePresent
    have characterized :=
      (input.mem_localizedRule3AxisPhysicalContinuationCursors_iff
        cursor candidate children).mp candidatePresent
    have inContinuations : candidate ∈ [next] := (membership candidate).mpr characterized
    simpa using inContinuations
  have childrenNodup : children.Nodup :=
    input.localizedRerootChildren_nodup cursor children exactChildren
  have filterNodup :
      (input.localizedRule3AxisPhysicalContinuationCursors cursor children).Nodup := by
    unfold localizedRule3AxisPhysicalContinuationCursors
    exact childrenNodup.filter _
  have sameMembers : ∀ candidate,
      candidate ∈ input.localizedRule3AxisPhysicalContinuationCursors cursor children ↔
        candidate ∈ [next] := by
    intro candidate
    constructor
    · intro candidatePresent
      simp [onlyNext candidate candidatePresent]
    · intro candidatePresent
      simp only [List.mem_singleton] at candidatePresent
      subst candidate
      exact nextInFilter
  have permutation :
      List.Perm (input.localizedRule3AxisPhysicalContinuationCursors cursor children) [next] :=
    (List.perm_ext_iff_of_nodup filterNodup (by simp)).mpr sameMembers
  exact List.perm_singleton.mp permutation

/-- A declarative branch list containing two distinct continuations forces the executable
physical filter to have at least two entries.  Distinctness is exactly the nondegeneracy that
the repaired branch topology requires and that the duplicate-free executable enumeration
detects. -/
theorem exists_cons_cons_of_declarative_branched_distinct
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor first second : input.LocalizedRerootCursor carrierFuel}
    {rest : List (input.LocalizedRerootCursor carrierFuel)}
    {children : List (input.LocalizedRerootCursor carrierFuel)}
    (membership : ∀ child, child ∈ (first :: second :: rest) ↔
      child ∈ children ∧ input.LocalizedRule3AxisPhysicalContinuation cursor child)
    (distinct : first ≠ second) :
    ∃ a b tail,
      input.localizedRule3AxisPhysicalContinuationCursors cursor children =
        a :: b :: tail := by
  have firstMember :
      first ∈ input.localizedRule3AxisPhysicalContinuationCursors cursor children := by
    rw [input.mem_localizedRule3AxisPhysicalContinuationCursors_iff]
    exact (membership first).mp (by simp)
  have secondMember :
      second ∈ input.localizedRule3AxisPhysicalContinuationCursors cursor children := by
    rw [input.mem_localizedRule3AxisPhysicalContinuationCursors_iff]
    exact (membership second).mp (by simp)
  cases filterComputed :
      input.localizedRule3AxisPhysicalContinuationCursors cursor children with
  | nil => simp [filterComputed] at firstMember
  | cons head tail =>
      cases tailComputed : tail with
      | nil =>
          have firstEq : first = head := by
            simpa [filterComputed, tailComputed] using firstMember
          have secondEq : second = head := by
            simpa [filterComputed, tailComputed] using secondMember
          exact absurd (firstEq.trans secondEq.symm) distinct
      | cons next more =>
          exact ⟨head, next, more, rfl⟩

/-- A declarative terminal topology is recognized as the executable terminal topology. -/
theorem localizedRule3AxisTopology?_eq_terminal_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (derived : input.DeclarativeLocalizedRule3AxisTopology cursor .terminal) :
    input.localizedRule3AxisTopology? cursor = some .terminal := by
  cases derived with
  | terminal frame =>
      rcases frame with ⟨children, childrenComputed, exactChildren, membership⟩
      have filterNil :
          input.localizedRule3AxisPhysicalContinuationCursors cursor children = [] :=
        input.localizedRule3AxisPhysicalContinuationCursors_eq_nil_of_declarative
          childrenComputed ⟨children, childrenComputed, exactChildren, membership⟩
      have continuationsComputed :=
        input.localizedRule3AxisPhysicalContinuationCursors?_eq_some_filter
          cursor children childrenComputed
      simp [localizedRule3AxisTopology?, continuationsComputed, filterNil]

/-- A declarative linear topology is recognized as the executable linear topology. -/
theorem localizedRule3AxisTopology?_eq_linear_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor next : input.LocalizedRerootCursor carrierFuel}
    (derived : input.DeclarativeLocalizedRule3AxisTopology cursor (.linear next)) :
    input.localizedRule3AxisTopology? cursor = some (.linear next) := by
  cases derived with
  | linear frame real =>
      rcases frame with ⟨children, childrenComputed, exactChildren, membership⟩
      have filterSingleton :
          input.localizedRule3AxisPhysicalContinuationCursors cursor children = [next] :=
        input.localizedRule3AxisPhysicalContinuationCursors_eq_singleton_of_declarative
          childrenComputed ⟨children, childrenComputed, exactChildren, membership⟩
      have continuationsComputed :=
        input.localizedRule3AxisPhysicalContinuationCursors?_eq_some_filter
          cursor children childrenComputed
      simp [localizedRule3AxisTopology?, continuationsComputed, filterSingleton, real]

/-- A declarative branch topology is recognized as some executable branch topology.  Only the
topology category is reflected; the declarative `rest` list is not compared with the filter. -/
theorem localizedRule3AxisTopology?_branched_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor first second : input.LocalizedRerootCursor carrierFuel}
    {rest : List (input.LocalizedRerootCursor carrierFuel)}
    (derived :
      input.DeclarativeLocalizedRule3AxisTopology cursor (.branched first second rest)) :
    ∃ a b tail, input.localizedRule3AxisTopology? cursor =
      some (.branched a b tail) := by
  cases derived with
  | branched frame distinct =>
      rcases frame with ⟨children, childrenComputed, exactChildren, membership⟩
      obtain ⟨a, b, tail, filterCons⟩ :=
        exists_cons_cons_of_declarative_branched_distinct input membership distinct
      have continuationsComputed :=
        input.localizedRule3AxisPhysicalContinuationCursors?_eq_some_filter
          cursor children childrenComputed
      exact ⟨a, b, tail, by
        simp [localizedRule3AxisTopology?, continuationsComputed, filterCons]⟩

/-! ## Reflecting declarative entries -/

/-- A declarative terminal-start entry is computed as the executable terminal-start entry. -/
theorem localizedRule3CumulatedAxisEntry?_eq_terminalStart_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {occurrence : input.LocalizedCIPOccurrence carrierFuel}
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    (derived :
      input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence (.terminalStart initial)) :
    input.localizedRule3CumulatedAxisEntry? occurrence = some (.terminalStart initial) := by
  cases derived with
  | terminalStart physical terminal =>
      have physicalComputed :=
        input.localizedRule3PhysicalEndpointCursorFrame?_eq_some_of_declarative
          occurrence initial physical
      have topologyComputed :=
        input.localizedRule3AxisTopology?_eq_terminal_of_declarative terminal
      simp [localizedRule3CumulatedAxisEntry?, physicalComputed, topologyComputed]

/-- Executable twin of terminal-start entry reflection. -/
theorem localizedRule3CumulatedAxisEntryExec?_eq_terminalStart_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {occurrence : input.LocalizedCIPOccurrence carrierFuel}
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    (derived :
      input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence (.terminalStart initial)) :
    input.localizedRule3CumulatedAxisEntryExec? occurrence = some (.terminalStart initial) := by
  rw [localizedRule3CumulatedAxisEntryExec?_eq_original input occurrence]
  exact input.localizedRule3CumulatedAxisEntry?_eq_terminalStart_of_declarative derived

/-! ## Complete walks within the zipper budget -/

/-- Every declarative axis walk has a nonempty path. -/
theorem declarativeWalk_length_pos
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {path : List (input.LocalizedRerootCursor carrierFuel)}
    (derived : input.DeclarativeLocalizedRule3CumulatedAxisWalk cursor path) :
    0 < path.length := by
  cases derived <;> simp

/-- A declarative walk with valid start has at most `budget` physical steps.  This is the exact
zipper-diameter bound needed to run the executable walk without truncation. -/
theorem declarativeWalk_steps_le_budget
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (path : List (input.LocalizedRerootCursor carrierFuel))
    (derived : input.DeclarativeLocalizedRule3CumulatedAxisWalk cursor path)
    (valid : input.LocalizedRerootCursorValid cursor) :
    path.length - 1 ≤ input.localizedRerootCursorBudget cursor := by
  revert valid
  induction derived with
  | terminal topology =>
      intro _valid
      simp
  | step topology rest ih =>
      rename_i start next tail
      intro valid
      cases topology with
      | linear frame real =>
          rcases frame with ⟨children, _childrenComputed, childrenDerived, membership⟩
          have nextChild : next ∈ children := ((membership next).mp (by simp)).1
          have childValid :=
            input.localizedRerootChild_valid start next children childrenDerived nextChild
          have decreases :=
            input.localizedRerootChild_budget_lt start next children valid
              childrenDerived nextChild
          have stepBound := ih childValid
          have pos := input.declarativeWalk_length_pos rest
          simp only [List.length_cons]
          omega

/-- Every declarative walk shorter than the traversal fuel is returned by the executable walk. -/
theorem walkLocalizedRule3CumulatedAxis?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (path : List (input.LocalizedRerootCursor carrierFuel))
    (derived : input.DeclarativeLocalizedRule3CumulatedAxisWalk cursor path)
    (bound : path.length ≤ traversalFuel + 1) :
    input.walkLocalizedRule3CumulatedAxis? traversalFuel cursor = some path := by
  revert traversalFuel bound
  induction derived with
  | terminal topology =>
      intro traversalFuel _bound
      cases traversalFuel <;>
        simp [walkLocalizedRule3CumulatedAxis?,
          input.localizedRule3AxisTopology?_eq_terminal_of_declarative topology]
  | step topology rest ih =>
      rename_i start next tail
      intro traversalFuel bound
      cases traversalFuel with
      | zero =>
          exfalso
          have pos := input.declarativeWalk_length_pos rest
          simp only [List.length_cons, Nat.zero_add] at bound
          omega
      | succ fuel =>
          have tailBound : tail.length ≤ fuel + 1 := by
            simp only [List.length_cons] at bound
            omega
          have tailComputed := ih fuel tailBound
          simp [walkLocalizedRule3CumulatedAxis?,
            input.localizedRule3AxisTopology?_eq_linear_of_declarative topology,
            tailComputed]

/-! ## Complete endpoint frames -/

/-- Every declarative terminal-to-terminal endpoint frame is returned by the executable endpoint
recovery, provided the traversal fuel covers the walk. -/
theorem localizedRule3CumulatedEndpointCursorFrame?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
    (walkBound : frame.rightward.length ≤ traversalFuel + 1)
    (derived :
      input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence frame) :
    input.localizedRule3CumulatedEndpointCursorFrame? traversalFuel occurrence = some frame := by
  rcases derived with ⟨entryDecl, walkDecl, reverseIdentity, rightPartnerEq, rightEq⟩
  rcases frame with ⟨initial, rightward, rightPartnerCursor, rightCursor, rightPartner, right⟩
  cases entryDecl with
  | terminalStart physical terminal =>
      have entryComputed :
          input.localizedRule3CumulatedAxisEntry? occurrence =
            some (.terminalStart initial) :=
        input.localizedRule3CumulatedAxisEntry?_eq_terminalStart_of_declarative
          (DeclarativeLocalizedRule3CumulatedAxisEntry.terminalStart physical terminal)
      have walkComputed :=
        input.walkLocalizedRule3CumulatedAxis?_eq_some_of_declarative
          traversalFuel initial.rightCursor rightward walkDecl walkBound
      obtain ⟨rest, restEq⟩ := reverseIdentity
      unfold localizedRule3CumulatedEndpointCursorFrame?
      rw [entryComputed]
      simp only [bind, Option.bind_some]
      rw [walkComputed]
      simp only [Option.bind_some]
      rw [restEq]
      try dsimp only
      rw [rightPartnerEq]
      simp only [Option.bind_some]
      rw [rightEq]
      try dsimp only
      try simp only [Option.bind_some]

/-- Executable twin of endpoint-frame completeness. -/
theorem localizedRule3CumulatedEndpointCursorFrameExec?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
    (walkBound : frame.rightward.length ≤ traversalFuel + 1)
    (derived :
      input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence frame) :
    input.localizedRule3CumulatedEndpointCursorFrameExec? traversalFuel occurrence = some frame := by
  rw [localizedRule3CumulatedEndpointCursorFrameExec?_eq_original input traversalFuel occurrence]
  exact input.localizedRule3CumulatedEndpointCursorFrame?_eq_some_of_declarative
    traversalFuel occurrence frame walkBound derived

/-- The declared directional cursor of a complete endpoint frame is path-valid: the physical
endpoint frame certifies the carrier-parent half of the cut neighborhood. -/
theorem declarativeEndpointFrame_rightCursor_valid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
    (derived :
      input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence frame) :
    input.LocalizedRerootCursorValid frame.initial.rightCursor := by
  rcases derived with ⟨entryDecl, _walkDecl, _reverseIdentity, _rightPartnerEq, _rightEq⟩
  cases entryDecl with
  | terminalStart physical _terminal =>
      rcases physical with ⟨_real, _current, _parent, _bond, parentDecl, _leftCurrent,
        _leftPrevious, rightOccurrence, rightPrevious⟩
      have parentInNeighbors : frame.initial.leftCursor.occurrence.1 ∈
          input.localizedRerootNeighborFrames (fuel := carrierFuel) occurrence.1 := by
        rw [localizedRerootNeighborFrames, List.mem_append]
        exact Or.inl parentDecl
      unfold LocalizedRerootCursorValid
      rw [rightPrevious, rightOccurrence]
      exact input.mem_localizedRerootNeighborFrames_symm occurrence
        frame.initial.leftCursor.occurrence.1 parentInNeighbors



theorem endpointWalk_length_le_traversalFuel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
    (derived :
      input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence frame) :
    frame.rightward.length ≤ input.localizedRule3CumulatedTraversalFuel carrierFuel + 1 := by
  have rightValid := input.declarativeEndpointFrame_rightCursor_valid occurrence frame derived
  rcases derived with ⟨_entryDecl, walkDecl, _reverseIdentity, _rightPartnerEq, _rightEq⟩
  have steps := declarativeWalk_steps_le_budget input frame.initial.rightCursor
    frame.rightward walkDecl rightValid
  have pos := input.declarativeWalk_length_pos walkDecl
  have budgetBound := input.localizedRerootCursorBudget_le_twice frame.initial.rightCursor
  simp only [localizedRule3CumulatedTraversalFuel, localizedOccurrenceRerootEvaluationFuel]
  omega

/-- Every declarative endpoint frame is returned by the original endpoint recovery at the
production traversal fuel. -/
theorem localizedRule3CumulatedEndpointCursorFrame?_eq_some_at_traversalFuel_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
    (derived :
      input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence frame) :
    input.localizedRule3CumulatedEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some frame :=
  input.localizedRule3CumulatedEndpointCursorFrame?_eq_some_of_declarative
    (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence frame
    (input.endpointWalk_length_le_traversalFuel occurrence frame derived) derived

/-- Executable endpoint completeness at the production traversal fuel. -/
theorem localizedRule3CumulatedEndpointCursorFrameExec?_eq_some_at_traversalFuel_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
    (derived :
      input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence frame) :
    input.localizedRule3CumulatedEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some frame :=
  input.localizedRule3CumulatedEndpointCursorFrameExec?_eq_some_of_declarative
    (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence frame
    (input.endpointWalk_length_le_traversalFuel occurrence frame derived) derived

/-! ## Recognition of the odd route -/

/-- A successful run of the odd detector entails the independent odd route; the certificate
carries the route constructed by the detector from its own runtime evidence. -/
theorem localizedRule3OddRoute_of_certificate?_isSome
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (detected : (input.localizedRule3OddRouteCertificate? occurrence).isSome) :
    input.LocalizedRule3OddRoute occurrence := by
  obtain ⟨certificate, _certificateEq⟩ := Option.isSome_iff_exists.mp detected
  exact certificate.valid

/-- The independent odd route is recognized by the executable odd detector at the production
traversal fuel. -/
theorem localizedRule3OddRouteCertificate?_isSome_of_route
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (route : input.LocalizedRule3OddRoute occurrence) :
    (input.localizedRule3OddRouteCertificate? occurrence).isSome := by
  rcases route with ⟨edge, axis, frameDecl, countNe, odd⟩
  have entryExec : input.localizedRule3CumulatedAxisEntryExec? occurrence =
      some (.terminalStart axis.initial) :=
    input.localizedRule3CumulatedAxisEntryExec?_eq_terminalStart_of_declarative frameDecl.1
  have endpointExec :=
    input.localizedRule3CumulatedEndpointCursorFrameExec?_eq_some_at_traversalFuel_of_declarative
      occurrence axis frameDecl
  unfold localizedRule3OddRouteCertificate?
  rw [dif_pos edge]
  split
  next _initialBranch =>
    split
    next endpointMissing =>
      simp [endpointMissing] at endpointExec
    next actualAxis endpointSome =>
      have sameAxis : actualAxis = axis :=
        Option.some.inj (endpointSome.symm.trans endpointExec)
      subst actualAxis
      split
      next ordinaryBranch => exact absurd ordinaryBranch countNe
      next notOrdinaryBranch => simp
  next failedTerminal =>
    exact absurd entryExec (failedTerminal axis.initial)

/-- Exact odd-route recognition: the executable odd detector succeeds iff the independent odd
route holds. -/
theorem localizedRule3OddRoute_iff_certificate?_isSome
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    (input.localizedRule3OddRouteCertificate? occurrence).isSome ↔
      input.LocalizedRule3OddRoute occurrence :=
  ⟨input.localizedRule3OddRoute_of_certificate?_isSome occurrence,
    input.localizedRule3OddRouteCertificate?_isSome_of_route occurrence⟩

/-! ## Recognition of the ordinary route -/

/-- A successful ordinary detector run entails the independent ordinary route. -/
theorem localizedRule3OrdinaryRoute_of_certificate?_isSome
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (detected : (input.localizedRule3OrdinaryRouteCertificate? occurrence).isSome) :
    input.LocalizedRule3OrdinaryRoute occurrence := by
  obtain ⟨certificate, _certificateEq⟩ := Option.isSome_iff_exists.mp detected
  exact certificate.valid

/-- The independent ordinary route is recognized by the executable ordinary detector at the
production traversal fuel. -/
theorem localizedRule3OrdinaryRouteCertificate?_isSome_of_route
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (route : input.LocalizedRule3OrdinaryRoute occurrence) :
    (input.localizedRule3OrdinaryRouteCertificate? occurrence).isSome := by
  rcases route with ⟨edge, branched | terminal⟩
  · rcases branched with ⟨initial, first, second, rest, entry⟩
    cases entry with
    | branched physical branchTopology =>
        obtain ⟨a, b, tail, topologyComputed⟩ :=
          input.localizedRule3AxisTopology?_branched_of_declarative branchTopology
        have physicalComputed :=
          input.localizedRule3PhysicalEndpointCursorFrame?_eq_some_of_declarative
            occurrence initial physical
        have entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
            some (.branched initial a b tail) := by
          simp [localizedRule3CumulatedAxisEntry?, physicalComputed, topologyComputed]
        have entryExec : input.localizedRule3CumulatedAxisEntryExec? occurrence =
            some (.branched initial a b tail) := by
          rw [localizedRule3CumulatedAxisEntryExec?_eq_original input occurrence]
          exact entryComputed
        unfold localizedRule3OrdinaryRouteCertificate?
        rw [dif_pos edge]
        split
        next initial' first' second' rest' entryEq => simp
        next initial' entryEq =>
          rw [entryEq] at entryExec
          simp at entryExec
        next notBranched notTerminal =>
          exact absurd entryExec (notBranched initial a b tail)
  · rcases terminal with ⟨axis, frameDecl, countEq⟩
    have entryExec : input.localizedRule3CumulatedAxisEntryExec? occurrence =
        some (.terminalStart axis.initial) :=
      input.localizedRule3CumulatedAxisEntryExec?_eq_terminalStart_of_declarative frameDecl.1
    have endpointExec :=
      input.localizedRule3CumulatedEndpointCursorFrameExec?_eq_some_at_traversalFuel_of_declarative
        occurrence axis frameDecl
    unfold localizedRule3OrdinaryRouteCertificate?
    rw [dif_pos edge]
    split
    next initial' first' second' rest' entryEq =>
      rw [entryEq] at entryExec
      simp at entryExec
    next initial' entryEq =>
      split
      next endpointMissing =>
        simp [endpointMissing] at endpointExec
      next actualAxis endpointSome =>
        have sameAxis : actualAxis = axis :=
          Option.some.inj (endpointSome.symm.trans endpointExec)
        subst actualAxis
        split
        next ordinaryEq => simp
        next notOrdinary => exact absurd countEq notOrdinary
    next notBranched notTerminal =>
      exact absurd entryExec (notTerminal axis.initial)

/-- Exact ordinary-route recognition: the executable ordinary detector succeeds iff the
independent (nondegenerate) ordinary route holds. -/
theorem localizedRule3OrdinaryRoute_iff_certificate?_isSome
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    (input.localizedRule3OrdinaryRouteCertificate? occurrence).isSome ↔
      input.LocalizedRule3OrdinaryRoute occurrence :=
  ⟨input.localizedRule3OrdinaryRoute_of_certificate?_isSome occurrence,
    input.localizedRule3OrdinaryRouteCertificate?_isSome_of_route occurrence⟩

/-! ## Converse mutual exclusion -/

/-- The converse of `ordinaryRoute_none_of_oddRoute`: once the ordinary detector has selected a
certificate, the odd detector refuses.  The two detectors inspect the same executable entry and
endpoint computations, and the ordinary one-bond count contradicts the odd `≠ 1` guard. -/
theorem localizedRule3OddRouteCertificate?_eq_none_of_ordinaryRoute
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (certificate : input.LocalizedRule3OrdinaryRouteCertificate occurrence)
    (routed : input.localizedRule3OrdinaryRouteCertificate? occurrence = some certificate) :
    input.localizedRule3OddRouteCertificate? occurrence = none := by
  cases hOdd : input.localizedRule3OddRouteCertificate? occurrence with
  | none => rfl
  | some oddCertificate =>
      have hNone := input.ordinaryRoute_none_of_oddRoute occurrence oddCertificate hOdd
      rw [routed] at hNone
      contradiction

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
