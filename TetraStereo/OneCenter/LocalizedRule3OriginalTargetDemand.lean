import TetraStereo.OneCenter.LocalizedRule3EndpointCallbackDemand
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.OneCenter.LocalizedConstitutionalRootSeparation
import TetraStereo.OneCenter.LocalizedRerootRootObservation
import TetraStereo.OneCenter.LocalizedParentBranchConstitutionalSeparation
import TetraStereo.OneCenter.LocalizedParentFrameHistory
import TetraStereo.OneCenter.LocalizedPhysicalReferenceUniqueness
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-!
# Local support of the actual ordinary Rule 3 callback requests

The ordinary short-circuit Rule 3 endpoint callback is requested at the two canonical reference
cursors selected below one physical endpoint cursor of a perceived open even axis.  This module
proves that those request cursors are supported outward by any strictly deeper original descriptor
target `T` of the same physical occurrence `O`.

The two sides behave differently.

* The right endpoint cursor is `O` with incoming cut at the carrier parent `P`.  Its reference
  cursors are immediate children of `O`, and every such child is an outward immediate child (a
  carrier-tree neighbour that is not the parent coordinate).  These are outward cursors of `O`,
  and therefore of every strictly shallower descriptor target in the same rooted carrier.

* The left endpoint cursor is `P` with incoming cut at `O`.  Its reference cursors are the
  neighbours of `P`: the sibling children (one slot below `P`, hence outward as well) and the
  single carrier parent `Q` of `P`.  A request that would have to call back at the ancestor `Q`
  together with a sibling `c` is suppressed *before* emission: `Q` and `c` have different
  Rule 1b root distances in the original rooted graph (`Q` is the carrier parent of the real
  active-simple centre `P`), so their complete `OfficialRuleMajorKey` comparison is strict.  The
  emission gate in `rule3ShortEndpointCallbackRequests` therefore takes the strict `gt`/`lt` arm
  and emits nothing.

Both reference cursors cannot be the ancestor: the two explicit substituents are distinct
(`Finset.sort` is duplicate free) while equal coordinates below `P` together with the shared
incoming cut would make the two cursors equal.
-/

/-! ## Carrier-tree geometry -/

/-- A carrier parent frame of a carrier occurrence has the same root, an address shorter by one,
and the drop-last address.  This is the `localizedCarrierParentFrames` filter, read literally. -/
theorem localizedCarrierParentFrame_facts
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrenceFrame)
    (parent : input.LocalizedCIPOccurrenceFrame)
    (present : parent ∈ input.localizedCarrierParentFrames (fuel := fuel) target) :
    parent.root = target.root ∧
      parent.address.length + 1 = target.address.length ∧
      parent.address = target.address.dropLast := by
  rw [localizedCarrierParentFrames, List.mem_filter] at present
  simp only [Bool.and_eq_true, beq_iff_eq] at present
  exact ⟨present.2.1.1, present.2.1.2, present.2.2⟩

/-- A selected executable reference cursor is an executable reroot child of the endpoint cursor,
records the endpoint occurrence as its incoming cut, carries the requested atom, and has real
physical provenance. -/
theorem localizedRule3ReferenceCursorExec?_facts
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor cursor : input.LocalizedRerootCursor fuel)
    (reference : input.Atom)
    (selected : input.localizedRule3ReferenceCursorExec? endpointCursor reference = some cursor) :
    cursor ∈ input.executableLocalizedRerootChildren endpointCursor ∧
      cursor.previous? = some endpointCursor.occurrence ∧
      cursor.occurrence.1.node.current? = some reference ∧
      LocalizedRule3PhysicalReferenceProvenance cursor.occurrence.1.node.provenance := by
  have original : input.localizedRule3ReferenceCursor? endpointCursor reference = some cursor := by
    rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
    exact selected
  rcases input.localizedRule3ReferenceCursor?_sound endpointCursor cursor reference original with
    ⟨children, childrenComputed, _childrenDerived, cursorPresent, cursorCurrent,
      cursorPhysical, cursorPrevious⟩
  have childrenEq : children = input.executableLocalizedRerootChildren endpointCursor := by
    have someEq : some children =
        some (input.executableLocalizedRerootChildren endpointCursor) :=
      childrenComputed.symm.trans (input.localizedRerootChildren?_eq_some_executable endpointCursor)
    exact Option.some.inj someEq
  exact ⟨childrenEq ▸ cursorPresent, cursorPrevious, cursorCurrent, cursorPhysical⟩

/-- Every executable reroot child of a cursor is either the carrier-parent coordinate of the
cursor occurrence or an outward sibling coordinate one slot below it.  Both alternatives are read
off the uncut neighbour list: a neighbour is adjacent in the carrier tree, and only the parent
case shortens the address. -/
theorem executableLocalizedRerootChild_dichotomy
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (start : input.LocalizedRerootCursor fuel)
    (child : input.LocalizedRerootCursor fuel)
    (childPresent : child ∈ input.executableLocalizedRerootChildren start) :
    (child.occurrence.1.address.length + 1 = start.occurrence.1.address.length ∧
        child.occurrence.1.address = start.occurrence.1.address.dropLast) ∨
      (∃ slot, child.occurrence.1.address = start.occurrence.1.address ++ [slot]) := by
  have derived := input.executableLocalizedRerootChildren_declarative start
  have childIntended : child.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames start := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨child, childPresent, rfl⟩
  have neighbor :=
    input.mem_localizedRerootNeighborFrames_of_mem_intended start child.occurrence.1 childIntended
  have adjacent :=
    (input.mem_localizedRerootNeighborFrames_iff start.occurrence.1 child.occurrence.1).mp
      neighbor |>.2
  rcases adjacent.2 with parent | outward
  · exact Or.inl parent
  · exact Or.inr (exists_eq_append_singleton_of_eq_dropLast outward.1 outward.2)

/-- **Strict outward movement.**  An executable reroot child reached by appending one sibling slot
below a cursor at least as deep as the descriptor target `T` is an outward cursor of `T`.  The
incoming cut of the child is the starting occurrence, which is strictly shallower, and the
coordinate strictly deepens. -/
theorem outwardRerootCursor_of_cursor_child
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (start child : input.LocalizedRerootCursor carrierFuel)
    (startRoot : start.occurrence.1.root = target.1.root)
    (startNotShorter : target.1.address.length ≤ start.occurrence.1.address.length)
    (childPresent : child ∈ input.executableLocalizedRerootChildren start)
    (childOutward : ∃ slot,
      child.occurrence.1.address = start.occurrence.1.address ++ [slot]) :
    OutwardRerootCursor input target child := by
  have derived := input.executableLocalizedRerootChildren_declarative start
  have childValid : input.LocalizedRerootCursorValid child :=
    input.localizedRerootChild_valid start child
      (input.executableLocalizedRerootChildren start) derived childPresent
  have childRoot : child.occurrence.1.root = start.occurrence.1.root :=
    input.localizedRerootChildren_root_eq start child
      (input.executableLocalizedRerootChildren start) derived childPresent
  have childPrevious : child.previous? = some start.occurrence :=
    input.executableLocalizedRerootChildren_previous start child childPresent
  obtain ⟨slot, childAddress⟩ := childOutward
  have childLength : child.occurrence.1.address.length =
      start.occurrence.1.address.length + 1 := by
    rw [childAddress, List.length_append]
    simp
  exact ⟨childValid, ⟨childRoot.trans startRoot, by omega⟩,
    start.occurrence, childPrevious, by omega⟩

/-! ## Rule 1b separation of the parent-side neighbour -/

/-- **Rule 1b separates a parent-side reference from a sibling reference.**  Below a cursor at
the carrier occurrence `P`, one child is the carrier-parent coordinate `Q` (the drop-last
address) and the other is an outward sibling one slot below `P`.  In the original rooted graph
`Q` is the carrier parent of the real active-simple centre `P`, so the Rule 1b root distance of
`Q` differs from that of every child of `P`.

The carrier-parent coordinate is pinned by uniqueness at a fixed root and address; the sibling
coordinate is an immediate child of `P` by the occurrence carrier's immediate-child theorem. -/
theorem rule1bRootDistance_ne_of_parentSide
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (P : input.LocalizedCIPOccurrence carrierFuel)
    (PActive : P.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory P)
    (parentCursor outwardCursor : input.LocalizedRerootCursor carrierFuel)
    (parentRoot : parentCursor.occurrence.1.root = P.1.root)
    (parentAddress : parentCursor.occurrence.1.address = P.1.address.dropLast)
    (outwardRoot : outwardCursor.occurrence.1.root = P.1.root)
    (slot : Nat)
    (outwardAddress : outwardCursor.occurrence.1.address = P.1.address ++ [slot]) :
    parentCursor.occurrence.1.node.rule1bRootDistance ≠
      outwardCursor.occurrence.1.node.rule1bRootDistance := by
  have parentDerived : input.DeclarativeLocalizedOccurrence carrierFuel
      parentCursor.occurrence.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel parentCursor.occurrence.1).mp
      parentCursor.occurrence.2
  have certificateDerived : input.DeclarativeLocalizedOccurrence carrierFuel
      certificate.parent.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel certificate.parent.1).mp certificate.parent.2
  have parentEq : parentCursor.occurrence.1 = certificate.parent.1 :=
    input.declarativeLocalizedOccurrence_functional_at_root_address parentDerived certificateDerived
      (parentRoot.trans certificate.parent_root.symm)
      (parentAddress.trans certificate.parent_address.symm)
  have PDerived : input.DeclarativeLocalizedOccurrence carrierFuel P.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel P.1).mp P.2
  have outwardDerived : input.DeclarativeLocalizedOccurrence carrierFuel
      outwardCursor.occurrence.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel outwardCursor.occurrence.1).mp
      outwardCursor.occurrence.2
  obtain ⟨childNode, childAtSlot, childFrame⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child PDerived outwardDerived
      outwardRoot slot outwardAddress
  have childNodeEq : outwardCursor.occurrence.1.node = childNode :=
    congrArg LocalizedCIPOccurrenceFrame.node childFrame
  have childNodeMem : outwardCursor.occurrence.1.node ∈
      input.executableOfficialCIPChildren P.1.node := by
    rw [childNodeEq]
    exact List.fst_mem_of_mem_zipIdx childAtSlot
  obtain ⟨current, parentCurrent, tail, currentEq, _parentCurrentEq, historyEq,
    parentHistoryEq⟩ := certificate.history_shape input
  have separated :=
    LocalizedParentBranchConstitutionalSeparation.parentRule1bDistance_ne_childRule1bDistance
      input P.1.node certificate.parent.1.node current parentCurrent tail
      PActive currentEq historyEq (certificate.parent_provenance input) parentHistoryEq
      outwardCursor.occurrence.1.node childNodeMem
  rw [parentEq]
  exact fun equal => separated equal.symm

/-- **Strict complete comparison for a request that would call the ancestor.**  If one of the two
canonical reference cursors below the left endpoint cursor is the carrier-parent coordinate of
`P` (the ancestor `Q`), then the complete constitutional comparison of the two cursors is a
strict ordering, never equality.  The two cursors are distinct, so the other one cannot be the
same ancestor; it is an outward sibling, and Rule 1b separates the two original-root keys.

This is exactly the premise that makes `rule3ShortEndpointCallbackRequests` take its strict
`gt`/`lt` arm, so no request is emitted. -/
theorem compareLocalizedConstitutionalCursors?_strict_of_parentSide
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (start : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCursor carrierFuel)
    (leftPresent : left ∈ input.executableLocalizedRerootChildren start)
    (rightPresent : right ∈ input.executableLocalizedRerootChildren start)
    (leftNeRight : left ≠ right)
    (parentSide : left.occurrence.1.address.length + 1 = start.occurrence.1.address.length ∨
      right.occurrence.1.address.length + 1 = start.occurrence.1.address.length)
    (startActive : start.occurrence.1.node.ActiveSimple)
    (startNonroot : start.occurrence.1.address ≠ []) :
    ∃ outcome, input.compareLocalizedConstitutionalCursors? left right = some outcome ∧
      outcome ≠ Ordering.eq := by
  let certificate := input.localizedParentFrameHistory start.occurrence startNonroot
  have leftHere : left ∈ input.executableLocalizedRerootChildren start := leftPresent
  have rightHere : right ∈ input.executableLocalizedRerootChildren start := rightPresent
  have derived := input.executableLocalizedRerootChildren_declarative start
  have leftRoot : left.occurrence.1.root = start.occurrence.1.root :=
    input.localizedRerootChildren_root_eq start left _ derived leftHere
  have rightRoot : right.occurrence.1.root = start.occurrence.1.root :=
    input.localizedRerootChildren_root_eq start right _ derived rightHere
  have leftDichotomy := executableLocalizedRerootChild_dichotomy input start left leftPresent
  have rightDichotomy := executableLocalizedRerootChild_dichotomy input start right rightPresent
  have distanceNe : left.occurrence.1.node.rule1bRootDistance ≠
      right.occurrence.1.node.rule1bRootDistance := by
    rcases leftDichotomy with ⟨_leftLength, leftAddress⟩ | ⟨leftSlot, leftAddress⟩
    · rcases rightDichotomy with ⟨_rightLength, rightAddress⟩ | ⟨rightSlot, rightAddress⟩
      · -- Both reference cursors would be the same ancestor coordinate.
        exfalso
        have sameAddress : right.occurrence.1.address = left.occurrence.1.address :=
          rightAddress.trans leftAddress.symm
        have frameEq : right.occurrence.1 = left.occurrence.1 :=
          input.declarativeLocalizedOccurrence_functional_at_root_address
            ((input.mem_localizedOccurrences_iff carrierFuel right.occurrence.1).mp
              right.occurrence.2)
            ((input.mem_localizedOccurrences_iff carrierFuel left.occurrence.1).mp
              left.occurrence.2)
            (rightRoot.trans leftRoot.symm) sameAddress
        have previousEq : right.previous? = left.previous? := by
          rw [input.executableLocalizedRerootChildren_previous start right rightHere,
            input.executableLocalizedRerootChildren_previous start left leftHere]
        exact leftNeRight (LocalizedRerootCursor.ext input (Subtype.ext frameEq)
          previousEq).symm
      · exact rule1bRootDistance_ne_of_parentSide input start.occurrence startActive certificate
          left right leftRoot leftAddress rightRoot rightSlot rightAddress
    · rcases rightDichotomy with ⟨_rightLength, rightAddress⟩ | ⟨rightSlot, rightAddress⟩
      · exact (rule1bRootDistance_ne_of_parentSide input start.occurrence startActive certificate
          right left rightRoot rightAddress leftRoot leftSlot leftAddress).symm
      · -- Both reference cursors would be outward siblings, contradicting the parent-side hit.
        exfalso
        have leftLength : left.occurrence.1.address.length =
            start.occurrence.1.address.length + 1 := by
          rw [leftAddress, List.length_append]
          simp
        have rightLength : right.occurrence.1.address.length =
            start.occurrence.1.address.length + 1 := by
          rw [rightAddress, List.length_append]
          simp
        omega
  have leftValid : input.LocalizedRerootCursorValid left :=
    input.localizedRerootChild_valid start left _ derived leftHere
  have rightValid : input.LocalizedRerootCursorValid right :=
    input.localizedRerootChild_valid start right _ derived rightHere
  obtain ⟨outcome, computed⟩ :=
    input.compareLocalizedConstitutionalCursors?_total left right leftValid rightValid
  obtain ⟨leftKey, rightKey, leftKeyComputed, rightKeyComputed, compareEq⟩ :=
    input.compareLocalizedConstitutionalCursors?_computations left right outcome computed
  have leftHead : leftKey.rule1b.head? =
      some [([], left.occurrence.1.node.rule1bRootDistance)] := by
    rw [input.buildLocalizedRerootRuleMajorKeyExec?_eq_original] at leftKeyComputed
    exact input.buildLocalizedRerootRuleMajorKey?_rule1b_head _ left leftKey leftKeyComputed
  have rightHead : rightKey.rule1b.head? =
      some [([], right.occurrence.1.node.rule1bRootDistance)] := by
    rw [input.buildLocalizedRerootRuleMajorKeyExec?_eq_original] at rightKeyComputed
    exact input.buildLocalizedRerootRuleMajorKey?_rule1b_head _ right rightKey rightKeyComputed
  refine ⟨outcome, computed, ?_⟩
  rw [← compareEq]
  exact OfficialRuleMajorKey.compare_ne_eq_of_rule1b_head_distances leftHead rightHead distanceNe

/-! ## The emission gate, read exactly -/

/-- **Every emitted endpoint request has the two-cursor form of the gate.**  A request is
emitted only for the two explicit substituents, only when both canonical reference cursors
exist, only when the plain constitutional-root comparator ties, and only when the complete
constitutional comparison refuses or ties.  The two selected cursors are exactly the request.

This is the exact refusal behaviour of `rule3ShortEndpointCallbackRequests`, read as a structural
statement about emitted requests. -/
theorem rule3ShortEndpointCallbackRequests_structure
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpoint partner : input.Atom)
    (cursor : input.LocalizedRerootCursor fuel)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests endpoint partner cursor) :
      ∃ (first second : input.Atom)
          (firstCursor secondCursor : input.LocalizedRerootCursor fuel),
        input.localizedRule3ExplicitSubstituents endpoint partner = [first, second] ∧
          input.localizedRule3ReferenceCursorExec? cursor first = some firstCursor ∧
          input.localizedRule3ReferenceCursorExec? cursor second = some secondCursor ∧
          input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor =
            Ordering.eq ∧
          (input.compareLocalizedConstitutionalCursors? firstCursor secondCursor = none ∨
            input.compareLocalizedConstitutionalCursors? firstCursor secondCursor =
              some Ordering.eq) ∧
          request = [firstCursor, secondCursor] := by
  unfold rule3ShortEndpointCallbackRequests at member
  cases hsubs : input.localizedRule3ExplicitSubstituents endpoint partner with
  | nil => simp [hsubs] at member
  | cons first rest =>
    cases rest with
    | nil => simp [hsubs] at member
    | cons second rest' =>
      cases rest' with
      | cons third rest'' => simp [hsubs] at member
      | nil =>
        cases hfirst : input.localizedRule3ReferenceCursorExec? cursor first with
        | none => simp [hsubs, hfirst] at member
        | some firstCursor =>
          cases hsecond : input.localizedRule3ReferenceCursorExec? cursor second with
          | none => simp [hsubs, hfirst, hsecond] at member
          | some secondCursor =>
            cases hroot : input.compareLocalizedRerootCursorConstitutionalRoot
              firstCursor secondCursor with
            | gt => simp [hsubs, hfirst, hsecond, hroot] at member
            | lt => simp [hsubs, hfirst, hsecond, hroot] at member
            | eq =>
              cases hconst : input.compareLocalizedConstitutionalCursors?
                firstCursor secondCursor with
              | none =>
                have requestEq : request = [firstCursor, secondCursor] := by
                  simpa [hsubs, hfirst, hsecond, hroot, hconst] using member
                exact ⟨first, second, firstCursor, secondCursor, rfl, hfirst, hsecond,
                  hroot, Or.inl hconst, requestEq⟩
              | some order =>
                cases order with
                | gt => simp [hsubs, hfirst, hsecond, hroot, hconst] at member
                | lt => simp [hsubs, hfirst, hsecond, hroot, hconst] at member
                | eq =>
                  have requestEq : request = [firstCursor, secondCursor] := by
                    simpa [hsubs, hfirst, hsecond, hroot, hconst] using member
                  exact ⟨first, second, firstCursor, secondCursor, rfl, hfirst, hsecond,
                    hroot, Or.inr hconst, requestEq⟩

/-- **Every emitted spatial request comes from one endpoint orientation.**  If the physical
endpoint recovery fails there is no request at all; otherwise each request is emitted either as
the left-endpoint request or as the right-endpoint request of the recovered frame. -/
theorem rule3ShortSpatialCallbackRequests_structure
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortSpatialCallbackRequests occurrence) :
      ∃ frame : input.LocalizedRule3PhysicalEndpointCursorFrame fuel,
        input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some frame ∧
          (request ∈ input.rule3ShortEndpointCallbackRequests frame.left frame.right
              frame.leftCursor ∨
            request ∈ input.rule3ShortEndpointCallbackRequests frame.right frame.left
              frame.rightCursor) := by
  unfold rule3ShortSpatialCallbackRequests at member
  cases hframe : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
  | none => simp [hframe] at member
  | some frame =>
    simp only [hframe] at member
    rcases List.mem_append.mp member with leftMember | rightMember
    · exact ⟨frame, rfl, Or.inl leftMember⟩
    · exact ⟨frame, rfl, Or.inr rightMember⟩

/-! ## One-sided locality -/

/-- **The parent coordinate is never a reference child when it is the cut.**  Below a cursor
whose incoming cut is the carrier parent of the cursor occurrence, the parent-side alternative
of the dichotomy is excluded: the intended child list removes the cut address, and the cut
address is exactly the parent coordinate. -/
theorem executableLocalizedRerootChild_not_parentSide_of_parent
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (start : input.LocalizedRerootCursor fuel)
    (previous : input.LocalizedCIPOccurrence fuel)
    (previousEq : start.previous? = some previous)
    (prevParent : previous.1 ∈ input.localizedCarrierParentFrames (fuel := fuel)
      start.occurrence.1)
    (child : input.LocalizedRerootCursor fuel)
    (childPresent : child ∈ input.executableLocalizedRerootChildren start) :
    child.occurrence.1.address.length + 1 ≠ start.occurrence.1.address.length := by
  intro parentLength
  rcases executableLocalizedRerootChild_dichotomy input start child childPresent with
    ⟨_short, childAddress⟩ | ⟨_slot, childAddress⟩
  · have previousAddress := (localizedCarrierParentFrame_facts input start.occurrence.1
      previous.1 prevParent).2.2
    have sameAsPrevious : child.occurrence.1.address = previous.1.address :=
      childAddress.trans previousAddress.symm
    have derived := input.executableLocalizedRerootChildren_declarative start
    have childIntended : child.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames start := by
      rw [← derived.1]
      exact List.mem_map.mpr ⟨child, childPresent, rfl⟩
    exact input.address_ne_previous_of_mem_intended start previous previousEq
      child.occurrence.1 childIntended sameAsPrevious
  · have childLonger : child.occurrence.1.address.length =
        start.occurrence.1.address.length + 1 := by
      rw [childAddress, List.length_append]
      simp
    omega

/-- **Left-endpoint requests are outward.**  A request emitted below a cursor at `P` (the left
endpoint, whose incoming cut is the physical occurrence `O`) cannot contain the carrier-parent
coordinate `Q` of `P`: together with the other reference cursor it would be compared strictly by
Rule 1b, and the emission gate would have taken the strict arm.  Every emitted cursor is
therefore an outward sibling of `P`, strictly deeper than `T` in the same rooted carrier. -/
theorem rule3ShortEndpointCallbackRequests_left_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (T : input.LocalizedCIPOccurrence carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (left right : input.Atom)
    (startRoot : start.occurrence.1.root = T.1.root)
    (startNotShorter : T.1.address.length ≤ start.occurrence.1.address.length)
    (startActive : start.occurrence.1.node.ActiveSimple)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests left right start) :
    ∀ cursor ∈ request, OutwardRerootCursor input T cursor := by
  rintro cursor cursorMem
  obtain ⟨first, second, firstCursor, secondCursor, subs, firstSel, secondSel, _rootCmp,
    constCmp, requestEq⟩ :=
    rule3ShortEndpointCallbackRequests_structure input left right start request member
  rw [requestEq] at cursorMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at cursorMem
  obtain ⟨firstChild, _firstPrev, firstCurrent, _firstPhysical⟩ :=
    localizedRule3ReferenceCursorExec?_facts input start firstCursor first firstSel
  obtain ⟨secondChild, _secondPrev, secondCurrent, _secondPhysical⟩ :=
    localizedRule3ReferenceCursorExec?_facts input start secondCursor second secondSel
  have substituentsNodup : (input.localizedRule3ExplicitSubstituents left right).Nodup := by
    unfold localizedRule3ExplicitSubstituents
    exact Finset.sort_nodup _ _
  have atomsNe : first ≠ second := by
    rw [subs] at substituentsNodup
    simpa using substituentsNodup
  have firstNeSecond : firstCursor ≠ secondCursor := by
    intro same
    apply atomsNe
    have currentEq : some first = some second := by
      rw [← firstCurrent, same, secondCurrent]
    exact Option.some.inj currentEq
  have startNonrootOfParentSide : ∀ x : input.LocalizedRerootCursor carrierFuel,
      x.occurrence.1.address.length + 1 = start.occurrence.1.address.length →
      start.occurrence.1.address ≠ [] := by
    intro _ shorter empty
    have zero : start.occurrence.1.address.length = 0 := by simpa using empty
    omega
  rcases cursorMem with hc | hc
  all_goals subst cursor
  · rcases executableLocalizedRerootChild_dichotomy input start firstCursor firstChild with
      ⟨firstLength, _⟩ | ⟨slot, firstAddress⟩
    · exfalso
      obtain ⟨outcome, computed, strict⟩ :=
        compareLocalizedConstitutionalCursors?_strict_of_parentSide input start firstCursor
          secondCursor firstChild secondChild firstNeSecond (Or.inl firstLength) startActive
          (startNonrootOfParentSide firstCursor firstLength)
      rcases constCmp with refused | tied
      · rw [refused] at computed
        exact absurd computed (by simp)
      · rw [tied] at computed
        exact strict (Option.some.inj computed).symm
    · exact outwardRerootCursor_of_cursor_child input T start firstCursor startRoot
        startNotShorter firstChild ⟨slot, firstAddress⟩
  · rcases executableLocalizedRerootChild_dichotomy input start secondCursor secondChild with
      ⟨secondLength, _⟩ | ⟨slot, secondAddress⟩
    · exfalso
      obtain ⟨outcome, computed, strict⟩ :=
        compareLocalizedConstitutionalCursors?_strict_of_parentSide input start firstCursor
          secondCursor firstChild secondChild firstNeSecond (Or.inr secondLength) startActive
          (startNonrootOfParentSide secondCursor secondLength)
      rcases constCmp with refused | tied
      · rw [refused] at computed
        exact absurd computed (by simp)
      · rw [tied] at computed
        exact strict (Option.some.inj computed).symm
    · exact outwardRerootCursor_of_cursor_child input T start secondCursor startRoot
        startNotShorter secondChild ⟨slot, secondAddress⟩

/-- **Right-endpoint requests are outward.**  Below a cursor at the physical occurrence `O` whose
incoming cut is the carrier parent `P`, every reference cursor is an immediate child of `O` and
cannot be the parent coordinate, which is the cut.  All of them are outward children of `O`, and
`O` is strictly deeper than `T`. -/
theorem rule3ShortEndpointCallbackRequests_right_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (T : input.LocalizedCIPOccurrence carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (left right : input.Atom)
    (previousEq : start.previous? = some previous)
    (previousParent : previous.1 ∈ input.localizedCarrierParentFrames (fuel := carrierFuel)
      start.occurrence.1)
    (startRoot : start.occurrence.1.root = T.1.root)
    (startDeeper : T.1.address.length < start.occurrence.1.address.length)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests left right start) :
    ∀ cursor ∈ request, OutwardRerootCursor input T cursor := by
  rintro cursor cursorMem
  obtain ⟨first, second, firstCursor, secondCursor, _subs, firstSel, secondSel, _rootCmp,
    _constCmp, requestEq⟩ :=
    rule3ShortEndpointCallbackRequests_structure input left right start request member
  rw [requestEq] at cursorMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at cursorMem
  obtain ⟨firstChild, _firstPrev, _firstCurrent, _firstPhysical⟩ :=
    localizedRule3ReferenceCursorExec?_facts input start firstCursor first firstSel
  obtain ⟨secondChild, _secondPrev, _secondCurrent, _secondPhysical⟩ :=
    localizedRule3ReferenceCursorExec?_facts input start secondCursor second secondSel
  rcases cursorMem with hc | hc
  all_goals subst cursor
  · have notParent := executableLocalizedRerootChild_not_parentSide_of_parent input start
      previous previousEq previousParent firstCursor firstChild
    rcases executableLocalizedRerootChild_dichotomy input start firstCursor firstChild with
      ⟨firstLength, _⟩ | ⟨slot, firstAddress⟩
    · exact absurd firstLength notParent
    · exact outwardRerootCursor_of_cursor_child input T start firstCursor startRoot
        (le_of_lt startDeeper) firstChild ⟨slot, firstAddress⟩
  · have notParent := executableLocalizedRerootChild_not_parentSide_of_parent input start
      previous previousEq previousParent secondCursor secondChild
    rcases executableLocalizedRerootChild_dichotomy input start secondCursor secondChild with
      ⟨secondLength, _⟩ | ⟨slot, secondAddress⟩
    · exact absurd secondLength notParent
    · exact outwardRerootCursor_of_cursor_child input T start secondCursor startRoot
        (le_of_lt startDeeper) secondChild ⟨slot, secondAddress⟩

/-! ## Headline -/

/-- **Ordinary Rule 3 request locality at the original descriptor target.**  Let `O` be a
physical occurrence of a perceived open even axis and `T` an original descriptor target strictly
shallower in the same rooted carrier.  Then every cursor occurring in every request actually
emitted by `rule3ShortSpatialCallbackRequests O` is an outward cursor of `T`: it is path valid,
strictly deeper than `T` in the same rooted carrier, and records an incoming cut of strictly
smaller address length.

No successful descriptor or callback premise is used.  The original descriptor target `T` and
the physical occurrence `O` are kept distinct throughout; the result is stated for the actual
request list of `LocalizedRule3EndpointCallbackDemand`. -/
theorem rule3ActualRequest_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O T : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency O T) :
    ∀ request ∈ input.rule3ShortSpatialCallbackRequests O,
      ∀ cursor ∈ request, OutwardRerootCursor input T cursor := by
  intro request member cursor cursorMem
  rcases rule3ShortSpatialCallbackRequests_structure input O request member with
    ⟨frame, computed, memberLeft | memberRight⟩
  · have sound := input.localizedRule3PhysicalEndpointCursorFrameExec?_sound O frame computed
    rcases sound with ⟨_realO, _currentO, parentO, _bond, parentPresent, _leftCurrent,
      _leftPrevious, _rightOccurrence, _rightPrevious⟩
    have parentFacts := localizedCarrierParentFrame_facts input O.1
      frame.leftCursor.occurrence.1 parentPresent
    have O_nonroot : O.1.address ≠ [] := by
      intro empty
      have derivedO := (input.mem_localizedOccurrences_iff carrierFuel O.1).mp O.2
      have rootFrame :=
        input.declarativeLocalizedOccurrence_eq_root_of_address_nil derivedO empty
      have nodeEq : O.1.node = OfficialCIPNode.root O.1.root :=
        congrArg LocalizedCIPOccurrenceFrame.node rootFrame
      rw [nodeEq] at parentO
      simp [OfficialCIPNode.root, OfficialCIPNode.parent?] at parentO
    have certificateO : input.LocalizedParentFrameHistory O :=
      input.localizedParentFrameHistory O O_nonroot
    have parentIsP : certificateO.parent.1 = frame.leftCursor.occurrence.1 := by
      have memP : frame.leftCursor.occurrence.1 ∈
          input.localizedCarrierParentFrames (fuel := carrierFuel) O.1 := parentPresent
      rw [certificateO.carrierParentFrames_eq_singleton input] at memP
      exact (List.mem_singleton.mp memP).symm
    have leftActive : frame.leftCursor.occurrence.1.node.ActiveSimple := by
      rw [← parentIsP]
      exact certificateO.parent_active
    have leftRoot : frame.leftCursor.occurrence.1.root = T.1.root :=
      parentFacts.1.trans deeper.1
    have parentLength : frame.leftCursor.occurrence.1.address.length + 1 =
        O.1.address.length := parentFacts.2.1
    have targetDeeper : T.1.address.length < O.1.address.length := deeper.2
    have leftNotShorter : T.1.address.length ≤
        frame.leftCursor.occurrence.1.address.length := by
      omega
    exact rule3ShortEndpointCallbackRequests_left_outward input T frame.leftCursor
      frame.left frame.right leftRoot leftNotShorter leftActive request memberLeft cursor cursorMem
  · have sound := input.localizedRule3PhysicalEndpointCursorFrameExec?_sound O frame computed
    rcases sound with ⟨_realO, _currentO, _parentO, _bond, parentPresent, _leftCurrent,
      _leftPrevious, rightOccurrence, rightPrevious⟩
    have parentPresentRight : frame.leftCursor.occurrence.1 ∈
        input.localizedCarrierParentFrames (fuel := carrierFuel)
          frame.rightCursor.occurrence.1 := by
      rw [rightOccurrence]
      exact parentPresent
    have rightRoot : frame.rightCursor.occurrence.1.root = T.1.root := by
      rw [rightOccurrence]
      exact deeper.1
    have rightDeeper : T.1.address.length < frame.rightCursor.occurrence.1.address.length := by
      rw [rightOccurrence]
      exact deeper.2
    exact rule3ShortEndpointCallbackRequests_right_outward input T frame.rightCursor
      frame.leftCursor.occurrence frame.right frame.left rightPrevious parentPresentRight
      rightRoot rightDeeper request memberRight cursor cursorMem

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCarrierParentFrame_facts
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ReferenceCursorExec?_facts
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableLocalizedRerootChild_dichotomy
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outwardRerootCursor_of_cursor_child
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule1bRootDistance_ne_of_parentSide
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedConstitutionalCursors?_strict_of_parentSide
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_structure
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortSpatialCallbackRequests_structure
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableLocalizedRerootChild_not_parentSide_of_parent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_left_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_right_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualRequest_outward
