import TetraStereo.OneCenter.LocalizedRule3OriginalTargetDemand
import TetraStereo.OneCenter.LocalizedRule3RouteCompleteness
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-!
# Outward locality of the actual extended short-circuit odd Rule-3 requests

The extended short-circuit Rule 3 evaluator splits on the runtime odd-route certificate.  On the
odd branch `rule3ShortOddCallbackRequests` emits two endpoint request groups only:

* the left endpoint of the recovered physical double-bond frame, i.e. the carrier parent `P` of the
  physical occurrence `O`, with incoming cut `O`;
* the terminal right end of the complete odd-axis walk started at the right endpoint cursor of the
  same physical frame.

This module proves that every cursor of every actual odd request is an outward cursor of any
strictly deeper original descriptor target `T` of `O`.  The two groups are handled differently.

* The left group is exactly the ordinary left-endpoint gate below the carrier parent `P` of `O`.
  Its parent-side (upward, ancestor) request is suppressed by the complete constitutional
  comparison; the existing `rule3ShortEndpointCallbackRequests_left_outward` already carries that
  argument, and it applies here because `P` is the real active-simple carrier parent of `O`.

* The right group is emitted below the terminal end `rightCursor` of the declarative axis walk
  `DeclarativeLocalizedRule3CumulatedAxisWalk frame.initial.rightCursor frame.rightward`.  The
  initial right cursor is `O` itself, cut at `P`, hence outward of `T` because `T` is strictly
  shallower.  Every `.linear` step of the walk is an actual executable edge
  `E cursor next` (the declarative continuation list is the executable children list), so
  `outward_edge_preserves` makes every path cursor outward.  The last two walk cursors form the
  final edge; its head `rightCursor` additionally records the previous walk cursor as incoming
  cut, which is the carrier-parent coordinate, so the ordinary right-endpoint gate applies at
  `rightCursor`.

The odd double-bond count (`1 < frame.doubleBondCount`) is not needed for support: the reverse
witness `frame.rightward.reverse = rightCursor :: rightPartnerCursor :: rest` already exhibits the
final edge.  No upward axis traversal occurs, no route certificate is assumed, and the eager
`rule3OddCallbackRequests` are deliberately *not* claimed: on the rooted path `T-P=O=C=D` the eager
route can request `T` at its initial left endpoint.
-/

/-! ## Walk geometry -/

/-- Every declarative axis walk starts at its first path cursor. -/
theorem declarativeWalk_path_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {start : input.LocalizedRerootCursor carrierFuel}
    {path : List (input.LocalizedRerootCursor carrierFuel)}
    (walk : input.DeclarativeLocalizedRule3CumulatedAxisWalk start path) :
    path.head? = some start := by
  cases walk with
  | terminal _ => rfl
  | step _ _ => rfl

/-- A linear declarative axis step is an actual executable reroot-child edge.  The declarative
frame of the step names the fail-closed children of `localizedRerootChildren?`, which is the
executable children list; membership in the singleton continuation list therefore is membership
in `executableLocalizedRerootChildren`. -/
theorem declarativeLinearStep_edge
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor next : input.LocalizedRerootCursor carrierFuel}
    (derived : input.DeclarativeLocalizedRule3AxisTopology cursor (.linear next)) :
    E input cursor next := by
  cases derived with
  | linear frame _real =>
      rcases frame with ⟨children, childrenComputed, _exactChildren, membership⟩
      have nextChild : next ∈ children := ((membership next).mp (by simp)).1
      have childrenEq : children = input.executableLocalizedRerootChildren cursor := by
        have someEq : some children = some (input.executableLocalizedRerootChildren cursor) :=
          childrenComputed.symm.trans (input.localizedRerootChildren?_eq_some_executable cursor)
        exact Option.some.inj someEq
      show next ∈ input.executableLocalizedRerootChildren cursor
      rw [← childrenEq]
      exact nextChild

/-- **A walk that starts outward stays outward.**  If the first cursor of a declarative cumulated
axis walk is an outward cursor of the descriptor target `T`, then every cursor on the walk is an
outward cursor of `T`.  The induction step turns the `.linear` topology of the walk into the
executable edge `E cursor next` and applies `outward_edge_preserves`. -/
theorem declarativeWalk_cursor_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (T : input.LocalizedCIPOccurrence carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (path : List (input.LocalizedRerootCursor carrierFuel))
    (walk : input.DeclarativeLocalizedRule3CumulatedAxisWalk start path)
    (outward : OutwardRerootCursor input T start) :
    ∀ cursor ∈ path, OutwardRerootCursor input T cursor := by
  revert outward
  induction walk with
  | terminal _topology =>
      intro outward point pointMem
      simp only [List.mem_singleton] at pointMem
      rw [pointMem]
      exact outward
  | step topology restWalk ih =>
      rename_i stepStart stepNext stepTail
      intro outward point pointMem
      rw [List.mem_cons] at pointMem
      rcases pointMem with pointEq | inTail
      · rw [pointEq]
        exact outward
      · exact ih (outward_edge_preserves input T stepStart stepNext outward
          (declarativeLinearStep_edge input topology)) point inTail

/-- **The final pair of a walk is an executable edge.**  If the reverse of a walk path begins with
`last`, `prev`, then `prev` is an executable child of the walk cursor that precedes it, and `last`
records `prev` as its incoming cut.  This is the last-step extraction used for the odd right
endpoint, where the walk frame supplies exactly such a reverse witness. -/
theorem declarativeWalk_reverse_last_pair
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (start : input.LocalizedRerootCursor carrierFuel)
    (path : List (input.LocalizedRerootCursor carrierFuel))
    (walk : input.DeclarativeLocalizedRule3CumulatedAxisWalk start path) :
    ∀ (last prev : input.LocalizedRerootCursor carrierFuel)
      (tailRest : List (input.LocalizedRerootCursor carrierFuel)),
      path.reverse = last :: prev :: tailRest →
        E input prev last ∧ last.previous? = some prev.occurrence := by
  induction walk with
  | terminal _topology =>
      intro last prev tailRest reverseEq
      have hlen := congrArg List.length reverseEq
      simp only [List.length_reverse, List.length_cons, List.length_nil] at hlen
      omega
  | step topology restWalk ih =>
      rename_i stepStart stepNext stepTail
      intro last prev tailRest reverseEq
      have stepEq : stepTail.reverse ++ [stepStart] = last :: prev :: tailRest := by
        simpa using reverseEq
      cases stepTail with
      | nil =>
          have pos := input.declarativeWalk_length_pos restWalk
          simp at pos
      | cons head tail' =>
          cases tail' with
          | nil =>
              have headEq : head = stepNext := by
                have headComputed := input.declarativeWalk_path_head restWalk
                simpa using headComputed
              have pairEq : head :: stepStart ::
                  ([] : List (input.LocalizedRerootCursor carrierFuel)) =
                    last :: prev :: tailRest := by
                simpa using stepEq
              rw [headEq] at pairEq
              injection pairEq with hlast hrest
              injection hrest with hprev _hrest
              have edge := declarativeLinearStep_edge input topology
              rw [← hlast, ← hprev]
              exact ⟨edge,
                input.executableLocalizedRerootChildren_previous stepStart stepNext edge⟩
          | cons second more =>
              obtain ⟨a, b, rest0, hdecomp⟩ :
                  ∃ (a b : input.LocalizedRerootCursor carrierFuel)
                    (rest0 : List (input.LocalizedRerootCursor carrierFuel)),
                    (head :: second :: more).reverse = a :: b :: rest0 := by
                cases hrev : (head :: second :: more).reverse with
                | nil =>
                    have hlen := congrArg List.length hrev
                    simp only [List.length_reverse, List.length_cons,
                      List.length_nil] at hlen
                    omega
                | cons a more' =>
                    cases more' with
                    | nil =>
                        have hlen := congrArg List.length hrev
                        simp only [List.length_reverse, List.length_cons,
                          List.length_nil] at hlen
                        omega
                    | cons b rest0 => exact ⟨a, b, rest0, rfl⟩
              have h : a :: b :: (rest0 ++ [stepStart]) =
                  last :: prev :: tailRest := by
                rw [hdecomp] at stepEq
                simpa using stepEq
              injection h with ha hrest
              injection hrest with hb _hrest
              rw [← ha, ← hb]
              exact ih a b rest0 hdecomp

/-! ## The actual extended odd request support -/

/-- **Outward support of the actual extended short-circuit odd Rule-3 requests.**  Let `O` be an
occurrence whose extended odd-cumulene frame is actually detected and `T` a strictly shallower
original descriptor target of the same rooted carrier.  Then every cursor occurring in every
request actually emitted by `rule3ShortOddCallbackRequests O` is an outward cursor of `T`: it is
path valid, strictly deeper than `T` in the same rooted carrier, and records an incoming cut of
strictly smaller address length.

Scope: this is the extended short-circuit odd route only.  No successful descriptor or callback
premise is used, and the eager `rule3OddCallbackRequests` are not claimed. -/
theorem rule3ShortOddActualRequest_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O T : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency O T) :
    ∀ request ∈ input.rule3ShortOddCallbackRequests O,
      ∀ cursor ∈ request, OutwardRerootCursor input T cursor := by
  intro request member cursor cursorMem
  unfold rule3ShortOddCallbackRequests at member
  cases computed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) O with
  | none => simp [computed] at member
  | some topology =>
      simp only [computed] at member
      have originalComputed : input.localizedRule3OddCumuleneEndpointCursorFrame?
          (input.localizedRule3CumulatedTraversalFuel carrierFuel) O = some topology := by
        rw [← input.localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_original
          (input.localizedRule3CumulatedTraversalFuel carrierFuel) O]
        exact computed
      have sound := input.localizedRule3OddCumuleneEndpointCursorFrame?_sound
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) O topology originalComputed
      obtain ⟨physical, _terminalLeft, walkDecl, reverseDecl, _rightPartnerCurrent,
        _rightCurrent, _oneLt, _odd⟩ := sound
      obtain ⟨reverseRest, reverseEq⟩ := reverseDecl
      obtain ⟨_realO, _currentO, parentO, _bondO, parentDecl, _leftCurrent, _leftPrevious,
        rightOccurrence, rightPrevious⟩ := physical
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
      have parentFacts := localizedCarrierParentFrame_facts input O.1
        topology.initial.leftCursor.occurrence.1 parentDecl
      rcases List.mem_append.mp member with leftMember | rightMember
      · /- Left endpoint: the request below the carrier parent `P` of `O`. -/
        have parentIsP : certificateO.parent.1 =
            topology.initial.leftCursor.occurrence.1 := by
          have memP : topology.initial.leftCursor.occurrence.1 ∈
              input.localizedCarrierParentFrames (fuel := carrierFuel) O.1 := parentDecl
          rw [certificateO.carrierParentFrames_eq_singleton input] at memP
          exact (List.mem_singleton.mp memP).symm
        have leftActive : topology.initial.leftCursor.occurrence.1.node.ActiveSimple := by
          rw [← parentIsP]
          exact certificateO.parent_active
        have leftRoot : topology.initial.leftCursor.occurrence.1.root = T.1.root :=
          parentFacts.1.trans deeper.1
        have leftNotShorter : T.1.address.length ≤
            topology.initial.leftCursor.occurrence.1.address.length := by
          have parentLength : topology.initial.leftCursor.occurrence.1.address.length + 1 =
              O.1.address.length := parentFacts.2.1
          have targetDeeper : T.1.address.length < O.1.address.length := deeper.2
          omega
        exact rule3ShortEndpointCallbackRequests_left_outward input T
          topology.initial.leftCursor topology.initial.left topology.initial.right
          leftRoot leftNotShorter leftActive request leftMember cursor cursorMem
      · /- Right endpoint: the terminal end of the odd-axis walk. -/
        have rightCursorMem : topology.rightCursor ∈ topology.rightward := by
          rw [← List.mem_reverse, reverseEq]
          simp
        have partnerMem : topology.rightPartnerCursor ∈ topology.rightward := by
          rw [← List.mem_reverse, reverseEq]
          simp
        have initialOutward : OutwardRerootCursor input T topology.initial.rightCursor := by
          have initialValid : input.LocalizedRerootCursorValid topology.initial.rightCursor := by
            have parentInNeighbors : topology.initial.leftCursor.occurrence.1 ∈
                input.localizedRerootNeighborFrames (fuel := carrierFuel) O.1 := by
              rw [localizedRerootNeighborFrames, List.mem_append]
              exact Or.inl parentDecl
            unfold LocalizedRerootCursorValid
            simp only [rightPrevious, rightOccurrence]
            exact input.mem_localizedRerootNeighborFrames_symm O
              topology.initial.leftCursor.occurrence.1 parentInNeighbors
          have initialDependency : input.LocalizedDepthDependency
              topology.initial.rightCursor.occurrence T := by
            rw [rightOccurrence]
            exact deeper
          have initialShorter :
              topology.initial.leftCursor.occurrence.1.address.length <
                topology.initial.rightCursor.occurrence.1.address.length := by
            rw [rightOccurrence]
            have parentLength : topology.initial.leftCursor.occurrence.1.address.length + 1 =
                O.1.address.length := parentFacts.2.1
            omega
          exact ⟨initialValid, initialDependency, topology.initial.leftCursor.occurrence,
            rightPrevious, initialShorter⟩
        have allOutward := declarativeWalk_cursor_outward input T
          topology.initial.rightCursor topology.rightward walkDecl initialOutward
        have startOutward : OutwardRerootCursor input T topology.rightCursor :=
          allOutward topology.rightCursor rightCursorMem
        have partnerOutward : OutwardRerootCursor input T topology.rightPartnerCursor :=
          allOutward topology.rightPartnerCursor partnerMem
        have lastPair := declarativeWalk_reverse_last_pair input
          topology.initial.rightCursor topology.rightward walkDecl
          topology.rightCursor topology.rightPartnerCursor reverseRest reverseEq
        have edge : E input topology.rightPartnerCursor topology.rightCursor := lastPair.1
        obtain ⟨partnerValid, _partnerDependency, partnerPrevious, partnerPreviousEq,
          partnerShorter⟩ := partnerOutward
        obtain ⟨dropLastStep, lengthStep, stepRoot, stepPrevious, _stepValid⟩ :=
          outward_edge input topology.rightPartnerCursor topology.rightCursor
            partnerValid partnerPrevious partnerPreviousEq partnerShorter edge
        have previousParent : topology.rightPartnerCursor.occurrence.1 ∈
            input.localizedCarrierParentFrames (fuel := carrierFuel)
              topology.rightCursor.occurrence.1 := by
          rw [localizedCarrierParentFrames, List.mem_filter]
          refine ⟨topology.rightPartnerCursor.occurrence.2, ?_⟩
          simp only [Bool.and_eq_true, beq_iff_eq]
          exact ⟨⟨stepRoot.symm, by omega⟩, dropLastStep.symm⟩
        exact rule3ShortEndpointCallbackRequests_right_outward input T
          topology.rightCursor topology.rightPartnerCursor.occurrence
          topology.right topology.rightPartner stepPrevious previousParent
          startOutward.2.1.1 startOutward.2.1.2 request rightMember cursor cursorMem

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeWalk_path_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLinearStep_edge
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeWalk_cursor_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeWalk_reverse_last_pair
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortOddActualRequest_outward
