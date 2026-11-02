import TetraStereo.OneCenter.LocalizedExtendedDemandGraph
import TetraStereo.OneCenter.LocalizedExtendedDemandDiscovery
import TetraStereo.OneCenter.LocalizedPreflightDemandTotality
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitOddNode
import TetraStereo.OneCenter.LocalizedRule3OriginalTargetDemand
import TetraStereo.OneCenter.LocalizedNonrootLeftRequestElimination
import TetraStereo.OneCenter.LocalizedOddRightRequestDepth
import TetraStereo.OneCenter.LocalizedActualFrameChildClassification
import TetraStereo.OneCenter.MultiCenterDetection
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput







































/-! ## The same-root cursor domain -/

/-- Domain of the recognized original-root demand graph: a path-valid cursor whose carrier root
is the distinguished center atom. -/
def TetrahedralRootCursorDomain (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (r : input.Atom) (cursor : input.LocalizedRerootCursor fuel) : Prop :=
  input.LocalizedRerootCursorValid cursor ∧ cursor.occurrence.1.root = r

/-! ## Budget orientation facts -/




theorem tetrahedralRoot_budget_ge_remaining
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    cursor.occurrence.1.remaining ≤ input.localizedRerootCursorBudget cursor := by
  have graded := input.localizedCIPOccurrence_depthGrade cursor.occurrence
  unfold localizedRerootCursorBudget
  split
  · omega
  · split <;> omega

/-- An outward reference cursor records a strictly shallower incoming coordinate, so its budget
is exactly its remaining depth. -/
theorem tetrahedralRoot_budget_eq_remaining_of_outward
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (O : input.LocalizedCIPOccurrence fuel)
    (cursor : input.LocalizedRerootCursor fuel)
    (outward : OutwardRerootCursor input O cursor) :
    input.localizedRerootCursorBudget cursor = cursor.occurrence.1.remaining := by
  obtain ⟨_valid, _dependency, previous, previousEq, shorter⟩ := outward
  unfold localizedRerootCursorBudget
  rw [previousEq]
  simp [shorter]

/-- A callback reference that is outward of the source occurrence strictly decreases the
structural budget of the source cursor. -/
theorem tetrahedralRoot_budget_lt_of_outward_reference
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (O : input.LocalizedCIPOccurrence fuel)
    (parent child : input.LocalizedRerootCursor fuel)
    (parentOccurrence : parent.occurrence.1 = O.1)
    (outward : OutwardRerootCursor input O child) :
    input.localizedRerootCursorBudget child <
      input.localizedRerootCursorBudget parent := by
  have childBudget := tetrahedralRoot_budget_eq_remaining_of_outward input O child outward
  have parentBound := tetrahedralRoot_budget_ge_remaining input parent
  have parentGrade := input.localizedCIPOccurrence_depthGrade parent.occurrence
  have childGrade := input.localizedCIPOccurrence_depthGrade child.occurrence
  have parentAddress : parent.occurrence.1.address.length = O.1.address.length := by
    rw [parentOccurrence]
  have childDeeper : O.1.address.length < child.occurrence.1.address.length :=
    outward.2.1.2
  rw [childBudget]
  omega

/-- Every executable structural child strictly decreases the structural budget. -/
theorem tetrahedralRoot_budget_lt_of_executableChild
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (parent child : input.LocalizedRerootCursor fuel)
    (parentValid : input.LocalizedRerootCursorValid parent)
    (present : child ∈ input.executableLocalizedRerootChildren parent) :
    input.localizedRerootCursorBudget child <
      input.localizedRerootCursorBudget parent := by
  have derived := input.executableLocalizedRerootChildren_declarative parent
  exact input.localizedRerootChild_budget_lt parent child
    (input.executableLocalizedRerootChildren parent) parentValid derived present

/-! ## Right endpoint requests relative to their actual source occurrence -/

/-- **Right-group references are outward children of the endpoint occurrence.**  At a cursor
whose occurrence is `O` and whose incoming cut is the carrier parent of that occurrence, every
reference cursor of an emitted endpoint request is an executable child of `O` that is not the cut
coordinate, hence is an outward cursor of `O` itself.  The reference sits one slot below `O`, so
the target `O` is already the incoming cut of the reference cursor. -/
theorem tetrahedralRoot_endpointRequests_right_outward_of_parent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (left right : input.Atom)
    (startOccurrence : start.occurrence = O)
    (previousEq : start.previous? = some previous)
    (previousParent : previous.1 ∈
      input.localizedCarrierParentFrames (fuel := carrierFuel) start.occurrence.1)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests left right start) :
    ∀ cursor ∈ request, OutwardRerootCursor input O cursor := by
  rintro cursor cursorMem
  obtain ⟨first, second, firstCursor, secondCursor, _subs, firstSel, secondSel, _rootCmp,
    _constCmp, requestEq⟩ :=
    rule3ShortEndpointCallbackRequests_structure input left right start request member
  rw [requestEq] at cursorMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at cursorMem
  obtain ⟨firstChild, _firstPrevious, _firstCurrent, _firstPhysical⟩ :=
    localizedRule3ReferenceCursorExec?_facts input start firstCursor first firstSel
  obtain ⟨secondChild, _secondPrevious, _secondCurrent, _secondPhysical⟩ :=
    localizedRule3ReferenceCursorExec?_facts input start secondCursor second secondSel
  have startRoot : start.occurrence.1.root = O.1.root := by
    rw [startOccurrence]
  have startNotShorter : O.1.address.length ≤ start.occurrence.1.address.length := by
    rw [startOccurrence]
  rcases cursorMem with hc | hc
  all_goals subst cursor
  · have notParent := executableLocalizedRerootChild_not_parentSide_of_parent input start
      previous previousEq previousParent firstCursor firstChild
    rcases executableLocalizedRerootChild_dichotomy input start firstCursor firstChild with
      ⟨firstLength, _⟩ | ⟨slot, firstAddress⟩
    · exact absurd firstLength notParent
    · exact outwardRerootCursor_of_cursor_child input O start firstCursor startRoot
        startNotShorter firstChild ⟨slot, firstAddress⟩
  · have notParent := executableLocalizedRerootChild_not_parentSide_of_parent input start
      previous previousEq previousParent secondCursor secondChild
    rcases executableLocalizedRerootChild_dichotomy input start secondCursor secondChild with
      ⟨secondLength, _⟩ | ⟨slot, secondAddress⟩
    · exact absurd secondLength notParent
    · exact outwardRerootCursor_of_cursor_child input O start secondCursor startRoot
        startNotShorter secondChild ⟨slot, secondAddress⟩

/-! ## Left endpoint request elimination -/

/-- If the carrier parent of an actual physical endpoint frame is itself at the root address,
then the left endpoint atom is exactly the root atom. -/
theorem tetrahedralRoot_left_eq_root_of_rootAddress
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (r : input.Atom)
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial)
    (rootEq : O.1.root = r)
    (rootAddress : initial.leftCursor.occurrence.1.address = []) :
    initial.left = r := by
  rcases frameDecl with
    ⟨_realO, _currentO, _parentO, _bond, parentMem, leftCurrent, _leftPrevious,
      _rightOccurrence, _rightPrevious⟩
  have derived : input.DeclarativeLocalizedOccurrence carrierFuel
      initial.leftCursor.occurrence.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel
      initial.leftCursor.occurrence.1).mp initial.leftCursor.occurrence.2
  have rootFrame := input.declarativeLocalizedOccurrence_eq_root_of_address_nil
    derived rootAddress
  have currentEq : initial.leftCursor.occurrence.1.node.current? =
      some initial.leftCursor.occurrence.1.root := by
    rw [congrArg LocalizedCIPOccurrenceFrame.node rootFrame]
    rfl
  have leftEqRoot : initial.left = initial.leftCursor.occurrence.1.root :=
    Option.some.inj (leftCurrent.symm.trans currentEq)
  have parentRoot : initial.leftCursor.occurrence.1.root = O.1.root :=
    (input.localizedCarrierParentFrame_facts O.1 initial.leftCursor.occurrence.1
      parentMem).1
  exact leftEqRoot.trans (parentRoot.trans rootEq)

/-- **Left endpoint requests vanish at a same-root occurrence of a non-three root.**  A nonroot
carrier parent is refused by the nonroot elimination, and a root carrier parent is refused by the
physical neighbour-count shape gate, where the neighbour count is transported to the recognized
center atom. -/
theorem tetrahedralRoot_leftRequests_eq_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (r : input.Atom)
    (rootCard : (input.moleculeGraph.neighborFinset r).card ≠ 3)
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (rootEq : O.1.root = r)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial) :
    input.rule3ShortEndpointCallbackRequests initial.left initial.right initial.leftCursor = [] := by
  by_cases rootAddress : initial.leftCursor.occurrence.1.address = []
  · apply input.rule3ShortEndpointCallbackRequests_eq_nil_of_neighbor_card_ne_three
      O initial frameDecl
    have leftEq : initial.left = r :=
      tetrahedralRoot_left_eq_root_of_rootAddress input r O initial frameDecl rootEq
        rootAddress
    rw [leftEq]
    exact rootCard
  · exact input.rule3ShortEndpointCallbackRequests_eq_nil_of_nonroot
      O initial frameDecl rootAddress

/-! ## Outward support of the actual short request lists -/

/-- **Actual ordinary spatial requests support the source occurrence.**  Once the left group is
eliminated, each emitted spatial request cursor is an outward cursor of the source occurrence
`O`, so it is a strict depth dependency of `O` with a strictly shorter incoming coordinate. -/
theorem tetrahedralRoot_spatialRequests_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedRerootCursor carrierFuel)
    (leftNil : ∀ (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel),
      input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O.occurrence initial →
        input.rule3ShortEndpointCallbackRequests initial.left initial.right
          initial.leftCursor = []) :
    ∀ request ∈ input.rule3ShortSpatialCallbackRequests O.occurrence,
      ∀ cursor ∈ request, OutwardRerootCursor input O.occurrence cursor := by
  intro request member cursor cursorMem
  rcases rule3ShortSpatialCallbackRequests_structure input O.occurrence request member with
    ⟨frame, computed, leftMember | rightMember⟩
  · have frameDecl :=
      input.localizedRule3PhysicalEndpointCursorFrameExec?_sound O.occurrence frame computed
    have empty := leftNil frame frameDecl
    rw [empty] at leftMember
    simp at leftMember
  · have frameDecl :=
      input.localizedRule3PhysicalEndpointCursorFrameExec?_sound O.occurrence frame computed
    rcases frameDecl with
      ⟨_realO, _currentO, _parentO, _bond, parentMem, _leftCurrent, _leftPrevious,
        rightOccurrence, rightPrevious⟩
    have previousParent : frame.leftCursor.occurrence.1 ∈
        input.localizedCarrierParentFrames (fuel := carrierFuel)
          frame.rightCursor.occurrence.1 := by
      rw [rightOccurrence]
      exact parentMem
    exact tetrahedralRoot_endpointRequests_right_outward_of_parent input O.occurrence
      frame.rightCursor frame.leftCursor.occurrence frame.right frame.left
      rightOccurrence rightPrevious previousParent request rightMember cursor cursorMem





theorem tetrahedralRoot_oddRequests_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedRerootCursor carrierFuel)
    (leftNil : ∀ (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel),
      input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O.occurrence initial →
        input.rule3ShortEndpointCallbackRequests initial.left initial.right
          initial.leftCursor = []) :
    ∀ request ∈ input.rule3ShortOddCallbackRequests O.occurrence,
      ∀ cursor ∈ request, OutwardRerootCursor input O.occurrence cursor := by
  intro request member cursor cursorMem
  unfold rule3ShortOddCallbackRequests at member
  cases computed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) O.occurrence with
  | none => simp [computed] at member
  | some topology =>
      simp only [computed] at member
      have originalComputed : input.localizedRule3OddCumuleneEndpointCursorFrame?
          (input.localizedRule3CumulatedTraversalFuel carrierFuel) O.occurrence =
            some topology := by
        rw [← input.localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_original
          (input.localizedRule3CumulatedTraversalFuel carrierFuel) O.occurrence]
        exact computed
      have sound := input.localizedRule3OddCumuleneEndpointCursorFrame?_sound
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) O.occurrence topology
        originalComputed
      rcases List.mem_append.mp member with leftMember | rightMember
      · have empty := leftNil topology.initial sound.1
        rw [empty] at leftMember
        simp at leftMember
      · exact input.oddRightRequest_outward O topology sound request rightMember cursor
          cursorMem

/-- **Every actual extended request supports its source occurrence.**  The extended evaluator has
exactly three branches: no certificate at all (no request), the short odd list, and the short
spatial list.  The joint-fallback branch is empty by
`rule3ExtendedNodeCallbackRequests_eq_nil_of_jointRouteCertificateNone`. -/
theorem tetrahedralRoot_extendedRequests_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedRerootCursor carrierFuel)
    (leftNil : ∀ (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel),
      input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O.occurrence initial →
        input.rule3ShortEndpointCallbackRequests initial.left initial.right
          initial.leftCursor = []) :
    ∀ request ∈ input.rule3ExtendedNodeCallbackRequests O.occurrence,
      ∀ cursor ∈ request, OutwardRerootCursor input O.occurrence cursor := by
  intro request member cursor cursorMem
  unfold rule3ExtendedNodeCallbackRequests at member
  cases odd : input.localizedRule3OddRouteCertificate? O.occurrence with
  | some _ =>
      simp only [odd] at member
      exact tetrahedralRoot_oddRequests_outward input O leftNil request member cursor
        cursorMem
  | none =>
      simp only [odd] at member
      unfold rule3NodeCallbackRequests at member
      cases ordinary : input.localizedRule3OrdinaryRouteCertificate? O.occurrence with
      | none =>
          rw [ordinary] at member
          rw [input.rule3OriginalNodeCallbackRequests_eq_nil_of_jointRouteCertificateNone
            O.occurrence ordinary odd] at member
          simp at member
      | some _ =>
          simp only [ordinary] at member
          exact tetrahedralRoot_spatialRequests_outward input O leftNil request member
            cursor cursorMem

/-- **Every actual preflight request supports its source occurrence.**  The pruned request list
is a pointwise sublist of the extended one. -/
theorem tetrahedralRoot_preflightRequests_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedRerootCursor carrierFuel)
    (leftNil : ∀ (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel),
      input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O.occurrence initial →
        input.rule3ShortEndpointCallbackRequests initial.left initial.right
          initial.leftCursor = []) :
    ∀ request ∈ input.rule3PreflightExtendedNodeCallbackRequests O.occurrence,
      ∀ cursor ∈ request, OutwardRerootCursor input O.occurrence cursor := by
  intro request member cursor cursorMem
  exact tetrahedralRoot_extendedRequests_outward input O leftNil request
    (input.rule3PreflightExtendedNodeCallbackRequests_subset O.occurrence request member)
    cursor cursorMem

/-! ## Acyclicity through the structural budget -/

/-- **The actual extended demand graph is acyclic on the same-root domain of a non-three root.**
Every reachable cursor stays at root `r`; every actual successor is either a structural child or
an outward callback reference of its source occurrence, and each strictly decreases
`localizedRerootCursorBudget`. -/
theorem tetrahedralRoot_extendedAcyclic_of_rootCard
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (r : input.Atom)
    (rootCard : (input.moleculeGraph.neighborFinset r).card ≠ 3)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ root ∈ roots, TetrahedralRootCursorDomain input r root) :
    input.ExtendedRule3DemandAcyclic roots := by
  refine acyclic_reachable_of_decreasing input.ExtendedRule3DemandEdge roots
    (TetrahedralRootCursorDomain input r) input.localizedRerootCursorBudget rootDomain ?_
  intro parent domainParent child edge
  obtain ⟨parentValid, parentRoot⟩ := domainParent
  have leftNil : ∀ (initial : input.LocalizedRule3PhysicalEndpointCursorFrame fuel),
      input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame parent.occurrence initial →
        input.rule3ShortEndpointCallbackRequests initial.left initial.right
          initial.leftCursor = [] :=
    fun initial frameDecl =>
      tetrahedralRoot_leftRequests_eq_nil input r rootCard parent.occurrence parentRoot
        initial frameDecl
  have callbacks := tetrahedralRoot_extendedRequests_outward input parent leftNil
  change child ∈ input.executableLocalizedRerootChildren parent ++
    (input.rule3ExtendedNodeCallbackRequests parent.occurrence).flatten at edge
  rcases List.mem_append.mp edge with structural | callback
  · have derived := input.executableLocalizedRerootChildren_declarative parent
    have childValid := input.localizedRerootChild_valid parent child
      (input.executableLocalizedRerootChildren parent) derived structural
    have childRoot := input.localizedRerootChildren_root_eq parent child
      (input.executableLocalizedRerootChildren parent) derived structural
    exact ⟨⟨childValid, childRoot.trans parentRoot⟩,
      tetrahedralRoot_budget_lt_of_executableChild input parent child parentValid structural⟩
  · obtain ⟨request, requestMember, cursorMember⟩ := List.mem_flatten.mp callback
    have outward := callbacks request requestMember child cursorMember
    exact ⟨⟨outward.1, outward.2.1.1.trans parentRoot⟩,
      tetrahedralRoot_budget_lt_of_outward_reference input parent.occurrence parent child rfl
        outward⟩




theorem tetrahedralRoot_extendedPlan_total_of_rootCard
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (r : input.Atom)
    (rootCard : (input.moleculeGraph.neighborFinset r).card ≠ 3)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ root ∈ roots, TetrahedralRootCursorDomain input r root) :
    ∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan :=
  input.prepareExtendedRule3DemandPlan_total_of_acyclic roots
    (tetrahedralRoot_extendedAcyclic_of_rootCard input r rootCard roots rootDomain)


theorem tetrahedralRoot_extendedPlan_stable_of_rootCard
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (r : input.Atom)
    (rootCard : (input.moleculeGraph.neighborFinset r).card ≠ 3)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ root ∈ roots, TetrahedralRootCursorDomain input r root) :
    ∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan ∧
      ∀ (target : input.LocalizedCIPOccurrence fuel)
        (view : input.LocalizedDependencyView target) (budget : Nat),
          plan.bound ≤ budget →
            plan.evaluate target view =
              input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget roots :=
  input.prepareExtendedRule3DemandPlan_constructs_stable_evaluator roots
    (tetrahedralRoot_extendedAcyclic_of_rootCard input r rootCard roots rootDomain)


theorem tetrahedralRoot_preflightPlan_total_of_rootCard
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (r : input.Atom)
    (rootCard : (input.moleculeGraph.neighborFinset r).card ≠ 3)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ root ∈ roots, TetrahedralRootCursorDomain input r root) :
    ∃ plan, input.preparePreflightExtendedDemandPlan roots = .ok plan :=
  input.preparePreflightExtendedDemandPlan_total_of_extendedAcyclic roots
    (tetrahedralRoot_extendedAcyclic_of_rootCard input r rootCard roots rootDomain)

/-! ## Recognized tetrahedral center and the actual four-ligand frame -/

/-- The center-recognition premise supplies the physical degree-four neighbour count. -/
theorem tetrahedralRoot_neighbor_card_of_center
    (input : CertifiedLocalizedCIPInput)
    (r : input.Atom)
    (centerMem : r ∈ input.moleculeGraph.tetrahedralCenterSet) :
    (input.moleculeGraph.neighborFinset r).card = 4 := by
  have center : input.moleculeGraph.IsTetrahedralCenter r :=
    (MoleculeGraph.mem_tetrahedralCenterSet input.moleculeGraph r).mp centerMem
  exact (input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card r).mp center



theorem tetrahedralRoot_frame_seed_domain
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (r : input.Atom)
    (targetRoot : target.1.root = r)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    ∀ root ∈ frame.cursors, TetrahedralRootCursorDomain input r root := by
  intro root present
  exact ⟨input.localizedOccurrenceFourLigandFrame_cursor_valid target frame computed root present,
    (input.localizedOccurrenceFourLigandFrame_cursor_root target frame computed root present).trans
      targetRoot⟩









theorem tetrahedralRoot_center_planTotality
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (r : input.Atom)
    (targetRoot : target.1.root = r)
    (centerMem : r ∈ input.moleculeGraph.tetrahedralCenterSet)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    (∃ plan, input.prepareExtendedRule3DemandPlan frame.cursors = .ok plan) ∧
      (∃ plan, input.prepareExtendedRule3DemandPlan frame.cursors = .ok plan ∧
        ∀ (T : input.LocalizedCIPOccurrence carrierFuel)
          (view : input.LocalizedDependencyView T) (budget : Nat),
            plan.bound ≤ budget →
              plan.evaluate T view =
                input.buildLocalizedExtendedShortCircuitRule3FrameExec? T view budget
                  frame.cursors) ∧
      (∃ plan, input.preparePreflightExtendedDemandPlan frame.cursors = .ok plan) := by
  have cardFour := tetrahedralRoot_neighbor_card_of_center input r centerMem
  have rootCard : (input.moleculeGraph.neighborFinset r).card ≠ 3 := by omega
  have seedDomain := tetrahedralRoot_frame_seed_domain input target r targetRoot frame computed
  exact ⟨tetrahedralRoot_extendedPlan_total_of_rootCard input r rootCard frame.cursors seedDomain,
    tetrahedralRoot_extendedPlan_stable_of_rootCard input r rootCard frame.cursors seedDomain,
    tetrahedralRoot_preflightPlan_total_of_rootCard input r rootCard frame.cursors seedDomain⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TetrahedralRootCursorDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_budget_ge_remaining
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_budget_eq_remaining_of_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_budget_lt_of_outward_reference
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_budget_lt_of_executableChild
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_endpointRequests_right_outward_of_parent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_left_eq_root_of_rootAddress
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_leftRequests_eq_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_spatialRequests_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_oddRequests_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_extendedRequests_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_preflightRequests_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_extendedAcyclic_of_rootCard
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_extendedPlan_total_of_rootCard
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_extendedPlan_stable_of_rootCard
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_preflightPlan_total_of_rootCard
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_neighbor_card_of_center
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_frame_seed_domain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralRoot_center_planTotality
