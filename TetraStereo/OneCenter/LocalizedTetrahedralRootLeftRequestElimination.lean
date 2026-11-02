import TetraStereo.OneCenter.LocalizedNonrootLeftRequestElimination
import TetraStereo.OneCenter.LocalizedOfficialContextPerception
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Left-endpoint request elimination at a tetrahedral carrier root

Let `O` be an actual physical endpoint occurrence of an open even axis in a carrier rooted at the
atom `r`, and let `initial` be the physical endpoint cursor frame declared at `O`.  Write
`P := initial.leftCursor.occurrence` for the actual carrier parent of `O`.  The carrier parent is
the endpoint occurrence whose current atom is the left endpoint `initial.left`.

This module proves that the left-endpoint request list

`input.rule3ShortEndpointCallbackRequests initial.left initial.right initial.leftCursor`

is literally empty whenever the carrier root atom does not have exactly three physical neighbours.

The two cases are the two already accepted local facts:

* if `P` is nonroot (`P.address ≠ []`), the published
  `rule3ShortEndpointCallbackRequests_eq_nil_of_nonroot` applies with no degree hypothesis;
* if `P` is the carrier root (`P.address = []`), the declarative occurrence at the empty address is
  the official root node for `P.root`, so the current atom of `P` is exactly `P.root`.  The frame
  declaration identifies that current atom with `initial.left`.  The published shape refusal
  `rule3ShortEndpointCallbackRequests_eq_nil_of_neighbor_card_ne_three` then eliminates the list
  from the degree hypothesis at the root atom.

No global or interior degree restriction, no double-bond-neighbour bound, no rank or acyclicity
assumption, and no terminality or branching premise is used.  The degree hypothesis is a single
cardinality inequality at the carrier root atom.

The second half of the module connects the hypothesis to successful *actual* descriptor-center
recognition.  If an actual occurrence `T` at the empty carrier address has
`localizedOccurrenceDescriptorCenter? T = some center`, then `T`'s node is the official root node
and `center.1 = T.root`; the subtype membership `center.2` is exactly the graph shape predicate
"four physical neighbours".  Hence the neighbour count of `T.root` is four, and in particular not
three.  This uses only center recognition: no final descriptor success, no coordinates and no
assumed four-ligand base is needed.  An internal target (nonempty address) is never promoted to a
statement about the original root.

## Exports

* `LocalizedRootDegreeNotThree` -- the stable root-degree predicate.
* `carrierParent_left_eq_root_of_address_nil` -- root atom identification at an empty address.
* `rule3ShortEndpointCallbackRequests_eq_nil_of_parentRoot_card_ne_three` -- general core.
* `rule3ShortEndpointCallbackRequests_eq_nil_of_carrierRoot_card_ne_three` -- carrier-root form.
* `rule3ShortEndpointCallbackRequests_eq_nil_of_root_card_ne_three` -- explicit root atom form.
* `rule3ShortEndpointCallbackRequests_eq_nil_of_carrierRootDegreeNotThree` and
  `..._of_rootDegreeNotThree` -- predicate forms.
* `rule3ShortSpatialCallbackRequests_eq_right_of_carrierRoot_card_ne_three` and
  `rule3ShortOddCallbackRequests_eq_right_of_carrierRoot_card_ne_three` -- the ordinary and odd
  actual request lists equal their right-endpoint lists.
* `rule3ActualRequest_rightEndpoint_and_outward_of_carrierRoot_card_ne_three` -- the same package
  at an arbitrary original descriptor target.
* `neighborFinset_card_eq_four_of_root_descriptorCenter` -- actual center recognition at a root
  supplies the degree hypothesis.
* `rule3ShortEndpointCallbackRequests_eq_nil_of_tetrahedralRoot` and its route packages -- the
  actual tetrahedral-root corollaries.

Every exported declaration is guarded by `assert_kernel_only`.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## The root-degree predicate -/

/-- The carrier root atom does not have exactly three physical neighbours.  This is a single-atom
input-graph cardinality fact; it says nothing about interior atoms. -/
def LocalizedRootDegreeNotThree (input : CertifiedLocalizedCIPInput) (root : input.Atom) : Prop :=
  (input.moleculeGraph.neighborFinset root).card ≠ 3

/-- The predicate is the explicit cardinality inequality. -/
theorem localizedRootDegreeNotThree_iff (input : CertifiedLocalizedCIPInput) (root : input.Atom) :
    input.LocalizedRootDegreeNotThree root ↔
      (input.moleculeGraph.neighborFinset root).card ≠ 3 :=
  Iff.rfl

/-! ## Root-atom identification at an empty address -/

/-- **The carrier parent's current atom is the carrier root at the empty address.**  If the actual
carrier parent `P = initial.leftCursor.occurrence` of a declared physical endpoint frame sits at
the empty carrier address, then its node is the official root node of `P.root`, whose current atom
is `P.root`; the frame declaration identifies that current atom with the left endpoint. -/
theorem carrierParent_left_eq_root_of_address_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial)
    (rootAddress : initial.leftCursor.occurrence.1.address = []) :
    initial.left = initial.leftCursor.occurrence.1.root := by
  rcases frameDecl with
    ⟨_OReal, _OCurrent, _OParent, _OBond, _OParentMem, PCurrent, _PPrevious, _ROcc, _RPrev⟩
  have PDerived : input.DeclarativeLocalizedOccurrence carrierFuel
      initial.leftCursor.occurrence.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel
      initial.leftCursor.occurrence.1).mp initial.leftCursor.occurrence.2
  have rootFrame :=
    input.declarativeLocalizedOccurrence_eq_root_of_address_nil PDerived rootAddress
  have nodeEq : initial.leftCursor.occurrence.1.node =
      OfficialCIPNode.root initial.leftCursor.occurrence.1.root :=
    congrArg LocalizedCIPOccurrenceFrame.node rootFrame
  have rootCurrent : initial.leftCursor.occurrence.1.node.current? =
      some initial.leftCursor.occurrence.1.root := by
    rw [nodeEq]
    rfl
  exact Option.some.inj (PCurrent.symm.trans rootCurrent)

/-! ## General core: degree refusal at the carrier-parent root -/

/-- **Left-endpoint requests are empty when the carrier-parent root has not exactly three
neighbours.**

The carrier parent of `O` is `P = initial.leftCursor.occurrence`.  If `P` is nonroot, the accepted
nonroot elimination applies directly.  If `P` is the carrier root, its current atom is its stored
root and the frame declaration makes that atom the left endpoint; the shape refusal then eliminates
the list from the degree hypothesis.  No other hypothesis is used. -/
theorem rule3ShortEndpointCallbackRequests_eq_nil_of_parentRoot_card_ne_three
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial)
    (cardNe : (input.moleculeGraph.neighborFinset
      initial.leftCursor.occurrence.1.root).card ≠ 3) :
    input.rule3ShortEndpointCallbackRequests initial.left initial.right initial.leftCursor = [] := by
  by_cases rootAddress : initial.leftCursor.occurrence.1.address = []
  · have leftEq :=
      input.carrierParent_left_eq_root_of_address_nil O initial frameDecl rootAddress
    have cardLeft : (input.moleculeGraph.neighborFinset initial.left).card ≠ 3 := by
      rw [leftEq]
      exact cardNe
    exact input.rule3ShortEndpointCallbackRequests_eq_nil_of_neighbor_card_ne_three
      O initial frameDecl cardLeft
  · exact input.rule3ShortEndpointCallbackRequests_eq_nil_of_nonroot
      O initial frameDecl rootAddress

/-! ## Carrier-root and explicit-root forms -/

/-- **Left-endpoint requests are empty when the carrier root `O.root` has not exactly three
neighbours.**  The carrier parent of `O` has the same stored root as `O` by the actual carrier
frame, so the general core applies. -/
theorem rule3ShortEndpointCallbackRequests_eq_nil_of_carrierRoot_card_ne_three
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial)
    (cardNe : (input.moleculeGraph.neighborFinset O.1.root).card ≠ 3) :
    input.rule3ShortEndpointCallbackRequests initial.left initial.right initial.leftCursor = [] := by
  have frameDeclCopy := frameDecl
  rcases frameDeclCopy with
    ⟨_OReal, _OCurrent, _OParent, _OBond, parentMem, _PCurrent, _PPrevious, _ROcc, _RPrev⟩
  have parentFacts := input.localizedCarrierParentFrame_facts O.1
    initial.leftCursor.occurrence.1 parentMem
  have cardParent : (input.moleculeGraph.neighborFinset
      initial.leftCursor.occurrence.1.root).card ≠ 3 := by
    rw [parentFacts.1]
    exact cardNe
  exact input.rule3ShortEndpointCallbackRequests_eq_nil_of_parentRoot_card_ne_three
    O initial frameDecl cardParent

/-- **Left-endpoint requests are empty when the named carrier root `r` has not exactly three
neighbours.**  The occurrence `O` is an actual occurrence of the carrier rooted at `r`. -/
theorem rule3ShortEndpointCallbackRequests_eq_nil_of_root_card_ne_three
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (r : input.Atom)
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial)
    (rootEq : O.1.root = r)
    (cardNe : (input.moleculeGraph.neighborFinset r).card ≠ 3) :
    input.rule3ShortEndpointCallbackRequests initial.left initial.right initial.leftCursor = [] := by
  apply input.rule3ShortEndpointCallbackRequests_eq_nil_of_carrierRoot_card_ne_three
    O initial frameDecl
  rw [rootEq]
  exact cardNe

/-- Predicate form of the carrier-root elimination. -/
theorem rule3ShortEndpointCallbackRequests_eq_nil_of_carrierRootDegreeNotThree
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial)
    (bound : input.LocalizedRootDegreeNotThree O.1.root) :
    input.rule3ShortEndpointCallbackRequests initial.left initial.right initial.leftCursor = [] := by
  unfold LocalizedRootDegreeNotThree at bound
  exact input.rule3ShortEndpointCallbackRequests_eq_nil_of_carrierRoot_card_ne_three
    O initial frameDecl bound

/-- Predicate form of the explicit-root elimination. -/
theorem rule3ShortEndpointCallbackRequests_eq_nil_of_rootDegreeNotThree
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (r : input.Atom)
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial)
    (rootEq : O.1.root = r)
    (bound : input.LocalizedRootDegreeNotThree r) :
    input.rule3ShortEndpointCallbackRequests initial.left initial.right initial.leftCursor = [] := by
  unfold LocalizedRootDegreeNotThree at bound
  exact input.rule3ShortEndpointCallbackRequests_eq_nil_of_root_card_ne_three
    r O initial frameDecl rootEq bound

/-! ## The ordinary and odd actual request lists -/

/-- **Spatial route: only the right endpoint can emit requests.**  For the frame actually recovered
by the physical endpoint cursor recovery on `O`, the actual spatial request list is exactly the
right-endpoint request list.  No target or dependency-view premise is used. -/
theorem rule3ShortSpatialCallbackRequests_eq_right_of_carrierRoot_card_ne_three
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec? O = some frame)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O frame)
    (cardNe : (input.moleculeGraph.neighborFinset O.1.root).card ≠ 3) :
    input.rule3ShortSpatialCallbackRequests O =
      input.rule3ShortEndpointCallbackRequests frame.right frame.left frame.rightCursor := by
  unfold rule3ShortSpatialCallbackRequests
  rw [computed]
  simp [rule3ShortEndpointCallbackRequests_eq_nil_of_carrierRoot_card_ne_three
    input O frame frameDecl cardNe]

/-- **Odd cumulene route: only the right endpoint can emit requests.**  When the odd cumulene
endpoint frame is recovered, the left-endpoint requests of its initial frame vanish and the odd
request list is exactly the right-endpoint request list. -/
theorem rule3ShortOddCallbackRequests_eq_right_of_carrierRoot_card_ne_three
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) O = some topology)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O topology.initial)
    (cardNe : (input.moleculeGraph.neighborFinset O.1.root).card ≠ 3) :
    input.rule3ShortOddCallbackRequests O =
      input.rule3ShortEndpointCallbackRequests topology.right topology.rightPartner
        topology.rightCursor := by
  unfold rule3ShortOddCallbackRequests
  rw [computed]
  simp [rule3ShortEndpointCallbackRequests_eq_nil_of_carrierRoot_card_ne_three
    input O topology.initial frameDecl cardNe]

/-- **Target-rooted package at an arbitrary original descriptor target.**  Let `T` be an original
descriptor target strictly shallower than the physical endpoint occurrence `O`.  For the frame
actually recovered at `O`, if the carrier root has not exactly three neighbours then the actual
spatial request list is exactly the right-endpoint list, and every cursor in every actually
emitted request is an outward cursor of `T`.  No view, no coordinate and no descriptor success is
used. -/
theorem rule3ActualRequest_rightEndpoint_and_outward_of_carrierRoot_card_ne_three
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O T : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency O T)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec? O = some frame)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O frame)
    (cardNe : (input.moleculeGraph.neighborFinset O.1.root).card ≠ 3) :
    input.rule3ShortSpatialCallbackRequests O =
        input.rule3ShortEndpointCallbackRequests frame.right frame.left frame.rightCursor ∧
      (∀ request ∈ input.rule3ShortSpatialCallbackRequests O,
        ∀ cursor ∈ request, OutwardRerootCursor input T cursor) :=
  ⟨input.rule3ShortSpatialCallbackRequests_eq_right_of_carrierRoot_card_ne_three
      O frame computed frameDecl cardNe,
    input.rule3ActualRequest_outward O T deeper⟩

/-! ## Actual root descriptor-center recognition supplies the degree hypothesis -/

/-- **Successful actual center recognition at an empty address has a four-neighbour root.**  Let
`T` be an actual occurrence at the empty carrier address and let `localizedOccurrenceDescriptorCenter?
T` recognise the center `center`.  The declarative root identity makes `T`'s node the official
root node, whose current atom is `T.root`; recognition identifies that atom with `center.1`; the
center subtype carries graph-shape membership, which is exactly neighbour count four. -/
theorem neighborFinset_card_eq_four_of_root_descriptorCenter
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (T : input.LocalizedCIPOccurrence carrierFuel)
    (targetAddress : T.1.address = [])
    (center : input.TetrahedralCenter)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? T = some center) :
    (input.moleculeGraph.neighborFinset T.1.root).card = 4 := by
  have meaning :=
    (input.localizedOccurrenceDescriptorCenter?_eq_some_iff T center).mp centerComputed
  unfold RealTetrahedralCenterNode at meaning
  obtain ⟨_real, centerCurrent⟩ := meaning
  have TDerived : input.DeclarativeLocalizedOccurrence carrierFuel T.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel T.1).mp T.2
  have rootFrame :=
    input.declarativeLocalizedOccurrence_eq_root_of_address_nil TDerived targetAddress
  have nodeEq : T.1.node = OfficialCIPNode.root T.1.root :=
    congrArg LocalizedCIPOccurrenceFrame.node rootFrame
  have rootCurrent : T.1.node.current? = some T.1.root := by
    rw [nodeEq]
    rfl
  have centerEqRoot : center.1 = T.1.root :=
    Option.some.inj (centerCurrent.symm.trans rootCurrent)
  have detected : center.1 ∈ input.moleculeGraph.tetrahedralCenterSet := by
    simpa only [tetrahedralCenterSet] using center.2
  have isTetra : input.moleculeGraph.IsTetrahedralCenter center.1 :=
    (input.moleculeGraph.mem_tetrahedralCenterSet center.1).mp detected
  have cardCenter :=
    (input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card center.1).mp isTetra
  rw [centerEqRoot] at cardCenter
  exact cardCenter

/-- **Actual root center recognition excludes three physical neighbours.** -/
theorem neighborFinset_card_ne_three_of_root_descriptorCenter
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (T : input.LocalizedCIPOccurrence carrierFuel)
    (targetAddress : T.1.address = [])
    (center : input.TetrahedralCenter)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? T = some center) :
    (input.moleculeGraph.neighborFinset T.1.root).card ≠ 3 := by
  rw [input.neighborFinset_card_eq_four_of_root_descriptorCenter
    T targetAddress center centerComputed]
  decide

/-- Predicate form: actual root center recognition establishes the root-degree predicate. -/
theorem localizedRootDegreeNotThree_of_root_descriptorCenter
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (T : input.LocalizedCIPOccurrence carrierFuel)
    (targetAddress : T.1.address = [])
    (center : input.TetrahedralCenter)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? T = some center) :
    input.LocalizedRootDegreeNotThree T.1.root := by
  unfold LocalizedRootDegreeNotThree
  exact input.neighborFinset_card_ne_three_of_root_descriptorCenter
    T targetAddress center centerComputed

/-- The recognized center is the stored root atom of the empty-address occurrence. -/
theorem root_eq_descriptorCenter_of_root_descriptorCenter
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (T : input.LocalizedCIPOccurrence carrierFuel)
    (targetAddress : T.1.address = [])
    (center : input.TetrahedralCenter)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? T = some center) :
    T.1.root = center.1 := by
  have meaning :=
    (input.localizedOccurrenceDescriptorCenter?_eq_some_iff T center).mp centerComputed
  unfold RealTetrahedralCenterNode at meaning
  obtain ⟨_real, centerCurrent⟩ := meaning
  have TDerived : input.DeclarativeLocalizedOccurrence carrierFuel T.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel T.1).mp T.2
  have rootFrame :=
    input.declarativeLocalizedOccurrence_eq_root_of_address_nil TDerived targetAddress
  have nodeEq : T.1.node = OfficialCIPNode.root T.1.root :=
    congrArg LocalizedCIPOccurrenceFrame.node rootFrame
  have rootCurrent : T.1.node.current? = some T.1.root := by
    rw [nodeEq]
    rfl
  exact Option.some.inj (rootCurrent.symm.trans centerCurrent)

/-! ## Actual tetrahedral-root corollaries -/

/-- **Left-endpoint requests are empty at an actually recognized tetrahedral carrier root.**  The
empty-address occurrence `T` is an actual occurrence of the carrier root, and actual center
recognition at `T` supplies the four-neighbour shape, hence the not-three hypothesis.  `O` is any
actual physical endpoint occurrence deeper in the same rooted carrier. -/
theorem rule3ShortEndpointCallbackRequests_eq_nil_of_tetrahedralRoot
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (T : input.LocalizedCIPOccurrence carrierFuel)
    (targetAddress : T.1.address = [])
    (center : input.TetrahedralCenter)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? T = some center)
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial)
    (sameRoot : O.1.root = T.1.root) :
    input.rule3ShortEndpointCallbackRequests initial.left initial.right initial.leftCursor = [] := by
  apply input.rule3ShortEndpointCallbackRequests_eq_nil_of_carrierRoot_card_ne_three
    O initial frameDecl
  rw [sameRoot]
  exact input.neighborFinset_card_ne_three_of_root_descriptorCenter
    T targetAddress center centerComputed

/-- **Left-endpoint requests are empty at an actually recognized tetrahedral carrier root**,
stated with the carrier-parent stored root instead of the occurrence root.  This form matches
callers that only know the physical frame's parent coordinate. -/
theorem rule3ShortEndpointCallbackRequests_eq_nil_of_tetrahedralRoot_parentRoot
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (T : input.LocalizedCIPOccurrence carrierFuel)
    (targetAddress : T.1.address = [])
    (center : input.TetrahedralCenter)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? T = some center)
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial)
    (sameRoot : initial.leftCursor.occurrence.1.root = T.1.root) :
    input.rule3ShortEndpointCallbackRequests initial.left initial.right initial.leftCursor = [] := by
  apply input.rule3ShortEndpointCallbackRequests_eq_nil_of_parentRoot_card_ne_three
    O initial frameDecl
  rw [sameRoot]
  exact input.neighborFinset_card_ne_three_of_root_descriptorCenter
    T targetAddress center centerComputed

/-- **Spatial route at an actually recognized tetrahedral carrier root.**  The actual spatial
request list is exactly the right-endpoint request list. -/
theorem rule3ShortSpatialCallbackRequests_eq_right_of_tetrahedralRoot
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (T : input.LocalizedCIPOccurrence carrierFuel)
    (targetAddress : T.1.address = [])
    (center : input.TetrahedralCenter)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? T = some center)
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec? O = some frame)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O frame)
    (sameRoot : O.1.root = T.1.root) :
    input.rule3ShortSpatialCallbackRequests O =
      input.rule3ShortEndpointCallbackRequests frame.right frame.left frame.rightCursor := by
  apply input.rule3ShortSpatialCallbackRequests_eq_right_of_carrierRoot_card_ne_three
    O frame computed frameDecl
  rw [sameRoot]
  exact input.neighborFinset_card_ne_three_of_root_descriptorCenter
    T targetAddress center centerComputed

/-- **Odd cumulene route at an actually recognized tetrahedral carrier root.**  The actual odd
request list is exactly the right-endpoint request list. -/
theorem rule3ShortOddCallbackRequests_eq_right_of_tetrahedralRoot
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (T : input.LocalizedCIPOccurrence carrierFuel)
    (targetAddress : T.1.address = [])
    (center : input.TetrahedralCenter)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? T = some center)
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) O = some topology)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O topology.initial)
    (sameRoot : O.1.root = T.1.root) :
    input.rule3ShortOddCallbackRequests O =
      input.rule3ShortEndpointCallbackRequests topology.right topology.rightPartner
        topology.rightCursor := by
  apply input.rule3ShortOddCallbackRequests_eq_right_of_carrierRoot_card_ne_three
    O topology computed frameDecl
  rw [sameRoot]
  exact input.neighborFinset_card_ne_three_of_root_descriptorCenter
    T targetAddress center centerComputed

/-- **Actual tetrahedral-root request package.**  For an original descriptor target `T` at the
empty carrier address whose center is actually recognized, every request actually emitted at the
deeper physical occurrence `O` is a right-endpoint request, and every cursor in every such request
is outward of `T`.  The target `T` is the same occurrence at which the center was recognized. -/
theorem rule3ActualRequest_rightEndpoint_and_outward_of_tetrahedralRoot
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (T : input.LocalizedCIPOccurrence carrierFuel)
    (targetAddress : T.1.address = [])
    (center : input.TetrahedralCenter)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? T = some center)
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency O T)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec? O = some frame)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O frame) :
    input.rule3ShortSpatialCallbackRequests O =
        input.rule3ShortEndpointCallbackRequests frame.right frame.left frame.rightCursor ∧
      (∀ request ∈ input.rule3ShortSpatialCallbackRequests O,
        ∀ cursor ∈ request, OutwardRerootCursor input T cursor) := by
  have sameRoot : O.1.root = T.1.root := deeper.1
  exact input.rule3ActualRequest_rightEndpoint_and_outward_of_carrierRoot_card_ne_three
    O T deeper frame computed frameDecl
    (by
      rw [sameRoot]
      exact input.neighborFinset_card_ne_three_of_root_descriptorCenter
        T targetAddress center centerComputed)

/-! ## Computed-only actual route wrappers -/

/-- **Computed-only core wrapper.**  The declarative endpoint frame is derived from the executable
recovery, so callers that only have the computed frame are covered. -/
theorem rule3ShortEndpointCallbackRequests_eq_nil_of_tetrahedralRoot_computed
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (T : input.LocalizedCIPOccurrence carrierFuel)
    (targetAddress : T.1.address = [])
    (center : input.TetrahedralCenter)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? T = some center)
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec? O = some initial)
    (sameRoot : O.1.root = T.1.root) :
    input.rule3ShortEndpointCallbackRequests initial.left initial.right initial.leftCursor = [] :=
  input.rule3ShortEndpointCallbackRequests_eq_nil_of_tetrahedralRoot
    T targetAddress center centerComputed O initial
    (input.localizedRule3PhysicalEndpointCursorFrameExec?_sound O initial computed) sameRoot

/-- **Computed-only spatial wrapper.**  The actual ordinary request list is exactly the
right-endpoint list, with the declarative frame derived from the executable recovery. -/
theorem rule3ShortSpatialCallbackRequests_eq_right_of_tetrahedralRoot_computed
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (T : input.LocalizedCIPOccurrence carrierFuel)
    (targetAddress : T.1.address = [])
    (center : input.TetrahedralCenter)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? T = some center)
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec? O = some frame)
    (sameRoot : O.1.root = T.1.root) :
    input.rule3ShortSpatialCallbackRequests O =
      input.rule3ShortEndpointCallbackRequests frame.right frame.left frame.rightCursor :=
  input.rule3ShortSpatialCallbackRequests_eq_right_of_tetrahedralRoot
    T targetAddress center centerComputed O frame computed
    (input.localizedRule3PhysicalEndpointCursorFrameExec?_sound O frame computed) sameRoot

/-- **Computed-only odd-cumulene wrapper.**  The initial declarative endpoint frame is derived from
the odd-cumulene soundness theorem, so the actual odd request list is exactly the right-endpoint
list from the executable recovery alone. -/
theorem rule3ShortOddCallbackRequests_eq_right_of_tetrahedralRoot_computed
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (T : input.LocalizedCIPOccurrence carrierFuel)
    (targetAddress : T.1.address = [])
    (center : input.TetrahedralCenter)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? T = some center)
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) O = some topology)
    (sameRoot : O.1.root = T.1.root) :
    input.rule3ShortOddCallbackRequests O =
      input.rule3ShortEndpointCallbackRequests topology.right topology.rightPartner
        topology.rightCursor := by
  have originalComputed : input.localizedRule3OddCumuleneEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) O = some topology := by
    rw [← input.localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_original
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) O]
    exact computed
  have sound := input.localizedRule3OddCumuleneEndpointCursorFrame?_sound
    (input.localizedRule3CumulatedTraversalFuel carrierFuel) O topology originalComputed
  exact input.rule3ShortOddCallbackRequests_eq_right_of_tetrahedralRoot
    T targetAddress center centerComputed O topology computed sound.1 sameRoot

/-- **Computed-only target-rooted package.**  For an original descriptor target `T` at the empty
address whose center is actually recognized, and the frame actually recovered at the deeper
occurrence `O`, every emitted request is a right-endpoint request and every request cursor is
outward of `T`.  No declarative frame premise is needed. -/
theorem rule3ActualRequest_rightEndpoint_and_outward_of_tetrahedralRoot_computed
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (T : input.LocalizedCIPOccurrence carrierFuel)
    (targetAddress : T.1.address = [])
    (center : input.TetrahedralCenter)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? T = some center)
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency O T)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec? O = some frame) :
    input.rule3ShortSpatialCallbackRequests O =
        input.rule3ShortEndpointCallbackRequests frame.right frame.left frame.rightCursor ∧
      (∀ request ∈ input.rule3ShortSpatialCallbackRequests O,
        ∀ cursor ∈ request, OutwardRerootCursor input T cursor) :=
  input.rule3ActualRequest_rightEndpoint_and_outward_of_tetrahedralRoot
    T targetAddress center centerComputed O deeper frame computed
    (input.localizedRule3PhysicalEndpointCursorFrameExec?_sound O frame computed)

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_eq_nil_of_tetrahedralRoot_computed
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortSpatialCallbackRequests_eq_right_of_tetrahedralRoot_computed
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortOddCallbackRequests_eq_right_of_tetrahedralRoot_computed
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualRequest_rightEndpoint_and_outward_of_tetrahedralRoot_computed

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRootDegreeNotThree
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRootDegreeNotThree_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierParent_left_eq_root_of_address_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_eq_nil_of_parentRoot_card_ne_three
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_eq_nil_of_carrierRoot_card_ne_three
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_eq_nil_of_root_card_ne_three
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_eq_nil_of_carrierRootDegreeNotThree
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_eq_nil_of_rootDegreeNotThree
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortSpatialCallbackRequests_eq_right_of_carrierRoot_card_ne_three
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortOddCallbackRequests_eq_right_of_carrierRoot_card_ne_three
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualRequest_rightEndpoint_and_outward_of_carrierRoot_card_ne_three
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.neighborFinset_card_eq_four_of_root_descriptorCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.neighborFinset_card_ne_three_of_root_descriptorCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRootDegreeNotThree_of_root_descriptorCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.root_eq_descriptorCenter_of_root_descriptorCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_eq_nil_of_tetrahedralRoot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_eq_nil_of_tetrahedralRoot_parentRoot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortSpatialCallbackRequests_eq_right_of_tetrahedralRoot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortOddCallbackRequests_eq_right_of_tetrahedralRoot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualRequest_rightEndpoint_and_outward_of_tetrahedralRoot

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
