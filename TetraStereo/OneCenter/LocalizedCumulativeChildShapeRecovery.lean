import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder
import Mathlib.Data.List.GetD

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-!
# Recovering child count and root priority from a cumulative key observable

A cumulative Rules-4a--5 key compiled at a reroot cursor exposes its parent observation before the
merged child spheres:

* the descriptor root sphere is exactly `[([], localizedCumulativeRule45Priority stage label)]`, a
  single entry whose payload is the complete cumulative priority vector of the parent label;
* the three constitutional root spheres are likewise singletons, because
  `MoleculeGraph.officialRuleMajorRootKey` starts every projection with one entry and
  `OfficialRuleMajorKey.assemble` appends the merged child spheres *after* that root sphere;
* at a branch, the first merged sphere contains exactly one entry per sorted child, so the length
  of the second Rule-1a sphere is the child count; at a terminal the second sphere is absent.

`localizedRerootCumulativeChildCount` extracts the child count from the Rule-1a second sphere.  For
every independently derived key it equals the derived child-list length (`0` at a terminal).  The
extraction is a function of `constitutional.rule1a`, hence of the comparison-visible observable, so
equality of two parent observables forces equality of their derived child counts.  The analogous
descriptor statement gives equality of the parent cumulative priority vectors at the derived stage,
and in particular of the Rule-4a unit-kind priority.

Nothing here assumes a key payload, a label, a sibling order or equality of child keys.  The
cross-cursor recursive induction that consumes these facts is *not* proved here.
-/

/-! ## The extraction -/

/-- Child count read from the second Rule-1a sphere of a cumulative key.

A derived terminal key has a one-sphere Rule-1a projection, so this is `0`; a derived branch key
has `rootSphere ++ mergedChildren`, whose second sphere carries one entry per child.  For an
arbitrary (not derivation-backed) key the reading is still well defined but carries no claim: the
root sphere could be absent. -/
def localizedRerootCumulativeChildCount
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) : Nat :=
  (key.constitutional.rule1a.getD 1 []).length

/-! ## Elementary list facts -/

/-- The first sphere of a nonempty `List.range` map is the value at `0`. -/
private theorem getD_zero_map_range {γ : Type*} {count : Nat} (positive : 0 < count)
    (f : Nat → γ) (fallback : γ) :
    ((List.range count).map f).getD 0 fallback = f 0 := by
  cases count with
  | zero => exact absurd positive (Nat.lt_irrefl 0)
  | succ n =>
      rw [List.range_succ_eq_map]
      rfl

/-- The folded maximum dominates its initial accumulator. -/
private theorem le_foldl_max {β : Type*} (measure : β → Nat) :
    ∀ (children : List β) (accumulator : Nat),
      accumulator ≤
        children.foldl (fun longest child => max longest (measure child)) accumulator
  | [], accumulator => Nat.le_refl accumulator
  | head :: tail, accumulator => by
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left accumulator (measure head))
        (le_foldl_max measure tail (max accumulator (measure head)))

/-- A `zipIdx` flat map of singleton batches has one entry per input element, independently of the
starting index. -/
private theorem length_zipIdx_flatMap_of_singleton {β γ : Type*}
    (batch : β × Nat → List γ) :
    ∀ (children : List β) (start : Nat),
      (∀ child ∈ children, ∀ index, (batch (child, index)).length = 1) →
      ((children.zipIdx start).flatMap batch).length = children.length
  | [], _start, _singleton => by simp
  | head :: tail, start, singleton => by
      rw [List.zipIdx_cons, List.flatMap_cons, List.length_append,
        singleton head (by simp) start,
        length_zipIdx_flatMap_of_singleton batch tail (start + 1)
          (fun child present index => singleton child (by simp [present]) index)]
      simp only [List.length_cons]
      omega

/-! ## First spheres of a compiled root and of an assembled parent -/

/-- The Rule-1a root sphere of `officialRuleMajorRootKey` is a singleton. -/
theorem officialRuleMajorRootKey_rule1a_length {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (complete : Bool) :
    (m.officialRuleMajorRootKey node complete).rule1a.length = 1 := by
  simp [MoleculeGraph.officialRuleMajorRootKey]

/-- A root sphere of length one is the first sphere of `assemble`, whatever the merged children
contribute: `assemble` appends the merged child spheres after the root spheres. -/
theorem assemble_rule1a_getD_one_length {V : Type*}
    (root : OfficialRuleMajorKey V) (children : List (OfficialRuleMajorKey V))
    (rootLength : root.rule1a.length = 1) :
    ((OfficialRuleMajorKey.assemble root children).rule1a.getD 1 []).length =
      ((OfficialRuleMajorKey.mergeChildren children OfficialRuleMajorKey.rule1a).getD
        0 []).length := by
  simp only [OfficialRuleMajorKey.assemble]
  rw [List.getD_append_right _ _ _ _ (by rw [rootLength]), rootLength, Nat.sub_self]

/-- The first merged sphere of a nonempty child list with singleton first child spheres has exactly
one entry per child. -/
theorem mergeChildren_getD_zero_length {V α : Type*}
    (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α)))
    (nonempty : children ≠ [])
    (firstSphere : ∀ child ∈ children, ((layers child).getD 0 []).length = 1) :
    ((OfficialRuleMajorKey.mergeChildren children layers).getD 0 []).length =
      children.length := by
  have layerNonempty : ∀ child ∈ children, layers child ≠ [] := by
    intro child present empty
    have singleton := firstSphere child present
    rw [empty] at singleton
    simp at singleton
  have layerPositive : ∀ child ∈ children, 0 < (layers child).length :=
    fun child present => List.length_pos_iff.mpr (layerNonempty child present)
  have countPositive : 0 < children.foldl
      (fun longest child => max longest (layers child).length) 0 := by
    cases children with
    | nil => exact absurd rfl nonempty
    | cons head tail =>
        simp only [List.foldl_cons, Nat.zero_max]
        exact Nat.lt_of_lt_of_le (layerPositive head (by simp))
          (le_foldl_max (fun child => (layers child).length) tail (layers head).length)
  have unfolded : OfficialRuleMajorKey.mergeChildren children layers =
      (List.range (children.foldl
        (fun longest child => max longest (layers child).length) 0)).map
        (fun depth => children.zipIdx.flatMap fun child =>
          OfficialRuleMajorKey.prefixLayer child.2 ((layers child.1).getD depth [])) := rfl
  rw [unfolded, getD_zero_map_range countPositive]
  exact length_zipIdx_flatMap_of_singleton
    (fun child => OfficialRuleMajorKey.prefixLayer child.2 ((layers child.1).getD 0 []))
    children 0
    (fun child present index => by
      simpa [OfficialRuleMajorKey.prefixLayer] using firstSphere child present)

/-! ## The exact root shape of a declaratively derived key -/

/-- Every derived key starts with a singleton Rule-1a sphere: the constitutional component of a
terminal key is the root key itself, and a branch key is an `assemble` whose root spheres are
appended before any merged child sphere. -/
theorem declarativeCumulativeKey_rootRule1a_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (derived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuel cursor key) :
    (key.constitutional.rule1a.getD 0 []).length = 1 := by
  cases derived with
  | terminal frame empty observed =>
      simp [MoleculeGraph.officialRuleMajorRootKey]
  | branch frame nonempty observed childDerivations ranking descending =>
      simp [OfficialRuleMajorKey.assemble, MoleculeGraph.officialRuleMajorRootKey]

/-- The Rule-1a, Rule-1b and Rule-2 root spheres of any derived key are each a single entry. -/
theorem declarativeCumulativeKey_constitutional_first_sphere
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (derived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuel cursor key) :
    (key.constitutional.rule1a.getD 0 []).length = 1 ∧
      (key.constitutional.rule1b.getD 0 []).length = 1 ∧
        (key.constitutional.rule2.getD 0 []).length = 1 := by
  cases derived with
  | terminal frame empty observed =>
      simp [MoleculeGraph.officialRuleMajorRootKey]
  | branch frame nonempty observed childDerivations ranking descending =>
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [OfficialRuleMajorKey.assemble, MoleculeGraph.officialRuleMajorRootKey]

/-- The descriptor of a derived key is the one-entry root sphere carrying the complete cumulative
priority vector of the observed parent label, followed by the merged child descriptors. -/
theorem declarativeCumulativeKey_descriptor_root
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (derived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuel cursor key) :
    ∃ (label : Option LocalizedAuxiliaryLabel)
      (tail : List (List (OfficialSparseEntry (List Nat)))),
      key.descriptor =
        [[([], localizedCumulativeRule45Priority stage label)]] ++ tail := by
  cases derived with
  | terminal frame empty observed => exact ⟨_, [], rfl⟩
  | branch frame nonempty observed childDerivations ranking descending =>
      exact ⟨_, _, rfl⟩

/-- The root descriptor sphere of a derived key is the single entry carrying the parent's complete
cumulative priority vector. -/
theorem declarativeCumulativeKey_descriptor_root_getD_zero
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (derived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuel cursor key) :
    ∃ label : Option LocalizedAuxiliaryLabel,
      key.descriptor.getD 0 [] =
        [([], localizedCumulativeRule45Priority stage label)] := by
  rcases input.declarativeCumulativeKey_descriptor_root stage target view derived with
    ⟨label, tail, shape⟩
  exact ⟨label, by rw [shape]; rfl⟩

/-- A derived key never has an empty descriptor: the root sphere is always present. -/
theorem declarativeCumulativeKey_descriptor_ne_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (derived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuel cursor key) :
    key.descriptor ≠ [] := by
  rcases input.declarativeCumulativeKey_descriptor_root stage target view derived with
    ⟨label, tail, shape⟩
  rw [shape]
  simp

/-! ## Child lists of independent derivations -/

/-- Pointwise derivations pair equal-length cursor and key lists. -/
theorem declarativeCumulativeKeyList_length
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key,
      input.DeclarativeLocalizedRerootCumulativeRule45KeyList
          stage target view fuel cursors keys →
        keys.length = cursors.length := by
  induction cursors with
  | nil =>
      intro keys derived
      cases derived with
      | nil => rfl
  | cons cursor cursors inductionHypothesis =>
      intro keys derived
      cases derived with
      | cons head tail => simp [inductionHypothesis _ tail]

/-- Every key of a pointwise derived child list has a singleton Rule-1a root sphere. -/
theorem declarativeCumulativeKeyList_rootRule1a_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key,
      input.DeclarativeLocalizedRerootCumulativeRule45KeyList
          stage target view fuel cursors keys →
        ∀ key ∈ keys, (key.constitutional.rule1a.getD 0 []).length = 1 := by
  induction cursors with
  | nil =>
      intro keys derived key present
      cases derived with
      | nil => simp at present
  | cons cursor cursors inductionHypothesis =>
      intro keys derived key present
      cases derived with
      | cons head tail =>
          rcases List.mem_cons.mp present with same | tailPresent
          · subst same
            exact input.declarativeCumulativeKey_rootRule1a_head stage target view head
          · exact inductionHypothesis _ tail key tailPresent

/-! ## Child count of a branch parent -/

/-- A branch key's extracted child count is exactly the number of derived children.  The merged
first sphere is placed after the one-sphere root, and every sorted child contributes exactly one
entry to it.  No key payload, label or sibling order is assumed. -/
theorem branch_rootChildCount
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {children : List (input.LocalizedRerootCursor carrierFuel)}
    {label : Option LocalizedAuxiliaryLabel}
    {childKeys sorted : List input.LocalizedRerootCumulativeRule45Key}
    (nonempty : children ≠ [])
    (childDerivations : input.DeclarativeLocalizedRerootCumulativeRule45KeyList
      stage target view fuel children childKeys)
    (ranking : sorted.Perm childKeys) :
    input.localizedRerootCumulativeChildCount
      { constitutional := OfficialRuleMajorKey.assemble
          (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false)
          (sorted.map fun child => child.constitutional)
        descriptor := [[([], localizedCumulativeRule45Priority stage label)]] ++
          input.mergeLocalizedRerootDescriptorChildren sorted
        labels := [[([], label)]] ++ input.mergeLocalizedRerootLabelChildren sorted
        rankedLabels := [[([], label)]] ++
          input.mergeLocalizedRerootRankedLabelChildren sorted } =
      children.length := by
  have mappedNonempty :
      (sorted.map fun child => child.constitutional) ≠ [] := by
    intro empty
    have sortedEmpty : sorted = [] := List.map_eq_nil_iff.mp empty
    have childKeysEmpty : childKeys.length = 0 := by
      rw [← ranking.length_eq, sortedEmpty]
      rfl
    have childrenEmpty : children.length = 0 := by
      rw [← input.declarativeCumulativeKeyList_length stage target view children
        childKeys childDerivations, childKeysEmpty]
    exact nonempty (List.eq_nil_of_length_eq_zero childrenEmpty)
  have firstSphere : ∀ key ∈ sorted.map (fun child => child.constitutional),
      ((OfficialRuleMajorKey.rule1a key).getD 0 []).length = 1 := by
    intro key present
    rw [List.mem_map] at present
    rcases present with ⟨child, childPresent, rfl⟩
    exact input.declarativeCumulativeKeyList_rootRule1a_head stage target view children
      childKeys childDerivations child (ranking.mem_iff.mp childPresent)
  unfold localizedRerootCumulativeChildCount
  change ((OfficialRuleMajorKey.assemble
      (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false)
      (sorted.map fun child => child.constitutional)).rule1a.getD 1 []).length =
    children.length
  rw [assemble_rule1a_getD_one_length _ _
    (officialRuleMajorRootKey_rule1a_length _ _ _)]
  rw [mergeChildren_getD_zero_length _ OfficialRuleMajorKey.rule1a mappedNonempty
      firstSphere,
    List.length_map, ranking.length_eq,
    input.declarativeCumulativeKeyList_length stage target view children childKeys
      childDerivations]

/-! ## Frames and child counts -/

/-- A derived key records a unique child list at its cursor: two independent frame descriptions of
the same cursor agree. -/
theorem declarativeRerootChildren_unique
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {children other : List (input.LocalizedRerootCursor carrierFuel)}
    (left : input.DeclarativeLocalizedRerootChildren cursor children)
    (right : input.DeclarativeLocalizedRerootChildren cursor other) :
    children = other :=
  Option.some.inj
    (((input.localizedRerootChildren?_eq_some_iff cursor children).mpr left).symm.trans
      ((input.localizedRerootChildren?_eq_some_iff cursor other).mpr right))

/-- The extracted child count of an independently derived key is the number of its children. -/
theorem declarativeCumulativeKey_rootChildCount_exists
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (derived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuel cursor key) :
    ∃ children : List (input.LocalizedRerootCursor carrierFuel),
      input.DeclarativeLocalizedRerootChildren cursor children ∧
        input.localizedRerootCumulativeChildCount key = children.length := by
  cases derived with
  | terminal frame empty observed =>
      cases empty
      exact ⟨[], frame,
        by simp [localizedRerootCumulativeChildCount,
          MoleculeGraph.officialRuleMajorRootKey]⟩
  | branch frame nonempty observed childDerivations ranking descending =>
      exact ⟨_, frame, branch_rootChildCount (input := input) (stage := stage)
        (target := target) (view := view) nonempty childDerivations ranking⟩

/-- The extracted child count of any derived key equals the length of any exact frame description
of its cursor.  This covers both constructors: a terminal derivation forces its frame to be empty,
a branch derivation supplies the nonempty child list. -/
theorem declarativeCumulativeKey_rootChildCount_eq_frame_length
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    {children : List (input.LocalizedRerootCursor carrierFuel)}
    (derived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuel cursor key)
    (frame : input.DeclarativeLocalizedRerootChildren cursor children) :
    input.localizedRerootCumulativeChildCount key = children.length := by
  rcases input.declarativeCumulativeKey_rootChildCount_exists stage target view derived with
    ⟨other, otherFrame, count⟩
  rw [count, input.declarativeRerootChildren_unique otherFrame frame]

/-- A key derived at a terminal cursor extracts child count zero. -/
theorem declarativeCumulativeKey_rootChildCount_eq_zero_of_nil_frame
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (derived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuel cursor key)
    (frame : input.DeclarativeLocalizedRerootChildren cursor []) :
    input.localizedRerootCumulativeChildCount key = 0 := by
  rw [input.declarativeCumulativeKey_rootChildCount_eq_frame_length stage target view
    derived frame]
  rfl

/-- A key derived at a branch cursor extracts a positive child count. -/
theorem declarativeCumulativeKey_rootChildCount_pos_of_nonempty_frame
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    {children : List (input.LocalizedRerootCursor carrierFuel)}
    (derived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuel cursor key)
    (frame : input.DeclarativeLocalizedRerootChildren cursor children)
    (nonempty : children ≠ []) :
    0 < input.localizedRerootCumulativeChildCount key := by
  rw [input.declarativeCumulativeKey_rootChildCount_eq_frame_length stage target view
    derived frame]
  exact List.length_pos_iff.mpr nonempty

/-! ## Observable equality forces shape agreement -/

/-- Equality of two cumulative key observables forces equality of the extracted child counts.  The
extraction reads only `constitutional.rule1a`, which the observable records. -/
theorem localizedRerootCumulativeChildCount_eq_of_observable_eq
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootCumulativeRule45Key}
    (observableEq : input.localizedRerootCumulativeRule45Observable left =
      input.localizedRerootCumulativeRule45Observable right) :
    input.localizedRerootCumulativeChildCount left =
      input.localizedRerootCumulativeChildCount right := by
  have rule1aEq : left.constitutional.rule1a = right.constitutional.rule1a :=
    congrArg LocalizedCumulativeRule45Observable.rule1a observableEq
  unfold localizedRerootCumulativeChildCount
  rw [rule1aEq]

/-- Equality of two derived parent observables forces equality of their child counts, including the
branch/terminal case correspondence: a terminal side has child count zero, so an observably equal
branch side must also have an empty child list. -/
theorem childCount_eq_of_observable_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {fuelLeft fuelRight : Nat}
    {cursorLeft cursorRight : input.LocalizedRerootCursor carrierFuel}
    {keyLeft keyRight : input.LocalizedRerootCumulativeRule45Key}
    {childrenLeft childrenRight : List (input.LocalizedRerootCursor carrierFuel)}
    (leftDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuelLeft cursorLeft keyLeft)
    (rightDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuelRight cursorRight keyRight)
    (leftFrame : input.DeclarativeLocalizedRerootChildren cursorLeft childrenLeft)
    (rightFrame : input.DeclarativeLocalizedRerootChildren cursorRight childrenRight)
    (observableEq : input.localizedRerootCumulativeRule45Observable keyLeft =
      input.localizedRerootCumulativeRule45Observable keyRight) :
    childrenLeft.length = childrenRight.length := by
  rw [← input.declarativeCumulativeKey_rootChildCount_eq_frame_length stage target view
        leftDerived leftFrame,
      ← input.declarativeCumulativeKey_rootChildCount_eq_frame_length stage target view
        rightDerived rightFrame]
  exact input.localizedRerootCumulativeChildCount_eq_of_observable_eq observableEq

/-- A nonempty branch derivation and a terminal derivation cannot carry equal observables: their
extracted child counts would disagree with the emptiness of the terminal child list. -/
theorem observable_ne_of_nonempty_nil_frames
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {fuelLeft fuelRight : Nat}
    {cursorLeft cursorRight : input.LocalizedRerootCursor carrierFuel}
    {keyLeft keyRight : input.LocalizedRerootCumulativeRule45Key}
    {children : List (input.LocalizedRerootCursor carrierFuel)}
    (leftDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuelLeft cursorLeft keyLeft)
    (rightDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuelRight cursorRight keyRight)
    (leftFrame : input.DeclarativeLocalizedRerootChildren cursorLeft children)
    (rightFrame : input.DeclarativeLocalizedRerootChildren cursorRight [])
    (nonempty : children ≠ []) :
    input.localizedRerootCumulativeRule45Observable keyLeft ≠
      input.localizedRerootCumulativeRule45Observable keyRight := by
  intro observableEq
  have lengths := input.childCount_eq_of_observable_eq stage target view
    leftDerived rightDerived leftFrame rightFrame observableEq
  exact nonempty (List.eq_nil_of_length_eq_zero (by simpa using lengths))

/-- Equality of two derived parent observables forces equality of the complete root cumulative
priority vectors recorded in their descriptor root spheres, without assuming equal labels or key
payloads. -/
theorem rootPriority_eq_of_observable_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuelLeft fuelRight : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {cursorLeft cursorRight : input.LocalizedRerootCursor carrierFuel}
    {keyLeft keyRight : input.LocalizedRerootCumulativeRule45Key}
    (leftDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuelLeft cursorLeft keyLeft)
    (rightDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      stage target view fuelRight cursorRight keyRight)
    (observableEq : input.localizedRerootCumulativeRule45Observable keyLeft =
      input.localizedRerootCumulativeRule45Observable keyRight) :
    ∃ labelLeft labelRight : Option LocalizedAuxiliaryLabel,
      keyLeft.descriptor.getD 0 [] =
          [([], localizedCumulativeRule45Priority stage labelLeft)] ∧
        keyRight.descriptor.getD 0 [] =
          [([], localizedCumulativeRule45Priority stage labelRight)] ∧
          localizedCumulativeRule45Priority stage labelLeft =
            localizedCumulativeRule45Priority stage labelRight := by
  rcases input.declarativeCumulativeKey_descriptor_root_getD_zero stage target view
    leftDerived with ⟨labelLeft, shapeLeft⟩
  rcases input.declarativeCumulativeKey_descriptor_root_getD_zero stage target view
    rightDerived with ⟨labelRight, shapeRight⟩
  have descriptorEq : keyLeft.descriptor = keyRight.descriptor :=
    congrArg LocalizedCumulativeRule45Observable.descriptor observableEq
  have getDEq : keyLeft.descriptor.getD 0 [] = keyRight.descriptor.getD 0 [] := by
    rw [descriptorEq]
  rw [shapeLeft, shapeRight] at getDEq
  have priorities : localizedCumulativeRule45Priority stage labelLeft =
      localizedCumulativeRule45Priority stage labelRight := by
    simpa using getDEq
  exact ⟨labelLeft, labelRight, shapeLeft, shapeRight, priorities⟩

/-- At Rule 4a the root priority is the unit-kind priority `localizedRule4aPriority`; observable
equality of two derived Rule-4a parents forces it to agree even when their labels differ. -/
theorem rule4a_rootPriority_eq_of_observable_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuelLeft fuelRight : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {cursorLeft cursorRight : input.LocalizedRerootCursor carrierFuel}
    {keyLeft keyRight : input.LocalizedRerootCumulativeRule45Key}
    (leftDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      LocalizedCumulativeRule45Stage.rule4a target view fuelLeft cursorLeft keyLeft)
    (rightDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      LocalizedCumulativeRule45Stage.rule4a target view fuelRight cursorRight keyRight)
    (observableEq : input.localizedRerootCumulativeRule45Observable keyLeft =
      input.localizedRerootCumulativeRule45Observable keyRight) :
    ∃ labelLeft labelRight : Option LocalizedAuxiliaryLabel,
      keyLeft.descriptor.getD 0 [] =
          [([], [localizedRule4aPriority labelLeft])] ∧
        keyRight.descriptor.getD 0 [] =
          [([], [localizedRule4aPriority labelRight])] ∧
          localizedRule4aPriority labelLeft = localizedRule4aPriority labelRight := by
  rcases input.rootPriority_eq_of_observable_eq
    LocalizedCumulativeRule45Stage.rule4a target view
    leftDerived rightDerived observableEq with
    ⟨labelLeft, labelRight, shapeLeft, shapeRight, priorities⟩
  refine ⟨labelLeft, labelRight, ?_, ?_, ?_⟩
  · simpa [localizedCumulativeRule45Priority] using shapeLeft
  · simpa [localizedCumulativeRule45Priority] using shapeRight
  · simpa [localizedCumulativeRule45Priority] using priorities

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
