/-
Copyright (c) 2026 TetraStereo contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import TetraStereo.OneCenter.PublicWholeStateDescriptorLocality
import TetraStereo.OneCenter.PublicParentRule3ComparisonInsulation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1000000

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-! ## Generic `List.mapM` helpers -/

/-- A successful `mapM` preserves the list length. -/
private theorem model_list_mapM_length_eq {α β : Type*} (f : α → Option β) :
    ∀ (values : List α) (results : List β),
      values.mapM f = some results → results.length = values.length
  | [], results, computed => by
      simp at computed
      subst results
      rfl
  | value :: values, results, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : f value with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : values.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst results
              simp [model_list_mapM_length_eq f values tail tailComputed]

/-- A successful `mapM` applied at an index returns the computed value stored at that index. -/
private theorem model_list_mapM_get_some {α β : Type*} (f : α → Option β) :
    ∀ (values : List α) (results : List β),
      values.mapM f = some results →
      ∀ (index : Nat) (valuesBound : index < values.length)
        (resultsBound : index < results.length),
        f (values[index]'valuesBound) = some (results[index]'resultsBound)
  | [], results, computed, index, valuesBound, _ => by
      simp at valuesBound
  | value :: values, results, computed, index, valuesBound, resultsBound => by
      rw [List.mapM_cons] at computed
      cases headComputed : f value with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : values.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst results
              cases index with
              | zero => simpa using headComputed
              | succ index =>
                  have valuesBound' : index < values.length := by simpa using valuesBound
                  have resultsBound' : index < tail.length := by simpa using resultsBound
                  simpa using
                    model_list_mapM_get_some f values tail tailComputed index
                      valuesBound' resultsBound'

/-- Pointwise equality on the members of a list lifts through `List.mapM`. -/
private theorem model_list_mapM_congr_on {α β : Type*} (first second : α → Option β) :
    ∀ (values : List α),
      (∀ value, value ∈ values → first value = second value) →
      values.mapM first = values.mapM second
  | [], _ => rfl
  | value :: values, agrees => by
      simp [List.mapM_cons, agrees value (by simp),
        model_list_mapM_congr_on first second values
          (fun member memberPresent => agrees member (by simp [memberPresent]))]

/-! ## Actual self-comparison records -/

/-- The Rule-5 reading comparator is reflexive on every reading list. -/
theorem compareAromaticCanonicalRerootCompoundRule5Readings_self
    (source : AuthoritativeChemicalInput) (commonReference : RS)
    (readings : List source.AromaticCanonicalRerootRule5Reading) :
    source.compareAromaticCanonicalRerootCompoundRule5Readings
      commonReference readings readings = Ordering.eq := by
  letI : Std.TransCmp
      (source.compareAromaticCanonicalRerootCompoundRule5Readings commonReference) :=
    source.compareAromaticCanonicalRerootCompoundRule5Readings_transCmp commonReference
  exact Std.ReflCmp.compare_self

/-- The prior Rules-4b/4c comparator is reflexive on every prior key. -/
theorem compareAromaticCanonicalRerootCompoundRule4bcKeys_self
    (source : AuthoritativeChemicalInput)
    (key : source.AromaticCanonicalRerootCompoundRule4bcKey) :
    source.compareAromaticCanonicalRerootCompoundRule4bcKeys key key = Ordering.eq := by
  letI : Std.TransCmp source.compareAromaticCanonicalRerootCompoundRule4bcKeys :=
    source.compareAromaticCanonicalRerootCompoundRule4bcKeys_transCmp
  exact Std.ReflCmp.compare_self

/-- **Actual self-comparison record equality.**  Comparing one compound through-Rule-5 key with
itself returns exactly `{ordering := eq, pseudo := false}`, including the pseudoasymmetry flag.
This is the diagonal parent/parent case needed when the same four-ligand slot is compared with
itself. -/
theorem compareAromaticCanonicalRerootCompoundThroughRule5_self
    (source : AuthoritativeChemicalInput)
    (key : source.AromaticCanonicalRerootCompoundRule45Key) :
    source.compareAromaticCanonicalRerootCompoundThroughRule5 key key =
      { ordering := Ordering.eq, pseudo := false } := by
  unfold compareAromaticCanonicalRerootCompoundThroughRule5
  rw [source.compareAromaticCanonicalRerootCompoundRule4bcKeys_self]
  simp [source.compareAromaticCanonicalRerootCompoundRule5Readings_self]

/-! ## The public declarative occurrence tree: address functionality

The public occurrence carrier of `AuthoritativeSemanticMancudeOccurrenceFixedPoint` is a bounded
official subtree enumeration.  The following structural lemmas are the public analogue of the
localized carrier functionality facts; they are proved directly against the public children
function `SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt` and do not import any localized
solver semantics. -/

/-- A bounded official public subtree is functional at root-relative addresses: two derivations
from the same official root cannot attach different provenance-bearing nodes or remaining depths
to the same sibling address. -/
theorem declarativeAromaticCanonicalOccurrenceSubtree_functional_at_address
    (source : AuthoritativeChemicalInput)
    {root : source.AromaticCanonicalAtom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {left right : source.AromaticCanonicalOccurrenceFrame}
    (leftDerived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node left)
    (rightDerived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node right)
    (sameAddress : left.address = right.address) :
    left = right := by
  induction leftDerived generalizing right with
  | subtreeRoot =>
      exact source.declarativeAromaticCanonicalOccurrenceSubtree_eq_root_of_address_eq
        rightDerived (by simpa using sameAddress.symm) |>.symm
  | @subtreeDescendant path fuel node leftChild leftSlot left
      leftChildAtSlot leftBelow inductionHypothesis =>
      cases rightDerived with
      | subtreeRoot =>
          have addressPrefix :=
            source.declarativeAromaticCanonicalOccurrenceSubtree_addressPrefix leftBelow
          have lengthBound := addressPrefix.length_le
          rw [sameAddress] at lengthBound
          simp at lengthBound
      | @subtreeDescendant _ _ _ rightChild rightSlot right
          rightChildAtSlot rightBelow =>
          have leftPrefix :=
            source.declarativeAromaticCanonicalOccurrenceSubtree_addressPrefix leftBelow
          have rightPrefix :=
            source.declarativeAromaticCanonicalOccurrenceSubtree_addressPrefix rightBelow
          rw [sameAddress] at leftPrefix
          have prefixIdentity : path ++ [leftSlot] = path ++ [rightSlot] := by
            rw [List.prefix_iff_eq_take] at leftPrefix rightPrefix
            calc
              path ++ [leftSlot] =
                  (right.address.take (path ++ [leftSlot]).length) := leftPrefix
              _ = right.address.take (path ++ [rightSlot]).length := by simp
              _ = path ++ [rightSlot] := rightPrefix.symm
          have slotIdentity : leftSlot = rightSlot := by
            simpa using prefixIdentity
          subst rightSlot
          have leftIndexed := List.mem_zipIdx leftChildAtSlot
          have rightIndexed := List.mem_zipIdx rightChildAtSlot
          have childIdentity : leftChild = rightChild := by
            simpa using leftIndexed.2.2.trans rightIndexed.2.2.symm
          subst rightChild
          exact inductionHypothesis rightBelow sameAddress

/-- If two occurrences lie in the same official subtree and the second address is exactly one
sibling slot below the first, then its node is exactly the executable official child at that
slot. -/
theorem declarativeAromaticCanonicalOccurrenceSubtree_immediate_child
    (source : AuthoritativeChemicalInput)
    {root : source.AromaticCanonicalAtom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {parent childOccurrence : source.AromaticCanonicalOccurrenceFrame}
    (parentDerived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node parent)
    (childDerived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node childOccurrence)
    (slot : Nat)
    (childAddress : childOccurrence.address = parent.address ++ [slot]) :
    ∃ child,
      (child, slot) ∈
          (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
            source.molecule.atomCount parent.node).zipIdx ∧
        childOccurrence =
          { root := parent.root
            address := parent.address ++ [slot]
            node := child
            remaining := parent.remaining - 1 } := by
  induction parentDerived generalizing childOccurrence with
  | subtreeRoot =>
      cases childDerived with
      | subtreeRoot => simp at childAddress
      | @subtreeDescendant _ childFuel _ child childSlot childOccurrence
          childAtSlot below =>
          have belowPrefix :=
            source.declarativeAromaticCanonicalOccurrenceSubtree_addressPrefix below
          rw [childAddress] at belowPrefix
          have prefixIdentity := belowPrefix.eq_of_length (by simp)
          have slotIdentity : childSlot = slot := by simpa using prefixIdentity
          subst childSlot
          have childIdentity :=
            source.declarativeAromaticCanonicalOccurrenceSubtree_eq_root_of_address_eq
              below (by simpa using childAddress)
          exact ⟨child, childAtSlot, by simpa using childIdentity⟩
  | @subtreeDescendant path fuel node parentChild parentSlot parent
      parentAtSlot parentBelow inductionHypothesis =>
      cases childDerived with
      | subtreeRoot =>
          have parentPrefix :=
            source.declarativeAromaticCanonicalOccurrenceSubtree_addressPrefix parentBelow
          have lengthBound := parentPrefix.length_le
          change path = parent.address ++ [slot] at childAddress
          rw [childAddress] at lengthBound
          simp at lengthBound
      | @subtreeDescendant _ _ _ candidateChild candidateSlot childOccurrence
          candidateAtSlot candidateBelow =>
          have parentPrefix :=
            source.declarativeAromaticCanonicalOccurrenceSubtree_addressPrefix parentBelow
          have parentPrefixChild : path ++ [parentSlot] <+:
              childOccurrence.address := by
            apply parentPrefix.trans
            rw [childAddress]
            exact List.prefix_append _ _
          have candidatePrefix :=
            source.declarativeAromaticCanonicalOccurrenceSubtree_addressPrefix candidateBelow
          have topPrefixIdentity :
              path ++ [parentSlot] = path ++ [candidateSlot] := by
            rw [List.prefix_iff_eq_take] at parentPrefixChild candidatePrefix
            calc
              path ++ [parentSlot] =
                  childOccurrence.address.take (path ++ [parentSlot]).length :=
                parentPrefixChild
              _ = childOccurrence.address.take
                  (path ++ [candidateSlot]).length := by simp
              _ = path ++ [candidateSlot] := candidatePrefix.symm
          have topSlotIdentity : parentSlot = candidateSlot := by
            simpa using topPrefixIdentity
          subst candidateSlot
          have parentIndexed := List.mem_zipIdx parentAtSlot
          have candidateIndexed := List.mem_zipIdx candidateAtSlot
          have topChildIdentity : parentChild = candidateChild := by
            simpa using parentIndexed.2.2.trans candidateIndexed.2.2.symm
          subst candidateChild
          exact inductionHypothesis candidateBelow childAddress

/-! ## Provenance of public official children -/

/-- A provenance generated by the canonical digraph: real atom or one of the two duplicate
kinds.  Placeholder provenance never arises in a graph-generated node. -/
def OfficialCIPNodeProvenanceGenerated : OfficialCIPNodeProvenance → Prop
  | .realAtom => True
  | .multipleBondDuplicate _ => True
  | .ringDuplicate _ => True
  | .placeholder _ _ => False

/-- The real-atom provenance is generated. -/
theorem officialCIPNodeProvenanceGenerated_realAtom :
    OfficialCIPNodeProvenanceGenerated OfficialCIPNodeProvenance.realAtom := trivial

/-- A generated provenance that is not a duplicate leaf is the real-atom provenance. -/
theorem officialCIPNodeProvenanceGenerated_eq_realAtom_of_not_duplicateLeaf
    {provenance : OfficialCIPNodeProvenance}
    (generated : OfficialCIPNodeProvenanceGenerated provenance)
    (nonduplicate : provenance.isDuplicateLeaf = false) :
    provenance = OfficialCIPNodeProvenance.realAtom := by
  cases provenance with
  | realAtom => rfl
  | multipleBondDuplicate distance =>
      simp [OfficialCIPNodeProvenance.isDuplicateLeaf] at nonduplicate
  | ringDuplicate distance =>
      simp [OfficialCIPNodeProvenance.isDuplicateLeaf] at nonduplicate
  | placeholder kind distance =>
      simp [OfficialCIPNodeProvenanceGenerated] at generated

/-- Every canonical child of a public official node is produced by an `extend` or a virtual
mancude duplicate, hence advances the stored history by one sphere. -/
theorem aromaticCanonicalOfficialCIPChildrenAt_history
    (source : SemanticMolecule) (size : Nat)
    {node child : OfficialCIPNode (Fin size)}
    (present : child ∈ source.aromaticCanonicalOfficialCIPChildrenAt size node) :
    ∃ next : Fin size, child.history = next :: node.history := by
  by_cases duplicate : node.isDuplicateLeaf = true
  · simp [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt, duplicate] at present
  · unfold SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt at present
    rw [if_neg duplicate] at present
    dsimp only at present
    rcases List.mem_append.mp present with ordinary | virtual
    · rcases List.mem_map.mp ordinary with ⟨copy, _copyPresent, rfl⟩
      exact ⟨copy.1, by simp [OfficialCIPNode.extend]⟩
    · cases current : node.current? with
      | none => simp [current] at virtual
      | some attached =>
          cases representative :
              source.aromaticCanonicalMancudeRepresentativeAt? size attached with
          | none => simp [current, representative] at virtual
          | some atom =>
              simp [current, representative] at virtual
              subst child
              exact ⟨atom, by simp⟩

/-- Every canonical child of a public official node has generated provenance. -/
theorem aromaticCanonicalOfficialCIPChildrenAt_generated
    (source : SemanticMolecule) (size : Nat)
    {node child : OfficialCIPNode (Fin size)}
    (present : child ∈ source.aromaticCanonicalOfficialCIPChildrenAt size node) :
    OfficialCIPNodeProvenanceGenerated child.provenance := by
  by_cases duplicate : node.isDuplicateLeaf = true
  · simp [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt, duplicate] at present
  · unfold SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt at present
    rw [if_neg duplicate] at present
    dsimp only at present
    rcases List.mem_append.mp present with ordinary | virtual
    · rcases List.mem_map.mp ordinary with ⟨copy, _copyPresent, rfl⟩
      rcases copy with ⟨next, copyIndex⟩
      simp only [OfficialCIPNode.extend_provenance, OfficialCIPNode.childProvenance]
      by_cases positive : copyIndex = 0
      · subst copyIndex
        by_cases visited : next ∈ node.history
        · simp [visited, OfficialCIPNodeProvenanceGenerated]
        · simp [visited, OfficialCIPNodeProvenanceGenerated]
      · simp [positive, OfficialCIPNodeProvenanceGenerated]
    · cases current : node.current? with
      | none => simp [current] at virtual
      | some attached =>
          cases representative :
              source.aromaticCanonicalMancudeRepresentativeAt? size attached with
          | none => simp [current, representative] at virtual
          | some atom =>
              simp [current, representative] at virtual
              subst child
              simp [OfficialCIPNode.extendMancudeDuplicate,
                OfficialCIPNodeProvenanceGenerated]

/-- Declarative derivations preserve generated provenance. -/
theorem declarativeAromaticCanonicalOccurrenceSubtree_generated
    (source : AuthoritativeChemicalInput)
    {root : source.AromaticCanonicalAtom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {occurrence : source.AromaticCanonicalOccurrenceFrame}
    (derived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node occurrence)
    (nodeGenerated : OfficialCIPNodeProvenanceGenerated node.provenance) :
    OfficialCIPNodeProvenanceGenerated occurrence.node.provenance := by
  induction derived with
  | subtreeRoot => exact nodeGenerated
  | subtreeDescendant childAtSlot descendant inductionHypothesis =>
      exact inductionHypothesis
        (aromaticCanonicalOfficialCIPChildrenAt_generated
          source.molecule source.molecule.atomCount
          (List.fst_mem_of_mem_zipIdx childAtSlot))

/-- Every carrier occurrence node has generated provenance. -/
theorem aromaticCanonicalOccurrence_node_provenance_generated
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (occurrence : source.AromaticCanonicalOccurrence fuel) :
    OfficialCIPNodeProvenanceGenerated occurrence.1.node.provenance :=
  source.declarativeAromaticCanonicalOccurrenceSubtree_generated
    ((source.mem_aromaticCanonicalOccurrences_iff fuel occurrence.1).mp occurrence.2)
    officialCIPNodeProvenanceGenerated_realAtom

/-! ## Availability of the two actual key frames at the common fuel -/

/-- A `List.mapM` is total on a list over which every value has a successful image. -/
private theorem model_list_mapM_exists_of_forall_exists {α β : Type*}
    (f : α → Option β) :
    ∀ values : List α, (∀ value ∈ values, ∃ result, f value = some result) →
      ∃ results, values.mapM f = some results
  | [], _ => ⟨[], rfl⟩
  | value :: values, complete => by
      obtain ⟨result, resultComputed⟩ := complete value (by simp)
      obtain ⟨results, resultsComputed⟩ :=
        model_list_mapM_exists_of_forall_exists f values
          (fun member present => complete member (by simp [present]))
      exact ⟨result :: results, by
        rw [List.mapM_cons, resultComputed]
        simp [resultsComputed]⟩

/-- The compound half of a successful frame is exactly the actual `mapM` result. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule45Keys
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel}
    {fuel : Nat}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      read fuel cursors = some frame) :
    cursors.mapM
        (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead? read fuel) =
      some frame.rule45Keys := by
  unfold buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead? at computed
  cases rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel cursors with
  | none => simp [rule3Computed] at computed
  | some rule3Frame =>
      by_cases rule3Length : rule3Frame.keys.length = 4
      · cases rule45Computed : cursors.mapM
            (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead? read fuel) with
        | none => simp [rule3Computed, rule3Length, rule45Computed] at computed
        | some rule45Keys =>
            by_cases rule45Length : rule45Keys.length = 4
            · simp [rule3Computed, rule3Length, rule45Computed, rule45Length] at computed
              subst frame
              simpa using rule45Computed
            · simp [rule3Computed, rule3Length, rule45Computed, rule45Length] at computed
      · simp [rule3Computed, rule3Length] at computed

/-- The compound key stored at one slot of a successful frame is produced by the actual
per-cursor builder applied to the cursor at that same slot. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_keyAt_rule45
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel}
    {fuel : Nat}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      read fuel cursors = some frame)
    (cursorsLength : cursors.length = 4) (index : Fin 4) :
    ∃ key,
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead? read fuel
          (cursors.get (Fin.cast cursorsLength.symm index)) = some key ∧
        (frame.keyAt index).rule45 = key := by
  have mapComputed :=
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule45Keys
      computed
  let keyIndex : Fin frame.rule45Keys.length :=
    Fin.cast frame.rule45Length.symm index
  let cursorIndex : Fin cursors.length :=
    Fin.cast cursorsLength.symm index
  have keyIndexBound : keyIndex.val < cursors.length := by
    have valueEq : keyIndex.val = index.val := rfl
    rw [valueEq, cursorsLength]
    exact index.isLt
  have getComputed :=
    model_list_mapM_get_some
      (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead? read fuel)
      cursors frame.rule45Keys mapComputed keyIndex.val keyIndexBound keyIndex.isLt
  refine ⟨frame.rule45Keys.get keyIndex, ?_, rfl⟩
  simpa [keyIndex, cursorIndex] using getComputed

/-- The shipped restricted builder's Rule-3 component is the actual reader-free Rule-3
computation. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_rule3Frame_computed
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {target : source.AromaticCanonicalOccurrence carrierFuel}
    {view : source.AromaticCanonicalDependencyView target}
    {fuel : Nat}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view fuel cursors = some frame) :
    source.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel cursors =
      some frame.rule3Frame := by
  unfold buildAromaticCanonicalOccurrenceRule3Through5KeyFrame? at computed
  cases rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel cursors with
  | none => simp [rule3Computed] at computed
  | some rule3Frame =>
      by_cases rule3Length : rule3Frame.keys.length = 4
      · cases rule45Computed : cursors.mapM
            (source.buildAromaticCanonicalRerootCompoundRule45Key? target view fuel) with
        | none => simp [rule3Computed, rule3Length, rule45Computed] at computed
        | some rule45Keys =>
            by_cases rule45Length : rule45Keys.length = 4
            · simp [rule3Computed, rule3Length, rule45Computed, rule45Length] at computed
              subst frame
              simpa using rule3Computed
            · simp [rule3Computed, rule3Length, rule45Computed, rule45Length] at computed
      · simp [rule3Computed, rule3Length] at computed

/-- The declarative Rule-3 spatial key list is pointwise related to its cursors. -/
private theorem model_declarativeRule3SpatialKeyExceptList_forall2
    {source : AuthoritativeChemicalInput} {carrierFuel fuel : Nat}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList
      excluded fuel cursors keys) :
    List.Forall₂
      (source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept excluded fuel)
      cursors keys :=
  match derived with
  | .nil _ => .nil
  | .cons head tail => .cons head
      (model_declarativeRule3SpatialKeyExceptList_forall2 tail)

/-- Every declarative Rule-3 spatial key starts with the addressed root node of its cursor. -/
theorem model_declarativeRule3SpatialKeyExcept_sourceNodes_head
    {source : AuthoritativeChemicalInput} {carrierFuel fuel : Nat}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {key : source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept
      excluded fuel cursor key) :
    key.constitutional.sourceNodes.head? = some [([], cursor.occurrence.1.node)] := by
  cases derived <;> rfl

/-- At a successful build every Rule-3 key slot starts with its actual cursor node. -/
theorem model_buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_keyAt_rule3_sourceNodes_head
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel}
    {fuel : Nat}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      read fuel cursors = some frame)
    (cursorsLength : cursors.length = 4) (index : Fin 4) :
    (frame.keyAt index).rule3.constitutional.sourceNodes.head? =
      some [([], (cursors.get (Fin.cast cursorsLength.symm index)).occurrence.1.node)] := by
  have declarative :=
    (source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule3Frame_sound
      read fuel cursors frame computed).2.2.2
  have pointwise := model_declarativeRule3SpatialKeyExceptList_forall2 declarative
  have derived := pointwise.get (i := index.val)
    (by rw [cursorsLength]; exact index.isLt)
    (by rw [frame.rule3Length]; exact index.isLt)
  exact model_declarativeRule3SpatialKeyExcept_sourceNodes_head derived





theorem exists_buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_at_twice_of_rule3Frame
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rule3Frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
      (2 * (carrierFuel + 1)) cursors = some rule3Frame)
    (cursorsLength : cursors.length = 4)
    (valid : ∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ frame,
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
        read (2 * (carrierFuel + 1)) cursors = some frame := by
  have declarative := source.buildAromaticCanonicalRule3CanonicalKeyFrame?_sound
    (2 * (carrierFuel + 1)) cursors rule3Frame rule3Computed
  have pointwise :=
    model_declarativeRule3SpatialKeyExceptList_forall2 declarative.2.2.2
  have rule3Length : rule3Frame.keys.length = 4 := by
    rw [← pointwise.length_eq, cursorsLength]
  have keysExist : ∀ cursor ∈ cursors, ∃ key,
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        read (2 * (carrierFuel + 1)) cursor = some key :=
    fun cursor present =>
      source.exists_buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_at_twice
        read cursor (valid cursor present)
  obtain ⟨keys, keysComputed⟩ := model_list_mapM_exists_of_forall_exists
    (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read (2 * (carrierFuel + 1))) cursors keysExist
  have keysLength : keys.length = 4 := by
    rw [model_list_mapM_length_eq
      (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        read (2 * (carrierFuel + 1))) cursors keys keysComputed, cursorsLength]
  refine ⟨{ rule3Frame := rule3Frame
            rule3Length := rule3Length
            rule45Keys := keys
            rule45Length := keysLength }, ?_⟩
  simp [buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?,
    rule3Computed, rule3Length, keysComputed, keysLength]

/-- **Restricted frame availability.**  The shipped restricted builder succeeds at the same common
fuel, with the same derived Rule-3 frame. -/
theorem exists_buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_at_twice_of_rule3Frame
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rule3Frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
      (2 * (carrierFuel + 1)) cursors = some rule3Frame)
    (cursorsLength : cursors.length = 4)
    (valid : ∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ frame,
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        target view (2 * (carrierFuel + 1)) cursors = some frame := by
  obtain ⟨frame, computed⟩ :=
    source.exists_buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_at_twice_of_rule3Frame
      (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
      cursors rule3Frame rule3Computed cursorsLength valid
  refine ⟨frame, ?_⟩
  rw [← source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_eq_rule3Through5KeyFrame?
    target view]
  exact computed

/-! ## Actual four-ligand frame geometry -/

/-- Every cursor of an actual four-ligand frame is a valid reroot cursor. -/
theorem aromaticCanonicalOccurrenceFourLigandFrame_roots_valid_model
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some frame) :
    ∀ cursor ∈ frame.roots, source.AromaticCanonicalRerootCursorValid cursor := by
  intro cursor present
  obtain ⟨declared, _⟩ :=
    source.aromaticCanonicalOccurrenceFourLigandFrame?_sound target frame computed
  obtain ⟨mapped, previous⟩ := declared
  have intended : cursor.occurrence.1 ∈
      source.intendedAromaticCanonicalRerootChildFrames
        { occurrence := target, previous? := none } := by
    rw [← mapped]
    exact List.mem_map_of_mem (f := fun child => child.occurrence.1) present
  have neighbor := source.mem_aromaticCanonicalRerootNeighborFrames_of_mem_intended
    { occurrence := target, previous? := none } cursor.occurrence.1 intended
  have previousEq := previous cursor present
  unfold AromaticCanonicalRerootCursorValid
  rw [previousEq]
  simpa using neighbor

/-- Every four-ligand slot is adjacent in the actual carrier tree to the target. -/
theorem aromaticCanonicalOccurrenceFourLigandFrame_cursorAt_adjacent
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some frame)
    (index : Fin 4) :
    (frame.cursorAt index).occurrence.1 ∈
        source.aromaticCanonicalOccurrences carrierFuel ∧
      source.AromaticCanonicalCarrierTreeAdjacent
        (frame.cursorAt index).occurrence.1 target.1 := by
  obtain ⟨declared, _⟩ :=
    source.aromaticCanonicalOccurrenceFourLigandFrame?_sound target frame computed
  obtain ⟨mapped, previous⟩ := declared
  have present : frame.cursorAt index ∈ frame.roots := List.get_mem _ _
  have intended : (frame.cursorAt index).occurrence.1 ∈
      source.intendedAromaticCanonicalRerootChildFrames
        { occurrence := target, previous? := none } := by
    rw [← mapped]
    exact List.mem_map_of_mem (f := fun child => child.occurrence.1) present
  have neighbor := source.mem_aromaticCanonicalRerootNeighborFrames_of_mem_intended
    { occurrence := target, previous? := none }
    (frame.cursorAt index).occurrence.1 intended
  exact (source.mem_aromaticCanonicalRerootNeighborFrames_iff
    target.1 (frame.cursorAt index).occurrence.1).mp neighbor

/-- Every four-ligand slot stores the same atom root as the target. -/
theorem aromaticCanonicalOccurrenceFourLigandFrame_cursorAt_root
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some frame)
    (index : Fin 4) :
    (frame.cursorAt index).occurrence.1.root = target.1.root :=
  (source.aromaticCanonicalOccurrenceFourLigandFrame_cursorAt_adjacent
    target frame computed index).2.1

/-- Every four-ligand cursor records the target as its incoming coordinate. -/
theorem aromaticCanonicalOccurrenceFourLigandFrame_cursorAt_previous
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some frame)
    (index : Fin 4) :
    (frame.cursorAt index).previous? = some target := by
  obtain ⟨declared, _⟩ :=
    source.aromaticCanonicalOccurrenceFourLigandFrame?_sound target frame computed
  exact declared.2 (frame.cursorAt index) (List.get_mem _ _)

/-- **Actual slot classification.**  Every four-ligand slot address is either the actual parent
address `target.address.dropLast` or an outward child address strictly below the target. -/
theorem aromaticCanonicalOccurrenceFourLigandFrame_slot_address_classification
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some frame)
    (index : Fin 4) :
    ((frame.cursorAt index).occurrence.1.address.length + 1 = target.1.address.length ∧
        (frame.cursorAt index).occurrence.1.address = target.1.address.dropLast) ∨
      (target.1.address.length + 1 =
          (frame.cursorAt index).occurrence.1.address.length ∧
        target.1.address = (frame.cursorAt index).occurrence.1.address.dropLast) := by
  have adjacent :=
    (source.aromaticCanonicalOccurrenceFourLigandFrame_cursorAt_adjacent
      target frame computed index).2
  exact adjacent.2

/-- **Parent-slot uniqueness.**  At most one actual four-ligand slot can be the parent address.
The proof uses the actual carrier functionality at a fixed root-relative address and the actual
`Nodup`ness of the executable zipper expansion; it assumes neither parent realness nor any desired
pair comparison. -/
theorem aromaticCanonicalOccurrenceFourLigandFrame_parent_slot_unique
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some frame)
    {left right : Fin 4}
    (leftParent : (frame.cursorAt left).occurrence.1.address.length + 1 =
      target.1.address.length)
    (rightParent : (frame.cursorAt right).occurrence.1.address.length + 1 =
      target.1.address.length) :
    left = right := by
  have leftAddress : (frame.cursorAt left).occurrence.1.address =
      target.1.address.dropLast := by
    rcases source.aromaticCanonicalOccurrenceFourLigandFrame_slot_address_classification
      target frame computed left with parent | outward
    · exact parent.2
    · omega
  have rightAddress : (frame.cursorAt right).occurrence.1.address =
      target.1.address.dropLast := by
    rcases source.aromaticCanonicalOccurrenceFourLigandFrame_slot_address_classification
      target frame computed right with parent | outward
    · exact parent.2
    · omega
  have leftDerived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      target.1.root [] (carrierFuel + 1) (OfficialCIPNode.root target.1.root)
      (frame.cursorAt left).occurrence.1 := by
    have derived :=
      (source.mem_aromaticCanonicalOccurrences_iff carrierFuel
        (frame.cursorAt left).occurrence.1).mp (frame.cursorAt left).occurrence.2
    rw [DeclarativeAromaticCanonicalOccurrence,
      DeclarativeAromaticCanonicalOccurrenceAtAtom] at derived
    rw [source.aromaticCanonicalOccurrenceFourLigandFrame_cursorAt_root
      target frame computed left] at derived
    exact derived
  have rightDerived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      target.1.root [] (carrierFuel + 1) (OfficialCIPNode.root target.1.root)
      (frame.cursorAt right).occurrence.1 := by
    have derived :=
      (source.mem_aromaticCanonicalOccurrences_iff carrierFuel
        (frame.cursorAt right).occurrence.1).mp (frame.cursorAt right).occurrence.2
    rw [DeclarativeAromaticCanonicalOccurrence,
      DeclarativeAromaticCanonicalOccurrenceAtAtom] at derived
    rw [source.aromaticCanonicalOccurrenceFourLigandFrame_cursorAt_root
      target frame computed right] at derived
    exact derived
  have frameEq : (frame.cursorAt left).occurrence.1 =
      (frame.cursorAt right).occurrence.1 :=
    source.declarativeAromaticCanonicalOccurrenceSubtree_functional_at_address
      leftDerived rightDerived (leftAddress.trans rightAddress.symm)
  have occurrenceEq : (frame.cursorAt left).occurrence =
      (frame.cursorAt right).occurrence := Subtype.ext frameEq
  have cursorEq : frame.cursorAt left = frame.cursorAt right := by
    apply AromaticCanonicalRerootCursor.ext
    · exact occurrenceEq
    · rw [source.aromaticCanonicalOccurrenceFourLigandFrame_cursorAt_previous
          target frame computed left,
        source.aromaticCanonicalOccurrenceFourLigandFrame_cursorAt_previous
          target frame computed right]
  have rootsNodup : frame.roots.Nodup := by
    rw [source.aromaticCanonicalOccurrenceFourLigandFrame?_roots_eq_rerootChildren
      target frame computed]
    exact source.aromaticCanonicalRerootChildren_nodup _
  have getEq : frame.roots.get (Fin.cast frame.rootsLength.symm left) =
      frame.roots.get (Fin.cast frame.rootsLength.symm right) := cursorEq
  have indexEq := (List.Nodup.get_inj_iff rootsNodup).mp getEq
  exact Fin.ext (by simpa using congrArg Fin.val indexEq)

/-! ## Actual parent/outward Rule-3 strictness -/

/-- **Parent/outward strict Rule-3 separation at an actual frame.**  For a frame built from the
actual four-ligand roots, a slot at the parent address and a slot at an outward child address are
already strictly decided by the reader-free Rule-3 comparison: the actual total original-root
Rule-1b distances differ, because the parent is a real occurrence at the shortened target address
while every generated child kind, including duplicates, has a different distance.  No compound key
and no reader is consulted. -/
theorem aromaticCanonicalOccurrenceFourLigandFrame_rule3_ne_of_parent_outward
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some base)
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (frameComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      read fuel base.roots = some frame)
    (parentSlot outwardSlot : Fin 4)
    (parentLength :
      (base.cursorAt parentSlot).occurrence.1.address.length + 1 =
        target.1.address.length)
    (outwardLength :
      target.1.address.length + 1 =
        (base.cursorAt outwardSlot).occurrence.1.address.length) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (frame.keyAt parentSlot).rule3 (frame.keyAt outwardSlot).rule3 ≠ Ordering.eq := by
  have distinct : parentSlot ≠ outwardSlot := by
    intro same
    rw [same] at parentLength
    omega
  obtain ⟨pair, pairParent, pairOutward⟩ :=
    source.exists_aromaticCanonicalParentOutwardLigandPair_ofFrame
      target base baseComputed parentSlot outwardSlot distinct parentLength outwardLength
  have different :
      (base.cursorAt parentSlot).occurrence.1.node.rule1bRootDistance ≠
        (base.cursorAt outwardSlot).occurrence.1.node.rule1bRootDistance := by
    have separated :=
      AromaticCanonicalParentOutwardLigandPair.rule1bRootDistance_ne source pair
    simpa [AromaticCanonicalParentOutwardLigandPair.parentCursor,
      AromaticCanonicalParentOutwardLigandPair.outwardCursor, pairParent, pairOutward]
      using separated
  have parentHead :=
    source.model_buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_keyAt_rule3_sourceNodes_head
      frameComputed base.rootsLength parentSlot
  have outwardHead :=
    source.model_buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_keyAt_rule3_sourceNodes_head
      frameComputed base.rootsLength outwardSlot
  exact source.compareAromaticCanonicalUncancelledRule3SpatialKeys_ne_eq_of_sourceNodes_head_distances
    parentHead outwardHead different

/-! ## Discharge of the tie seam from actual slot classification -/

/-- **The tie seam holds for the two actual frames.**  For the whole-state frame and the shipped
restricted frame built at one fuel on the same actual four-ligand roots, the compound through-Rule-5
comparison records agree on every pair that the shared reader-free Rule-3 comparison leaves tied.
The two actual slots are classified by their actual addresses:

* two outward children obtain whole-`Option` equality of their compound computations from the
  shipped whole-state key agreement;
* two parent slots coincide by actual parent-slot uniqueness, so the comparison is the actual
  diagonal record `{ordering := eq, pseudo := false}` on both frames;
* a parent/outward pair (in either order) cannot be tied at all, because the actual Rule-1b
  root distances differ and Rule 3 therefore already decides. -/
theorem aromaticCanonicalOccurrenceFourLigandFrame_wholeState_ties
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some base)
    (wholeFrame restrictedFrame :
      source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (wholeComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      (source.aromaticCanonicalWholeStateReader state) fuel base.roots = some wholeFrame)
    (restrictedComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      (fun cursor => source.aromaticCanonicalDependencyLabel target
        (source.aromaticCanonicalDependencyView state target) cursor)
      fuel base.roots = some restrictedFrame)
    (leftIndex rightIndex : Fin 4)
    (tie : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (wholeFrame.keyAt leftIndex).rule3 (wholeFrame.keyAt rightIndex).rule3 =
        Ordering.eq) :
    source.compareAromaticCanonicalRerootCompoundThroughRule5
        (wholeFrame.keyAt leftIndex).rule45 (wholeFrame.keyAt rightIndex).rule45 =
      source.compareAromaticCanonicalRerootCompoundThroughRule5
        (restrictedFrame.keyAt leftIndex).rule45
        (restrictedFrame.keyAt rightIndex).rule45 := by
  obtain ⟨wholeLeftKey, wholeLeftComputed, wholeLeftEq⟩ :=
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_keyAt_rule45
      wholeComputed base.rootsLength leftIndex
  obtain ⟨wholeRightKey, wholeRightComputed, wholeRightEq⟩ :=
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_keyAt_rule45
      wholeComputed base.rootsLength rightIndex
  obtain ⟨restrictedLeftKey, restrictedLeftComputed, restrictedLeftEq⟩ :=
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_keyAt_rule45
      restrictedComputed base.rootsLength leftIndex
  obtain ⟨restrictedRightKey, restrictedRightComputed, restrictedRightEq⟩ :=
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_keyAt_rule45
      restrictedComputed base.rootsLength rightIndex
  have leftClass :=
    source.aromaticCanonicalOccurrenceFourLigandFrame_slot_address_classification
      target base baseComputed leftIndex
  have rightClass :=
    source.aromaticCanonicalOccurrenceFourLigandFrame_slot_address_classification
      target base baseComputed rightIndex
  by_cases leftParent :
      (base.cursorAt leftIndex).occurrence.1.address.length + 1 =
        target.1.address.length
  · by_cases rightParent :
        (base.cursorAt rightIndex).occurrence.1.address.length + 1 =
          target.1.address.length
    · -- Both slots sit at the actual parent address, hence they are the same slot.
      have indexEq : leftIndex = rightIndex :=
        source.aromaticCanonicalOccurrenceFourLigandFrame_parent_slot_unique
          target base baseComputed leftParent rightParent
      subst rightIndex
      rw [source.compareAromaticCanonicalRerootCompoundThroughRule5_self,
        source.compareAromaticCanonicalRerootCompoundThroughRule5_self]
    · -- Parent on the left, outward child on the right: Rule 3 already decides.
      have rightOutward :
          target.1.address.length + 1 =
            (base.cursorAt rightIndex).occurrence.1.address.length := by
        rcases rightClass with parent | outward
        · omega
        · exact outward.1
      exact absurd tie
        (source.aromaticCanonicalOccurrenceFourLigandFrame_rule3_ne_of_parent_outward
          (source.aromaticCanonicalWholeStateReader state) target base baseComputed
          wholeFrame wholeComputed leftIndex rightIndex leftParent rightOutward)
  · -- The left slot is outward.
    have leftOutward :
        target.1.address.length + 1 =
          (base.cursorAt leftIndex).occurrence.1.address.length := by
      rcases leftClass with parent | outward
      · omega
      · exact outward.1
    by_cases rightParent :
        (base.cursorAt rightIndex).occurrence.1.address.length + 1 =
          target.1.address.length
    · -- Outward child on the left, parent on the right: Rule 3 already decides, in the
      -- reverse orientation.  Swap the tie with the oriented-comparator law.
      have strict :=
        source.aromaticCanonicalOccurrenceFourLigandFrame_rule3_ne_of_parent_outward
          (source.aromaticCanonicalWholeStateReader state) target base baseComputed
          wholeFrame wholeComputed rightIndex leftIndex rightParent leftOutward
      have tieReversed :
          source.compareAromaticCanonicalUncancelledRule3SpatialKeys
            (wholeFrame.keyAt rightIndex).rule3 (wholeFrame.keyAt leftIndex).rule3 =
              Ordering.eq := by
        letI : Std.TransCmp
            source.compareAromaticCanonicalUncancelledRule3SpatialKeys :=
          source.compareAromaticCanonicalUncancelledRule3SpatialKeys_transCmp
        rw [Std.OrientedCmp.eq_swap
          (cmp := source.compareAromaticCanonicalUncancelledRule3SpatialKeys)
          (a := (wholeFrame.keyAt rightIndex).rule3)
          (b := (wholeFrame.keyAt leftIndex).rule3), tie]
        rfl
      exact absurd tieReversed strict
    · -- Both slots are outward: the shipped whole-state key agreement applies slotwise.
      have leftPresent : base.cursorAt leftIndex ∈ base.roots := List.get_mem _ _
      have rightPresent : base.cursorAt rightIndex ∈ base.roots := List.get_mem _ _
      have leftKeyEq : wholeLeftKey = restrictedLeftKey := by
        apply Option.some.inj
        rw [← wholeLeftComputed, ← restrictedLeftComputed]
        exact
          source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_dependencyLabel_of_ligandRoot
            target state fuel (base.cursorAt leftIndex)
            (source.aromaticCanonicalOccurrenceFourLigandFrame?_roots_mem_rerootChildren
              target base baseComputed (base.cursorAt leftIndex) leftPresent)
            (by omega)
      have rightKeyEq : wholeRightKey = restrictedRightKey := by
        apply Option.some.inj
        rw [← wholeRightComputed, ← restrictedRightComputed]
        exact
          source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_dependencyLabel_of_ligandRoot
            target state fuel (base.cursorAt rightIndex)
            (source.aromaticCanonicalOccurrenceFourLigandFrame?_roots_mem_rerootChildren
              target base baseComputed (base.cursorAt rightIndex) rightPresent)
            (by omega)
      rw [wholeLeftEq, wholeRightEq, restrictedLeftEq, restrictedRightEq,
        leftKeyEq, rightKeyEq]

/-! ## Unconditional whole-state descriptor equality for every target -/










theorem aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel) :
    source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
        (source.aromaticCanonicalWholeStateReader state) target
        (2 * (carrierFuel + 1)) =
      source.aromaticCanonicalOccurrenceRule3Through5Descriptor?
        target (source.aromaticCanonicalDependencyView state target)
        (2 * (carrierFuel + 1)) := by
  cases baseComputed : source.aromaticCanonicalOccurrenceFourLigandFrame? target with
  | none =>
      unfold aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
        aromaticCanonicalOccurrenceRule3Through5Descriptor?
        aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?
        aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
      rw [baseComputed]
      simp
  | some base =>
      cases rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
          (2 * (carrierFuel + 1)) base.roots with
      | none =>
          unfold aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
            aromaticCanonicalOccurrenceRule3Through5Descriptor?
            aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?
            aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
          rw [baseComputed]
          simp [rule3Computed, buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?,
            buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?]
      | some rule3Frame =>
          by_cases rule3Length : rule3Frame.keys.length = 4
          · obtain ⟨wholeFrame, wholeComputed⟩ :=
              source.exists_buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_at_twice_of_rule3Frame
                (source.aromaticCanonicalWholeStateReader state) base.roots rule3Frame
                rule3Computed base.rootsLength
                (source.aromaticCanonicalOccurrenceFourLigandFrame_roots_valid_model
                  target base baseComputed)
            obtain ⟨restrictedFrame, restrictedComputed⟩ :=
              source.exists_buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_at_twice_of_rule3Frame
                target (source.aromaticCanonicalDependencyView state target) base.roots
                rule3Frame rule3Computed base.rootsLength
                (source.aromaticCanonicalOccurrenceFourLigandFrame_roots_valid_model
                  target base baseComputed)
            have restrictedWithRead :
                source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
                  (fun cursor => source.aromaticCanonicalDependencyLabel target
                    (source.aromaticCanonicalDependencyView state target) cursor)
                  (2 * (carrierFuel + 1)) base.roots = some restrictedFrame := by
              rw [source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_eq_rule3Through5KeyFrame?
                target (source.aromaticCanonicalDependencyView state target)]
              exact restrictedComputed
            exact
              source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_of_keyFrameTieSeam
                target state (2 * (carrierFuel + 1)) base baseComputed
                wholeFrame restrictedFrame wholeComputed restrictedComputed
                (AromaticCanonicalOccurrenceRule3Through5FrameTieSeam.of_computations
                  source (source.aromaticCanonicalWholeStateReader state) target
                  (source.aromaticCanonicalDependencyView state target)
                  (2 * (carrierFuel + 1)) base.roots wholeFrame restrictedFrame
                  wholeComputed restrictedComputed
                  (source.aromaticCanonicalOccurrenceFourLigandFrame_wholeState_ties
                    target state base baseComputed wholeFrame restrictedFrame
                    wholeComputed restrictedWithRead))
          · unfold aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
              aromaticCanonicalOccurrenceRule3Through5Descriptor?
              aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?
              aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
            rw [baseComputed]
            simp [rule3Computed, rule3Length,
              buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?,
              buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?]

/-- Outcome form of the unconditional descriptor equality: both descriptors accept exactly the
same labels at the common fuel, for every target. -/
theorem aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_some_iff_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (descriptor : AromaticCanonicalAuxiliaryLabel) :
    source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
        (source.aromaticCanonicalWholeStateReader state) target
        (2 * (carrierFuel + 1)) = some descriptor ↔
      source.aromaticCanonicalOccurrenceRule3Through5Descriptor?
        target (source.aromaticCanonicalDependencyView state target)
        (2 * (carrierFuel + 1)) = some descriptor := by
  rw [source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_at_twice
    target state]

/-- Success/failure form of the unconditional descriptor equality: the two descriptors are
defined exactly together, so every fail-closed `none` outcome coincides. -/
theorem aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_isSome_eq_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel) :
    (source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
        (source.aromaticCanonicalWholeStateReader state) target
        (2 * (carrierFuel + 1))).isSome =
      (source.aromaticCanonicalOccurrenceRule3Through5Descriptor?
        target (source.aromaticCanonicalDependencyView state target)
        (2 * (carrierFuel + 1))).isSome := by
  rw [source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_at_twice
    target state]

/-! ## Lift to the existing public unique model -/

/-- **Model locality at the common fuel for every target.**  In the existing public unique
Rule-3--5 model at rule fuel `2 * (carrierFuel + 1)`, the stored label at **every**
source-canonical occurrence target is exactly the whole-state descriptor computed there.  This
composes the actual descriptor equality with the existing canonical model characterization; it
introduces no second model wrapper and no additional semantics. -/
theorem aromaticCanonicalOccurrenceRule3Through5Model_eq_descriptorWithRead?_of_wholeState
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel (2 * (carrierFuel + 1)))).CIPModel state)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    state target =
      source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
        (source.aromaticCanonicalWholeStateReader state) target
        (2 * (carrierFuel + 1)) := by
  let view := source.aromaticCanonicalDependencyView state target
  have locality :=
    source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_at_twice
      target state
  have modelIff : ∀ descriptor,
      state target = some descriptor ↔
        source.aromaticCanonicalOccurrenceRule3Through5Descriptor? target view
          (2 * (carrierFuel + 1)) = some descriptor := by
    intro descriptor
    rw [source.aromaticCanonicalOccurrenceRule3Through5Model_eq_some_iff_canonical
      state model target descriptor]
    exact (source.aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
      target view (2 * (carrierFuel + 1)) descriptor).symm
  rw [locality]
  cases restricted : source.aromaticCanonicalOccurrenceRule3Through5Descriptor? target view
      (2 * (carrierFuel + 1)) with
  | none =>
      cases stored : state target with
      | none => rfl
      | some descriptor =>
          have accepted := (modelIff descriptor).mp stored
          rw [restricted] at accepted
          cases accepted
  | some descriptor => exact (modelIff descriptor).mpr restricted

/-- Outcome form of the model locality: for every target the model stores exactly the whole-state
descriptor's label, with the same success/failure behaviour. -/
theorem aromaticCanonicalOccurrenceRule3Through5Model_eq_some_iff_of_wholeState
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel (2 * (carrierFuel + 1)))).CIPModel state)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (descriptor : AromaticCanonicalAuxiliaryLabel) :
    state target = some descriptor ↔
      source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
        (source.aromaticCanonicalWholeStateReader state) target
        (2 * (carrierFuel + 1)) = some descriptor := by
  rw [source.aromaticCanonicalOccurrenceRule3Through5Model_eq_descriptorWithRead?_of_wholeState
    state model target]

/-- **Instantiation of the existing public existence/uniqueness theorem.**  At the common fuel the
shipped unique Rule-3--5 model is exactly the whole-state descriptor evaluator, pointwise for every
target.  This repackages the shipped `existsUnique_aromaticCanonicalOccurrenceRule3Through5Model`
with the descriptor equality; it is not a second fixed-point theorem and introduces no new
semantics. -/
theorem existsUnique_aromaticCanonicalOccurrenceRule3Through5Model_wholeState
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) :
    ∃! state : source.AromaticCanonicalAuxiliaryState carrierFuel,
      (source.aromaticCanonicalOccurrenceSystem
        (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
          carrierFuel (2 * (carrierFuel + 1)))).CIPModel state ∧
      ∀ target : source.AromaticCanonicalOccurrence carrierFuel,
        state target =
          source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
            (source.aromaticCanonicalWholeStateReader state) target
            (2 * (carrierFuel + 1)) := by
  obtain ⟨state, model, unique⟩ :=
    source.existsUnique_aromaticCanonicalOccurrenceRule3Through5Model
      carrierFuel (2 * (carrierFuel + 1))
  refine ⟨state, ⟨model, fun target =>
    source.aromaticCanonicalOccurrenceRule3Through5Model_eq_descriptorWithRead?_of_wholeState
      state model target⟩, ?_⟩
  intro other otherBoth
  exact unique other otherBoth.1

end AuthoritativeChemicalInput
end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalOccurrenceRule3Through5FrameTieSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.OfficialCIPNodeProvenanceGenerated
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.officialCIPNodeProvenanceGenerated_realAtom
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.officialCIPNodeProvenanceGenerated_eq_realAtom_of_not_duplicateLeaf
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOfficialCIPChildrenAt_history
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOfficialCIPChildrenAt_generated
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.declarativeAromaticCanonicalOccurrenceSubtree_generated
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrence_node_provenance_generated
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRerootCompoundRule5Readings_self
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRerootCompoundRule4bcKeys_self
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalRerootCompoundThroughRule5_self
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.declarativeAromaticCanonicalOccurrenceSubtree_addressPrefix
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.declarativeAromaticCanonicalOccurrenceSubtree_eq_root_of_address_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.declarativeAromaticCanonicalOccurrenceSubtree_functional_at_address
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.declarativeAromaticCanonicalOccurrenceSubtree_immediate_child
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule45Keys
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_keyAt_rule45
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_rule3Frame_computed
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.model_declarativeRule3SpatialKeyExcept_sourceNodes_head
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.model_buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_keyAt_rule3_sourceNodes_head
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_at_twice_of_rule3Frame
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_at_twice_of_rule3Frame
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceFourLigandFrame_roots_valid_model
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceFourLigandFrame_cursorAt_adjacent
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceFourLigandFrame_cursorAt_root
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceFourLigandFrame_cursorAt_previous
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceFourLigandFrame_slot_address_classification
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceFourLigandFrame_parent_slot_unique
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceFourLigandFrame_rule3_ne_of_parent_outward
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceFourLigandFrame_wholeState_ties
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_at_twice
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5Model_eq_descriptorWithRead?_of_wholeState
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_some_iff_at_twice
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_isSome_eq_at_twice
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5Model_eq_some_iff_of_wholeState
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.existsUnique_aromaticCanonicalOccurrenceRule3Through5Model_wholeState

/-! Guards for the imported actual parent API and the predecessor transport interfaces used by the
proof above. -/
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_aromaticCanonicalParentOutwardLigandPair_ofFrame
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalParentOutwardLigandPair.rule1bRootDistance_ne
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalUncancelledRule3SpatialKeys_ne_eq_of_sourceNodes_head_distances
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_keyAt_rule3_sourceNodes_head
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_dependencyLabel_of_ligandRoot
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceFourLigandFrame?_roots_mem_rerootChildren
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_of_keyFrameTieSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalOccurrenceRule3Through5FrameTieSeam.of_computations
