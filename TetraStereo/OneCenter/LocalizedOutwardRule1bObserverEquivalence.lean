import TetraStereo.OneCenter.OfficialRuleMajorObservation
import TetraStereo.OneCenter.LocalizedOccurrenceRerootFrame
import TetraStereo.OneCenter.AuthoritativeLocalizedRule1bConformance
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

universe u























namespace TetraStereo.OneCenter.OutwardRule1bObserverEquivalence

open TetraStereo.OneCenter
open OfficialCIPNode OfficialCIPNodeProvenance OfficialRuleMajorKey MoleculeGraph
open CertifiedLocalizedCIPInput

/-- Root-first history index of an atom already stored on the branch. -/
theorem duplicateRootDistance_eq_firstIndex
    {V : Type*} [DecidableEq V] (node : OfficialCIPNode V) (atom : V)
    (present : atom ∈ node.history) :
    ∃ i, firstIndexOf? atom node.history.reverse = some i ∧
      node.duplicateRootDistance atom = i ∧
      i < node.history.length ∧
      node.history.reverse[i]? = some atom := by
  have inReverse : atom ∈ node.history.reverse := by
    simpa [List.mem_reverse] using present
  have helper : ∀ (target : V) (values : List V), target ∈ values →
      ∃ i, firstIndexOf? target values = some i ∧ i < values.length ∧
        values[i]? = some target := by
    intro target values
    induction values with
    | nil => intro present; simp at present
    | cons value values ih =>
        intro present
        by_cases head : value = target
        · subst value
          exact ⟨0, by simp [firstIndexOf?], by simp, by simp⟩
        · have tailPresent : target ∈ values :=
            (List.mem_cons.mp present).resolve_left (Ne.symm head)
          obtain ⟨i, hi, hlt, hget⟩ := ih tailPresent
          refine ⟨i + 1, ?_, by simpa using Nat.succ_lt_succ hlt, ?_⟩
          · simp [firstIndexOf?, head, hi]
          · simpa using hget
  obtain ⟨i, hi, hlt, hget⟩ := helper atom node.history.reverse inReverse
  refine ⟨i, hi, ?_, ?_, hget⟩
  · simp [duplicateRootDistance, hi]
  · simpa [List.length_reverse] using hlt

theorem duplicateRootDistance_lt_of_mem
    {V : Type*} [DecidableEq V] (node : OfficialCIPNode V) (atom : V)
    (present : atom ∈ node.history) :
    node.duplicateRootDistance atom < node.history.length := by
  obtain ⟨_, _, hdistance, hlt, _⟩ :=
    duplicateRootDistance_eq_firstIndex node atom present
  simpa [hdistance] using hlt

theorem history_length_eq_depth_add_one
    {V : Type*} [DecidableEq V] (node : OfficialCIPNode V)
    (nonempty : node.history ≠ []) :
    node.history.length = node.depth + 1 := by
  have positive : 0 < node.history.length := List.length_pos_iff.mpr nonempty
  unfold depth
  omega

/-- An outward graph node is real, or it is a ring or multiple-bond duplicate of a strictly
earlier sphere. The history is the official path, so the depth is defined. -/
structure OutwardRanked {V : Type*} [DecidableEq V] (node : OfficialCIPNode V) : Prop where
  nonempty : node.history ≠ []
  classified :
    node.provenance = realAtom ∨
      ∃ j, (node.provenance = ringDuplicate j ∨
          node.provenance = multipleBondDuplicate j) ∧
        j < node.depth

theorem outwardRanked_root {V : Type*} [DecidableEq V] (atom : V) :
    OutwardRanked (root atom) := by
  refine ⟨?_, Or.inl rfl⟩
  dsimp [root]
  exact List.cons_ne_nil _ _

/-- Every executable child of an outward node is outward, one sphere deeper. A ring child stores
the root-first index of the repeated atom, which is strictly earlier than the child sphere. -/
theorem outwardRanked_of_executableChild
    (input : CertifiedLocalizedCIPInput)
    {parent child : OfficialCIPNode input.Atom}
    (ranked : OutwardRanked parent)
    (present : child ∈ input.executableOfficialCIPChildren parent) :
    OutwardRanked child ∧ child.depth = parent.depth + 1 := by
  by_cases duplicate : parent.isDuplicateLeaf = true
  · simp [executableOfficialCIPChildren, duplicate] at present
  · rw [executableOfficialCIPChildren, if_neg duplicate] at present
    obtain ⟨copy, _, identity⟩ := List.mem_map.mp present
    rcases copy with ⟨next, copyIndex⟩
    subst identity
    have parentLength : parent.history.length = parent.depth + 1 :=
      history_length_eq_depth_add_one parent ranked.nonempty
    have childDepth : (parent.extend next copyIndex).depth = parent.depth + 1 := by
      unfold depth
      simp only [extend_history, List.length_cons]
      omega
    refine ⟨⟨?_, ?_⟩, childDepth⟩
    · simp [extend]
    · by_cases copyZero : copyIndex = 0
      · by_cases repeated : next ∈ parent.history
        · obtain ⟨i, hi, hdistance, hlt, _⟩ :=
            duplicateRootDistance_eq_firstIndex parent next repeated
          refine Or.inr ⟨parent.duplicateRootDistance next, ?_, ?_⟩
          · exact Or.inl (by simp [copyZero, repeated])
          · rw [childDepth, ← parentLength, hdistance]
            exact hlt
        · exact Or.inl (by simp [copyZero, repeated])
      · refine Or.inr ⟨parent.depth, ?_, ?_⟩
        · exact Or.inr (by simp [copyZero])
        · rw [childDepth]
          omega

theorem executable_ring_child_ancestor
    (input : CertifiedLocalizedCIPInput)
    {parent child : OfficialCIPNode input.Atom} {j : Nat}
    (ranked : OutwardRanked parent)
    (present : child ∈ input.executableOfficialCIPChildren parent)
    (ring : child.provenance = ringDuplicate j) :
    j < child.depth ∧
      ∃ atom, child = parent.extend atom 0 ∧
        atom ∈ parent.history ∧
        parent.duplicateRootDistance atom = j ∧
        firstIndexOf? atom parent.history.reverse = some j := by
  have step := outwardRanked_of_executableChild input ranked present
  by_cases duplicate : parent.isDuplicateLeaf = true
  · simp [executableOfficialCIPChildren, duplicate] at present
  · rw [executableOfficialCIPChildren, if_neg duplicate] at present
    obtain ⟨copy, _, identity⟩ := List.mem_map.mp present
    rcases copy with ⟨next, copyIndex⟩
    subst identity
    have copyZero : copyIndex = 0 := by
      by_contra nonzero
      simp [nonzero] at ring
    subst copyZero
    have repeated : next ∈ parent.history := by
      by_contra fresh
      simp [fresh] at ring
    simp [repeated] at ring
    have distance : parent.duplicateRootDistance next = j := by
      simpa using ring
    obtain ⟨i, hi, hdistance, hlt, _⟩ :=
      duplicateRootDistance_eq_firstIndex parent next repeated
    have parentLength : parent.history.length = parent.depth + 1 :=
      history_length_eq_depth_add_one parent ranked.nonempty
    refine ⟨?_, next, rfl, repeated, distance, ?_⟩
    · rw [← distance, hdistance, step.2, ← parentLength]
      exact hlt
    · rw [← distance, hdistance]
      exact hi

/-- Real nodes read the sentinel. Duplicate and placeholder nodes keep the stored distance. -/
def hybridDuplicatePriority (sentinel : Nat) {V : Type*} (node : OfficialCIPNode V) : Nat :=
  match node.provenance with
  | realAtom => sentinel
  | multipleBondDuplicate distance => distance
  | ringDuplicate distance => distance
  | OfficialCIPNodeProvenance.placeholder _ distance => distance

@[simp] theorem hybridDuplicatePriority_real (sentinel : Nat) {V : Type*}
    (node : OfficialCIPNode V) (real : node.provenance = realAtom) :
    hybridDuplicatePriority sentinel node = sentinel := by
  simp [hybridDuplicatePriority, real]

@[simp] theorem hybridDuplicatePriority_ring (sentinel : Nat) {V : Type*}
    (node : OfficialCIPNode V) (j : Nat) (ring : node.provenance = ringDuplicate j) :
    hybridDuplicatePriority sentinel node = j := by
  simp [hybridDuplicatePriority, ring]

@[simp] theorem hybridDuplicatePriority_multiple (sentinel : Nat) {V : Type*}
    (node : OfficialCIPNode V) (j : Nat)
    (multiple : node.provenance = multipleBondDuplicate j) :
    hybridDuplicatePriority sentinel node = j := by
  simp [hybridDuplicatePriority, multiple]

private theorem compareRule1b_refl (value : Nat) :
    compareRule1b value value = Ordering.eq := by
  unfold compareRule1b compareNat
  exact Nat.compare_eq_eq.mpr rfl

private theorem compareRule1b_lt_of_gt {left right : Nat} (closer : right < left) :
    compareRule1b left right = Ordering.lt := by
  unfold compareRule1b compareNat
  exact Nat.compare_eq_lt.mpr closer

private theorem compareRule1b_gt_of_lt {left right : Nat} (closer : left < right) :
    compareRule1b left right = Ordering.gt := by
  unfold compareRule1b compareNat
  exact Nat.compare_eq_gt.mpr closer

/-- At one common depth the two observers return the same seniority. Both-real is a tie on both
sides even though the sentinel need not equal the depth. -/
theorem compareRule1b_actual_eq_hybrid
    {V : Type*} [DecidableEq V] (sentinel n : Nat)
    {left right : OfficialCIPNode V}
    (rankedLeft : OutwardRanked left) (rankedRight : OutwardRanked right)
    (depthLeft : left.depth = n) (depthRight : right.depth = n)
    (below : n < sentinel) :
    compareRule1b left.rule1bRootDistance right.rule1bRootDistance =
      compareRule1b (hybridDuplicatePriority sentinel left)
        (hybridDuplicatePriority sentinel right) := by
  rcases rankedLeft.classified with realLeft | ⟨jLeft, provenanceLeft, earlierLeft⟩
  · rcases rankedRight.classified with realRight | ⟨jRight, provenanceRight, earlierRight⟩
    · have actual : left.rule1bRootDistance = n ∧ right.rule1bRootDistance = n := by
        simp [rule1bRootDistance, realLeft, realRight, depthLeft, depthRight]
      simp [actual.1, actual.2, hybridDuplicatePriority, realLeft, realRight,
        compareRule1b_refl]
    · have leftActual : left.rule1bRootDistance = n := by
        simp [rule1bRootDistance, realLeft, depthLeft]
      have rightActual : right.rule1bRootDistance = jRight := by
        rcases provenanceRight with ringRight | multipleRight
        · simp [rule1bRootDistance, ringRight]
        · simp [rule1bRootDistance, multipleRight]
      have rightHybrid : hybridDuplicatePriority sentinel right = jRight := by
        rcases provenanceRight with ringRight | multipleRight
        · simp [ringRight]
        · simp [multipleRight]
      have leftHybrid : hybridDuplicatePriority sentinel left = sentinel := by
        simp [realLeft]
      rw [leftActual, rightActual, leftHybrid, rightHybrid]
      rw [compareRule1b_lt_of_gt (by simpa [depthRight] using earlierRight)]
      exact (compareRule1b_lt_of_gt
        (Nat.lt_trans (by simpa [depthRight] using earlierRight) below)).symm
  · rcases rankedRight.classified with realRight | ⟨jRight, provenanceRight, earlierRight⟩
    · have rightActual : right.rule1bRootDistance = n := by
        simp [rule1bRootDistance, realRight, depthRight]
      have leftActual : left.rule1bRootDistance = jLeft := by
        rcases provenanceLeft with ringLeft | multipleLeft
        · simp [rule1bRootDistance, ringLeft]
        · simp [rule1bRootDistance, multipleLeft]
      have leftHybrid : hybridDuplicatePriority sentinel left = jLeft := by
        rcases provenanceLeft with ringLeft | multipleLeft
        · simp [ringLeft]
        · simp [multipleLeft]
      have rightHybrid : hybridDuplicatePriority sentinel right = sentinel := by
        simp [realRight]
      rw [leftActual, rightActual, leftHybrid, rightHybrid]
      rw [compareRule1b_gt_of_lt (by simpa [depthLeft] using earlierLeft)]
      exact (compareRule1b_gt_of_lt
        (Nat.lt_trans (by simpa [depthLeft] using earlierLeft) below)).symm
    · have leftValue : left.rule1bRootDistance = jLeft ∧
          hybridDuplicatePriority sentinel left = jLeft := by
        rcases provenanceLeft with ringLeft | multipleLeft
        · exact ⟨by simp [rule1bRootDistance, ringLeft], by simp [ringLeft]⟩
        · exact ⟨by simp [rule1bRootDistance, multipleLeft], by simp [multipleLeft]⟩
      have rightValue : right.rule1bRootDistance = jRight ∧
          hybridDuplicatePriority sentinel right = jRight := by
        rcases provenanceRight with ringRight | multipleRight
        · exact ⟨by simp [rule1bRootDistance, ringRight], by simp [ringRight]⟩
        · exact ⟨by simp [rule1bRootDistance, multipleRight], by simp [multipleRight]⟩
      simp [leftValue.1, leftValue.2, rightValue.1, rightValue.2]

theorem hybrid_real_ne_actual
    {V : Type*} [DecidableEq V] (sentinel : Nat) (node : OfficialCIPNode V)
    (real : node.provenance = realAtom)
    (below : node.depth < sentinel) :
    hybridDuplicatePriority sentinel node ≠ node.rule1bRootDistance := by
  simp [hybridDuplicatePriority, rule1bRootDistance, real]
  exact Nat.ne_of_gt below

inductive ObservedClass where
  | real
  | duplicate (distance : Nat)
  deriving DecidableEq, Repr

def observedClass {V : Type*} (node : OfficialCIPNode V) : ObservedClass :=
  match node.provenance with
  | realAtom => .real
  | ringDuplicate distance => .duplicate distance
  | multipleBondDuplicate distance => .duplicate distance
  | OfficialCIPNodeProvenance.placeholder _ distance => .duplicate distance

/-- The outward invariant makes the actual Rule 1b number decide the class. Value `n` is real.
A smaller value is the represented duplicate distance. -/
theorem observedClass_of_rule1b
    {V : Type*} [DecidableEq V] {node : OfficialCIPNode V}
    (ranked : OutwardRanked node) :
    (node.rule1bRootDistance = node.depth ∧ observedClass node = .real ∧
        node.provenance = realAtom) ∨
    (node.rule1bRootDistance < node.depth ∧
        observedClass node = .duplicate node.rule1bRootDistance ∧
        node.provenance ≠ realAtom) := by
  rcases ranked.classified with real | ⟨j, provenance, earlier⟩
  · left
    simp [rule1bRootDistance, observedClass, real]
  · right
    rcases provenance with ring | multiple
    · refine ⟨?_, ?_, ?_⟩
      · simpa [rule1bRootDistance, ring] using earlier
      · simp [observedClass, rule1bRootDistance, ring]
      · simp [ring]
    · refine ⟨?_, ?_, ?_⟩
      · simpa [rule1bRootDistance, multiple] using earlier
      · simp [observedClass, rule1bRootDistance, multiple]
      · simp [multiple]

theorem observedClass_eq_of_same_depth
    {V : Type*} [DecidableEq V] {n : Nat} {left right : OfficialCIPNode V}
    (rankedLeft : OutwardRanked left) (rankedRight : OutwardRanked right)
    (depthLeft : left.depth = n) (depthRight : right.depth = n)
    (sameDistance : left.rule1bRootDistance = right.rule1bRootDistance) :
    observedClass left = observedClass right := by
  rcases observedClass_of_rule1b rankedLeft with
    ⟨leftValue, leftClass, _⟩ | ⟨leftValue, leftClass, _⟩
  · rcases observedClass_of_rule1b rankedRight with
      ⟨rightValue, rightClass, _⟩ | ⟨rightValue, rightClass, _⟩
    · simp [leftClass, rightClass]
    · have leftNumber : left.rule1bRootDistance = n := by simpa [depthLeft] using leftValue
      have rightNumber : right.rule1bRootDistance < n := by simpa [depthRight] using rightValue
      have : n < n := by rw [← leftNumber, ← sameDistance] at rightNumber; omega
      omega
  · rcases observedClass_of_rule1b rankedRight with
      ⟨rightValue, rightClass, _⟩ | ⟨rightValue, rightClass, _⟩
    · have rightNumber : right.rule1bRootDistance = n := by simpa [depthRight] using rightValue
      have leftNumber : left.rule1bRootDistance < n := by simpa [depthLeft] using leftValue
      have : n < n := by rw [← rightNumber, sameDistance] at leftNumber; omega
      omega
    · simp [leftClass, rightClass, sameDistance]

def SphereDepthGraded {V : Type*} [DecidableEq V] (depth0 : Nat)
    (sources : List (List (OfficialSparseEntry (OfficialCIPNode V)))) : Prop :=
  ∀ k entry, entry ∈ sources.getD k [] →
    OutwardRanked entry.2 ∧ entry.2.depth = depth0 + k

def SphereAddressGraded {α : Type*}
    (sources : List (List (OfficialSparseEntry α))) : Prop :=
  ∀ k entry, entry ∈ sources.getD k [] → entry.1.length = k

private theorem graded_tail {V : Type*} [DecidableEq V] {n : Nat}
    {layer : List (OfficialSparseEntry (OfficialCIPNode V))}
    {rest : List (List (OfficialSparseEntry (OfficialCIPNode V)))}
    (graded : SphereDepthGraded n (layer :: rest)) :
    SphereDepthGraded (n + 1) rest := by
  intro k entry present
  have stored := graded (k + 1) entry (by simpa [List.getD_cons_succ] using present)
  exact ⟨stored.1, by omega⟩

private theorem bound_tail {V : Type*} [DecidableEq V] {sentinel : Nat}
    {layer : List (OfficialSparseEntry (OfficialCIPNode V))}
    {rest : List (List (OfficialSparseEntry (OfficialCIPNode V)))}
    (bound : ∀ k entry, entry ∈ (layer :: rest).getD k [] → entry.2.depth < sentinel) :
    ∀ k entry, entry ∈ rest.getD k [] → entry.2.depth < sentinel := by
  intro k entry present
  exact bound (k + 1) entry (by simpa [List.getD_cons_succ] using present)

private theorem compareSparseEntry_of_observation
    {α : Type} (cmp : α → α → Ordering)
    (pathLeft pathRight : List Nat) (actualLeft actualRight hybridLeft hybridRight : α)
    (sameObservation : cmp actualLeft actualRight = cmp hybridLeft hybridRight) :
    compareSparseEntry cmp (pathLeft, actualLeft) (pathRight, actualRight) =
      compareSparseEntry cmp (pathLeft, hybridLeft) (pathRight, hybridRight) := by
  unfold compareSparseEntry
  simp only [compareLex]
  cases pathOrder : List.compareLex compareNat pathRight pathLeft with
  | lt =>
      change (flip (List.compareLex compareNat) pathLeft pathRight).then
          (cmp actualLeft actualRight) =
        (flip (List.compareLex compareNat) pathLeft pathRight).then
          (cmp hybridLeft hybridRight)
      have pathCmp : flip (List.compareLex compareNat) pathLeft pathRight = .lt := by
        change List.compareLex compareNat pathRight pathLeft = .lt
        exact pathOrder
      rw [pathCmp]
      rfl
  | gt =>
      change (flip (List.compareLex compareNat) pathLeft pathRight).then
          (cmp actualLeft actualRight) =
        (flip (List.compareLex compareNat) pathLeft pathRight).then
          (cmp hybridLeft hybridRight)
      have pathCmp : flip (List.compareLex compareNat) pathLeft pathRight = .gt := by
        change List.compareLex compareNat pathRight pathLeft = .gt
        exact pathOrder
      rw [pathCmp]
      rfl
  | eq =>
      change (flip (List.compareLex compareNat) pathLeft pathRight).then
          (cmp actualLeft actualRight) =
        (flip (List.compareLex compareNat) pathLeft pathRight).then
          (cmp hybridLeft hybridRight)
      have pathCmp : flip (List.compareLex compareNat) pathLeft pathRight = .eq := by
        change List.compareLex compareNat pathRight pathLeft = .eq
        exact pathOrder
      rw [pathCmp]
      exact sameObservation

private theorem then_congr {a b c d : Ordering} (left : a = b) (right : c = d) :
    a.then c = b.then d := by
  subst left
  subst right
  rfl

private theorem compareLayer_actual_eq_hybrid
    {V : Type*} [DecidableEq V] (sentinel n : Nat)
    (layerLeft layerRight : List (OfficialSparseEntry (OfficialCIPNode V)))
    (uniformLeft : ∀ entry ∈ layerLeft, OutwardRanked entry.2 ∧ entry.2.depth = n)
    (uniformRight : ∀ entry ∈ layerRight, OutwardRanked entry.2 ∧ entry.2.depth = n)
    (below : n < sentinel) :
    compareSparseLayer compareRule1b
        (layerLeft.map (mapObservation rule1bRootDistance))
        (layerRight.map (mapObservation rule1bRootDistance)) =
      compareSparseLayer compareRule1b
        (layerLeft.map (mapObservation (hybridDuplicatePriority sentinel)))
        (layerRight.map (mapObservation (hybridDuplicatePriority sentinel))) := by
  induction layerLeft generalizing layerRight with
  | nil =>
      cases layerRight <;> simp [compareSparseLayer, List.compareLex]
  | cons entryLeft tailLeft tailLeftIh =>
      cases layerRight with
      | nil => simp [compareSparseLayer, List.compareLex]
      | cons entryRight tailRight =>
          rcases entryLeft with ⟨pathLeft, nodeLeft⟩
          rcases entryRight with ⟨pathRight, nodeRight⟩
          have entryAgreement :
              compareSparseEntry compareRule1b
                (pathLeft, rule1bRootDistance nodeLeft)
                  (pathRight, rule1bRootDistance nodeRight) =
                compareSparseEntry compareRule1b
                  (pathLeft, hybridDuplicatePriority sentinel nodeLeft)
                  (pathRight, hybridDuplicatePriority sentinel nodeRight) := by
            exact compareSparseEntry_of_observation compareRule1b pathLeft pathRight
              (rule1bRootDistance nodeLeft) (rule1bRootDistance nodeRight)
              (hybridDuplicatePriority sentinel nodeLeft)
              (hybridDuplicatePriority sentinel nodeRight)
              (compareRule1b_actual_eq_hybrid sentinel n
                (uniformLeft (pathLeft, nodeLeft) (by simp)).1
                (uniformRight (pathRight, nodeRight) (by simp)).1
                (uniformLeft (pathLeft, nodeLeft) (by simp)).2
                (uniformRight (pathRight, nodeRight) (by simp)).2
                below)
          have tailAgreement :=
            tailLeftIh tailRight
              (fun entry present => uniformLeft entry (by simp [present]))
              (fun entry present => uniformRight entry (by simp [present]))
          simp only [List.map_cons, compareSparseLayer, List.compareLex_cons_cons]
          exact then_congr entryAgreement tailAgreement

/-- Sphere-by-sphere Rule 1b seniority agrees. Each sphere is one common depth, so the proof
never flattens the arm into one multiset. -/
theorem compareRule1bLayers_actual_eq_hybrid
    {V : Type*} [DecidableEq V] (sentinel n : Nat)
    (left right : List (List (OfficialSparseEntry (OfficialCIPNode V))))
    (gradedLeft : SphereDepthGraded n left) (gradedRight : SphereDepthGraded n right)
    (boundLeft : ∀ k entry, entry ∈ left.getD k [] → entry.2.depth < sentinel)
    (boundRight : ∀ k entry, entry ∈ right.getD k [] → entry.2.depth < sentinel) :
    compareSparseLayers compareRule1b (mapSourceLayers rule1bRootDistance left)
        (mapSourceLayers rule1bRootDistance right) =
      compareSparseLayers compareRule1b
        (mapSourceLayers (hybridDuplicatePriority sentinel) left)
        (mapSourceLayers (hybridDuplicatePriority sentinel) right) := by
  induction left generalizing right n with
  | nil =>
      cases right <;> simp [mapSourceLayers, compareSparseLayers, List.compareLex]
  | cons layerLeft restLeft restIh =>
      cases right with
      | nil => simp [mapSourceLayers, compareSparseLayers, List.compareLex]
      | cons layerRight restRight =>
          have tailAgreement :=
            restIh (n + 1) restRight (graded_tail gradedLeft) (graded_tail gradedRight)
              (bound_tail boundLeft) (bound_tail boundRight)
          have layerAgreement :
              compareSparseLayer compareRule1b
                  (layerLeft.map (mapObservation rule1bRootDistance))
                  (layerRight.map (mapObservation rule1bRootDistance)) =
                compareSparseLayer compareRule1b
                  (layerLeft.map (mapObservation (hybridDuplicatePriority sentinel)))
                  (layerRight.map (mapObservation (hybridDuplicatePriority sentinel))) := by
            cases layerLeft with
            | nil =>
                cases layerRight <;> simp [compareSparseLayer, List.compareLex]
            | cons entryLeft tailLeft =>
                cases layerRight with
                | nil => simp [compareSparseLayer, List.compareLex]
                | cons entryRight tailRight =>
                    have inSphere : entryLeft ∈ ((entryLeft :: tailLeft) :: restLeft).getD 0 [] := by
                      rw [List.getD_cons_zero]
                      exact List.mem_cons_self
                    have below : n < sentinel := by
                      have stored := gradedLeft 0 entryLeft inSphere
                      have small := boundLeft 0 entryLeft inSphere
                      simpa [stored.2] using small
                    apply compareLayer_actual_eq_hybrid sentinel n
                    · intro entry present
                      have inRoot : entry ∈ ((entryLeft :: tailLeft) :: restLeft).getD 0 [] := by
                        rw [List.getD_cons_zero]
                        exact present
                      exact gradedLeft 0 entry inRoot
                    · intro entry present
                      have inRoot : entry ∈ ((entryRight :: tailRight) :: restRight).getD 0 [] := by
                        rw [List.getD_cons_zero]
                        exact present
                      exact gradedRight 0 entry inRoot
                    · exact below
          simp only [mapSourceLayers, List.map_cons, compareSparseLayers,
            List.compareLex_cons_cons]
          exact then_congr layerAgreement tailAgreement

theorem subtree_depth_invariant
    (input : CertifiedLocalizedCIPInput)
    {rootAtom : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (ranked : OutwardRanked node)
    (depthAligned : node.depth = path.length)
    (derived : input.DeclarativeLocalizedOccurrenceSubtree rootAtom path fuel node occurrence) :
    OutwardRanked occurrence.node ∧
      occurrence.node.depth = occurrence.address.length ∧
      path <+: occurrence.address ∧
      occurrence.node.depth =
        node.depth + (occurrence.address.length - path.length) := by
  revert ranked depthAligned
  induction derived with
  | subtreeRoot path fuel node =>
      intro ranked depthAligned
      refine ⟨ranked, depthAligned, List.prefix_refl _, ?_⟩
      simp [depthAligned]
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot descendant ih =>
      intro ranked depthAligned
      have childPresent : child ∈ input.executableOfficialCIPChildren node :=
        List.fst_mem_of_mem_zipIdx childAtSlot
      have childStep := outwardRanked_of_executableChild input ranked childPresent
      have childDepth : child.depth = (path ++ [slot]).length := by
        rw [childStep.2, depthAligned]
        simp
      obtain ⟨childRanked, childAddress, childPrefix, childRelative⟩ :=
        ih childStep.1 childDepth
      refine ⟨childRanked, childAddress,
        List.IsPrefix.trans (List.prefix_append path [slot]) childPrefix, ?_⟩
      have suffixLength : (path ++ [slot]).length ≤ occurrence.address.length :=
        List.IsPrefix.length_le childPrefix
      rw [childRelative, childStep.2]
      omega

theorem carrierOccurrence_ranked_depth
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrence fuel occurrence) :
    OutwardRanked occurrence.node ∧
      occurrence.node.depth = occurrence.address.length := by
  have rooted := input.declarativeLocalizedOccurrence_as_rootSubtree derived
  have rootDepth : (root occurrence.root).depth = ([] : List Nat).length := by
    unfold depth
    simp [root]
  have stored :=
    subtree_depth_invariant input (outwardRanked_root occurrence.root) rootDepth rooted
  exact ⟨stored.1, stored.2.1⟩

/-- An address extension in one rooted carrier is an outward move: the depth grows by the
length of the appended slot suffix. -/
theorem outwardExtension_depth
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {start occurrence : input.LocalizedCIPOccurrenceFrame}
    (startDerived : input.DeclarativeLocalizedOccurrence fuel start)
    (occurrenceDerived : input.DeclarativeLocalizedOccurrence fuel occurrence)
    (sameRoot : occurrence.root = start.root)
    (extension : start.address <+: occurrence.address) :
    occurrence.node.depth =
      start.node.depth + (occurrence.address.length - start.address.length) ∧
    occurrence.root = start.root := by
  obtain ⟨_, startDepth⟩ := carrierOccurrence_ranked_depth input startDerived
  obtain ⟨_, occurrenceDepth⟩ := carrierOccurrence_ranked_depth input occurrenceDerived
  have longer : start.address.length ≤ occurrence.address.length :=
    List.IsPrefix.length_le extension
  refine ⟨?_, sameRoot⟩
  rw [startDepth, occurrenceDepth]
  exact (Nat.add_sub_of_le longer).symm

theorem outwardFrame_step
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {source childFrame : input.LocalizedCIPOccurrenceFrame} {slot : Nat}
    (sourceDerived : input.DeclarativeLocalizedOccurrence fuel source)
    (childDerived : input.DeclarativeLocalizedOccurrence fuel childFrame)
    (sameRoot : childFrame.root = source.root)
    (childAddress : childFrame.address = source.address ++ [slot]) :
    ∃ child, (child, slot) ∈ (input.executableOfficialCIPChildren source.node).zipIdx ∧
      childFrame.node = child ∧
      OutwardRanked child ∧
      child.depth = source.node.depth + 1 := by
  obtain ⟨child, atSlot, identity⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child
      sourceDerived childDerived sameRoot slot childAddress
  have nodeIdentity : childFrame.node = child := by
    simp [identity]
  have present : child ∈ input.executableOfficialCIPChildren source.node :=
    List.fst_mem_of_mem_zipIdx atSlot
  obtain ⟨sourceRanked, _⟩ := carrierOccurrence_ranked_depth input sourceDerived
  have step := outwardRanked_of_executableChild input sourceRanked present
  exact ⟨child, atSlot, nodeIdentity, step.1, step.2⟩

/-- A carrier parent frame is the shorter address. It is not an outward extension of its child. -/
theorem parentFrame_not_outwardExtension
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {source parent : input.LocalizedCIPOccurrenceFrame}
    (present : parent ∈ input.localizedCarrierParentFrames (fuel := fuel) source) :
    ¬ source.address <+: parent.address := by
  rw [localizedCarrierParentFrames, List.mem_filter] at present
  rcases present with ⟨_, condition⟩
  simp only [Bool.and_eq_true, beq_iff_eq] at condition
  intro extension
  have longer : source.address.length ≤ parent.address.length :=
    List.IsPrefix.length_le extension
  omega

private theorem depth_lt_sentinel_of_support
    {V : Type*} [DecidableEq V] {sentinel fuel n : Nat}
    {sources : List (List (OfficialSparseEntry (OfficialCIPNode V)))}
    (graded : SphereDepthGraded n sources)
    (support : sources.length ≤ fuel + 1)
    (bound : n + fuel < sentinel)
    {k : Nat} {entry : OfficialSparseEntry (OfficialCIPNode V)}
    (present : entry ∈ sources.getD k []) :
    entry.2.depth < sentinel := by
  have index : k < sources.length := by
    by_contra tooFar
    have noneIndex : sources[k]? = none :=
      List.getElem?_eq_none (Nat.not_lt.mp tooFar)
    rw [List.getD_eq_getElem?_getD, noneIndex] at present
    simp at present
  have equation := (graded k entry present).2
  have smallIndex : k ≤ fuel := by omega
  omega

structure ExpansionTwin
    (input : CertifiedLocalizedCIPInput) (sentinel fuel depth : Nat)
    (actual hybrid : OfficialRuleMajorKey input.Atom) : Prop where
  sources : actual.sourceNodes = hybrid.sourceNodes
  completeEq : actual.complete = hybrid.complete
  done : actual.complete = true
  graded : SphereDepthGraded depth actual.sourceNodes
  addressed : SphereAddressGraded actual.sourceNodes
  support : actual.sourceNodes.length ≤ fuel + 1
  alignActual : SourceAlignedWith rule1bRootDistance input.moleculeGraph actual
  alignHybrid : SourceAlignedWith (hybridDuplicatePriority sentinel)
    input.moleculeGraph hybrid

private theorem twin_rule1a
    (input : CertifiedLocalizedCIPInput) {sentinel fuel depth : Nat}
    {actual hybrid : OfficialRuleMajorKey input.Atom}
    (twin : ExpansionTwin input sentinel fuel depth actual hybrid) :
    actual.rule1a = hybrid.rule1a ∧ actual.rule2 = hybrid.rule2 := by
  rcases twin.alignActual with ⟨actual1a, _, actual2⟩
  rcases twin.alignHybrid with ⟨hybrid1a, _, hybrid2⟩
  refine ⟨?_, ?_⟩
  · rw [actual1a, hybrid1a, twin.sources]
  · rw [actual2, hybrid2, twin.sources]

private theorem compare_of_twins
    (input : CertifiedLocalizedCIPInput) {sentinel fuel n : Nat}
    {actualLeft hybridLeft actualRight hybridRight : OfficialRuleMajorKey input.Atom}
    (left : ExpansionTwin input sentinel fuel n actualLeft hybridLeft)
    (right : ExpansionTwin input sentinel fuel n actualRight hybridRight)
    (bound : n + fuel < sentinel) :
    compare actualLeft actualRight = compare hybridLeft hybridRight := by
  obtain ⟨rule1aLeft, rule2Left⟩ := twin_rule1a input left
  obtain ⟨rule1aRight, rule2Right⟩ := twin_rule1a input right
  have rule1b :
      compareSparseLayers compareRule1b actualLeft.rule1b actualRight.rule1b =
        compareSparseLayers compareRule1b hybridLeft.rule1b hybridRight.rule1b := by
    rcases left.alignActual with ⟨_, actualLeft1b, _⟩
    rcases right.alignActual with ⟨_, actualRight1b, _⟩
    rcases left.alignHybrid with ⟨_, hybridLeft1b, _⟩
    rcases right.alignHybrid with ⟨_, hybridRight1b, _⟩
    rw [actualLeft1b, actualRight1b, hybridLeft1b, hybridRight1b,
      ← left.sources, ← right.sources]
    exact compareRule1bLayers_actual_eq_hybrid sentinel n
      actualLeft.sourceNodes actualRight.sourceNodes
      left.graded right.graded
      (fun k entry present =>
        depth_lt_sentinel_of_support left.graded left.support bound present)
      (fun k entry present =>
        depth_lt_sentinel_of_support right.graded right.support bound present)
  unfold OfficialRuleMajorKey.compare
  simp only [compareLex, Ordering.byKey]
  rw [rule1aLeft, rule1aRight, rule2Left, rule2Right, rule1b]

private theorem compare?_of_twins
    (input : CertifiedLocalizedCIPInput) {sentinel fuel n : Nat}
    {actualLeft hybridLeft actualRight hybridRight : OfficialRuleMajorKey input.Atom}
    (left : ExpansionTwin input sentinel fuel n actualLeft hybridLeft)
    (right : ExpansionTwin input sentinel fuel n actualRight hybridRight)
    (bound : n + fuel < sentinel) :
    compare? actualLeft actualRight = compare? hybridLeft hybridRight := by
  obtain ⟨rule1aLeft, _⟩ := twin_rule1a input left
  obtain ⟨rule1aRight, _⟩ := twin_rule1a input right
  have hybridLeftDone : hybridLeft.complete = true := by
    rw [← left.completeEq, left.done]
  have hybridRightDone : hybridRight.complete = true := by
    rw [← right.completeEq, right.done]
  unfold compare?
  rw [rule1aLeft, rule1aRight]
  cases outcome :
      compareSparseLayers compareNat hybridLeft.rule1a hybridRight.rule1a with
  | lt => simp
  | gt => simp
  | eq =>
      simp [left.done, right.done, hybridLeftDone, hybridRightDone]
      exact compare_of_twins input left right bound

private theorem insert?_twin
    (input : CertifiedLocalizedCIPInput) (sentinel fuel depth : Nat)
    (bound : depth + fuel < sentinel)
    (candidateActual candidateHybrid : OfficialRuleMajorKey input.Atom)
    (candidate : ExpansionTwin input sentinel fuel depth candidateActual candidateHybrid) :
    ∀ {tailActual tailHybrid : List (OfficialRuleMajorKey input.Atom)},
      List.Forall₂ (ExpansionTwin input sentinel fuel depth) tailActual tailHybrid →
      ∃ sortedActual sortedHybrid,
        insert? candidateActual tailActual = some sortedActual ∧
        insert? candidateHybrid tailHybrid = some sortedHybrid ∧
        List.Forall₂ (ExpansionTwin input sentinel fuel depth) sortedActual sortedHybrid := by
  intro tailActual tailHybrid related
  revert tailHybrid related
  induction tailActual with
  | nil =>
      intro tailHybrid related
      cases tailHybrid with
      | nil =>
          cases related
          refine ⟨[candidateActual], [candidateHybrid], by simp [insert?],
            by simp [insert?], ?_⟩
          exact List.Forall₂.cons candidate List.Forall₂.nil
      | cons _ _ => cases related
  | cons headActual tailActual ih =>
      intro tailHybrid related
      cases tailHybrid with
      | nil => cases related
      | cons headHybrid tailHybrid =>
          cases related with
          | cons headRelated tailRelated =>
              have compared := compare?_of_twins input candidate headRelated bound
              have actualSome := compare?_isSome_of_complete candidateActual headActual
                candidate.done headRelated.done
              cases outcome : compare? candidateActual headActual with
              | none => simp [outcome] at actualSome
              | some ordering =>
                  have hybridOutcome : compare? candidateHybrid headHybrid = some ordering := by
                    rw [← compared, outcome]
                  cases ordering with
                  | gt =>
                      refine ⟨candidateActual :: headActual :: tailActual,
                        candidateHybrid :: headHybrid :: tailHybrid, ?_, ?_, ?_⟩
                      · simp [insert?, outcome]
                      · simp [insert?, hybridOutcome]
                      · exact List.Forall₂.cons candidate
                          (List.Forall₂.cons headRelated tailRelated)
                  | eq =>
                      refine ⟨candidateActual :: headActual :: tailActual,
                        candidateHybrid :: headHybrid :: tailHybrid, ?_, ?_, ?_⟩
                      · simp [insert?, outcome]
                      · simp [insert?, hybridOutcome]
                      · exact List.Forall₂.cons candidate
                          (List.Forall₂.cons headRelated tailRelated)
                  | lt =>
                      obtain ⟨sortedActual, sortedHybrid, actualInserted,
                        hybridInserted, sortedRelated⟩ := ih tailRelated
                      refine ⟨headActual :: sortedActual, headHybrid :: sortedHybrid,
                        ?_, ?_, ?_⟩
                      · simp [insert?, outcome, actualInserted]
                      · simp [insert?, hybridOutcome, hybridInserted]
                      · exact List.Forall₂.cons headRelated sortedRelated

private theorem sort?_twin
    (input : CertifiedLocalizedCIPInput) (sentinel fuel depth : Nat)
    (bound : depth + fuel < sentinel) :
    ∀ {keysActual keysHybrid : List (OfficialRuleMajorKey input.Atom)},
      List.Forall₂ (ExpansionTwin input sentinel fuel depth) keysActual keysHybrid →
      ∃ sortedActual sortedHybrid,
        sort? keysActual = some sortedActual ∧
        sort? keysHybrid = some sortedHybrid ∧
        List.Forall₂ (ExpansionTwin input sentinel fuel depth) sortedActual sortedHybrid := by
  intro keysActual keysHybrid related
  induction keysActual generalizing keysHybrid with
  | nil =>
      cases keysHybrid with
      | nil =>
          cases related
          exact ⟨[], [], by simp [sort?], by simp [sort?], List.Forall₂.nil⟩
      | cons _ _ => cases related
  | cons candidateActual tailActual ih =>
      cases keysHybrid with
      | nil => cases related
      | cons candidateHybrid tailHybrid =>
          cases related with
          | cons headRelated tailRelated =>
              obtain ⟨sortedTailActual, sortedTailHybrid, actualSorted, hybridSorted, tailTwins⟩ :=
              ih tailRelated
              obtain ⟨sortedActual, sortedHybrid, actualInserted, hybridInserted, sortedTwins⟩ :=
                insert?_twin input sentinel fuel depth bound candidateActual candidateHybrid
                  headRelated tailTwins
              refine ⟨sortedActual, sortedHybrid, ?_, ?_, sortedTwins⟩
              · simp [sort?, actualSorted, actualInserted]
              · simp [sort?, hybridSorted, hybridInserted]

private theorem buildNodeList
    (input : CertifiedLocalizedCIPInput) (sentinel fuel childDepth : Nat)
    (bound : childDepth + fuel < sentinel)
    (buildOne : ∀ child, OutwardRanked child → child.depth = childDepth →
      MoleculeGraph.OfficialExpansionCompleteWithin input.executableOfficialCIPChildren
        fuel child →
      ∃ actual hybrid,
        buildOfficialRuleMajorKeyWith rule1bRootDistance input.moleculeGraph
            input.executableOfficialCIPChildren fuel child = some actual ∧
        buildOfficialRuleMajorKeyWith (hybridDuplicatePriority sentinel) input.moleculeGraph
            input.executableOfficialCIPChildren fuel child = some hybrid ∧
        ExpansionTwin input sentinel fuel childDepth actual hybrid) :
    ∀ (nodes : List (OfficialCIPNode input.Atom)),
      (∀ child ∈ nodes, OutwardRanked child ∧ child.depth = childDepth ∧
        MoleculeGraph.OfficialExpansionCompleteWithin input.executableOfficialCIPChildren
          fuel child) →
      ∃ keysActual keysHybrid,
        nodes.mapM (buildOfficialRuleMajorKeyWith rule1bRootDistance input.moleculeGraph
            input.executableOfficialCIPChildren fuel) = some keysActual ∧
        nodes.mapM (buildOfficialRuleMajorKeyWith (hybridDuplicatePriority sentinel)
            input.moleculeGraph input.executableOfficialCIPChildren fuel) = some keysHybrid ∧
        List.Forall₂ (ExpansionTwin input sentinel fuel childDepth) keysActual keysHybrid
  | [], _ => ⟨[], [], by simp, by simp, List.Forall₂.nil⟩
  | child :: nodes, specification => by
      have childSpecification := specification child (by simp)
      obtain ⟨actual, hybrid, actualBuilt, hybridBuilt, twin⟩ :=
        buildOne child childSpecification.1 childSpecification.2.1 childSpecification.2.2
      have tailSpecification : ∀ tail ∈ nodes, OutwardRanked tail ∧ tail.depth = childDepth ∧
          MoleculeGraph.OfficialExpansionCompleteWithin input.executableOfficialCIPChildren
            fuel tail := by
        intro tail present
        exact specification tail (by simp [present])
      obtain ⟨tailActual, tailHybrid, actualTail, hybridTail, tailTwins⟩ :=
        buildNodeList input sentinel fuel childDepth bound buildOne nodes tailSpecification
      refine ⟨actual :: tailActual, hybrid :: tailHybrid, ?_, ?_,
        List.Forall₂.cons twin tailTwins⟩
      · simp [actualBuilt, actualTail]
      · simp [hybridBuilt, hybridTail]

private theorem singleton_depth_graded
    {V : Type*} [DecidableEq V] {n : Nat} {node : OfficialCIPNode V}
    (ranked : OutwardRanked node) (depthAligned : node.depth = n) :
    SphereDepthGraded n [[([], node)]] := by
  intro k entry present
  cases k with
  | zero =>
      rw [List.getD_cons_zero] at present
      simp at present
      rcases present with rfl
      exact ⟨ranked, by simp [depthAligned]⟩
  | succ k =>
      rw [List.getD_cons_succ] at present
      simp at present

private theorem singleton_address_graded
    {V : Type*} [DecidableEq V] (node : OfficialCIPNode V) :
    SphereAddressGraded [[([], node)]] := by
  intro k entry present
  cases k with
  | zero =>
      rw [List.getD_cons_zero] at present
      simp at present
      rcases present with rfl
      simp
  | succ k =>
      rw [List.getD_cons_succ] at present
      simp at present

private theorem twin_root
    (input : CertifiedLocalizedCIPInput) (sentinel fuel n : Nat)
    (node : OfficialCIPNode input.Atom)
    (ranked : OutwardRanked node) (depthAligned : node.depth = n) :
    ExpansionTwin input sentinel fuel n
      (officialRuleMajorRootKeyWith rule1bRootDistance input.moleculeGraph node true)
      (officialRuleMajorRootKeyWith (hybridDuplicatePriority sentinel)
        input.moleculeGraph node true) := by
  refine ⟨?_, rfl, rfl, singleton_depth_graded ranked depthAligned,
    singleton_address_graded node, ?_, ?_, ?_⟩
  · simp [officialRuleMajorRootKeyWith]
  · simp [officialRuleMajorRootKeyWith]
  · exact officialRuleMajorRootKeyWith_sourceAlignedWith _ _ _ _
  · exact officialRuleMajorRootKeyWith_sourceAlignedWith _ _ _ _

private theorem forall2_sources
    (input : CertifiedLocalizedCIPInput) {sentinel fuel depth : Nat}
    {left right : List (OfficialRuleMajorKey input.Atom)}
    (related : List.Forall₂ (ExpansionTwin input sentinel fuel depth) left right) :
    List.Forall₂ (fun actual hybrid => actual.sourceNodes = hybrid.sourceNodes) left right := by
  induction related with
  | nil => exact List.Forall₂.nil
  | @cons actual hybrid leftTail rightTail twin tail ih =>
      exact List.Forall₂.cons twin.sources ih

private theorem twin_of_mem_right
    (input : CertifiedLocalizedCIPInput) {sentinel fuel depth : Nat}
    {left right : List (OfficialRuleMajorKey input.Atom)}
    {hybrid : OfficialRuleMajorKey input.Atom}
    (related : List.Forall₂ (ExpansionTwin input sentinel fuel depth) left right)
    (present : hybrid ∈ right) :
    ∃ actual, actual ∈ left ∧ ExpansionTwin input sentinel fuel depth actual hybrid := by
  induction related with
  | nil => simp at present
  | @cons headActual headHybrid tailActual tailHybrid headTwin tailRelated ih =>
      rcases List.mem_cons.mp present with headEq | tailPresent
      · subst hybrid
        exact ⟨headActual, by simp, headTwin⟩
      · obtain ⟨actual, actualPresent, twin⟩ := ih tailPresent
        exact ⟨actual, by simp [actualPresent], twin⟩

private theorem exists_twin_of_mem
    (input : CertifiedLocalizedCIPInput) {sentinel fuel depth : Nat}
    {left right : List (OfficialRuleMajorKey input.Atom)}
    {actual : OfficialRuleMajorKey input.Atom}
    (related : List.Forall₂ (ExpansionTwin input sentinel fuel depth) left right)
    (present : actual ∈ left) :
    ∃ hybrid, hybrid ∈ right ∧ ExpansionTwin input sentinel fuel depth actual hybrid := by
  induction related with
  | nil => simp at present
  | @cons headActual headHybrid tailActual tailHybrid headTwin tailRelated ih =>
      rcases List.mem_cons.mp present with headEq | tailPresent
      · subst actual
        exact ⟨headHybrid, by simp, headTwin⟩
      · obtain ⟨hybrid, hybridPresent, twin⟩ := ih tailPresent
        exact ⟨hybrid, by simp [hybridPresent], twin⟩

private theorem childLayerCount_sources_congr
    {V : Type*} {left right : List (OfficialRuleMajorKey V)}
    (related : List.Forall₂ (fun actual hybrid => actual.sourceNodes = hybrid.sourceNodes)
      left right) :
    childLayerCount left (fun key => key.sourceNodes) =
      childLayerCount right (fun key => key.sourceNodes) := by
  unfold childLayerCount
  suffices ∀ initial,
      List.foldl (fun longest child => max longest child.sourceNodes.length) initial left =
        List.foldl (fun longest child => max longest child.sourceNodes.length) initial right by
    exact this 0
  induction related with
  | nil => intro initial; rfl
  | @cons actual hybrid leftTail rightTail sourcesEqual tail ih =>
      intro initial
      simp only [List.foldl_cons, sourcesEqual]
      exact ih (max initial hybrid.sourceNodes.length)

private theorem mergeLayer_sources_congr
    {V : Type*} {start depth : Nat} {left right : List (OfficialRuleMajorKey V)}
    (related : List.Forall₂ (fun actual hybrid => actual.sourceNodes = hybrid.sourceNodes)
      left right) :
    (left.zipIdx start).flatMap (fun child =>
        prefixLayer child.2 (child.1.sourceNodes.getD depth [])) =
      (right.zipIdx start).flatMap (fun child =>
        prefixLayer child.2 (child.1.sourceNodes.getD depth [])) := by
  revert right related
  induction left generalizing start with
  | nil =>
      intro right related
      cases right with
      | nil => simp
      | cons _ _ => cases related
  | cons actual leftTail ih =>
      intro right related
      cases right with
      | nil => cases related
      | cons hybrid rightTail =>
          cases related with
          | cons sourcesEqual tail =>
              simp only [List.zipIdx_cons, List.flatMap_cons]
              rw [sourcesEqual]
              exact congrArg
                (fun tailLayers => prefixLayer start (hybrid.sourceNodes.getD depth []) ++ tailLayers)
                (ih (right := rightTail) tail (start := start + 1))

private theorem mergeChildren_sources_congr
    {V : Type*} {left right : List (OfficialRuleMajorKey V)}
    (related : List.Forall₂ (fun actual hybrid => actual.sourceNodes = hybrid.sourceNodes)
      left right) :
    mergeChildren left (fun key => key.sourceNodes) =
      mergeChildren right (fun key => key.sourceNodes) := by
  unfold mergeChildren
  have countEqual := childLayerCount_sources_congr related
  simp only [countEqual]
  refine congrArg (fun layerAt =>
    (List.range (childLayerCount right (fun key => key.sourceNodes))).map layerAt) ?_
  funext depth
  exact mergeLayer_sources_congr related

private theorem getD_map_range {α : Type u} (f : Nat → α) :
    ∀ count k (fallback : α), k < count →
      ((List.range count).map f).getD k fallback = f k
  | 0, _, _, hk => by cases hk
  | count + 1, 0, _, _ => by
      simp [List.range_succ_eq_map]
  | count + 1, k + 1, fallback, hk => by
      simp only [List.range_succ_eq_map, List.map_cons, List.map_map]
      rw [List.getD_cons_succ]
      simpa [Function.comp] using
        getD_map_range (fun index => f (index + 1)) count k fallback (Nat.lt_of_succ_lt_succ hk)

private theorem mem_mergeChildren_getD
    {V α : Type*} {children : List (OfficialRuleMajorKey V)}
    {layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α))}
    {k : Nat} {entry : OfficialSparseEntry α}
    (present : entry ∈ (mergeChildren children layers).getD k []) :
    ∃ child slot old, (child, slot) ∈ children.zipIdx ∧
      old ∈ (layers child).getD k [] ∧
      entry = (slot :: old.1, old.2) := by
  have indexBound : k < (mergeChildren children layers).length := by
    by_contra tooFar
    have noneIndex : (mergeChildren children layers)[k]? = none :=
      List.getElem?_eq_none (Nat.not_lt.mp tooFar)
    rw [List.getD_eq_getElem?_getD, noneIndex] at present
    simp at present
  have lengthEquation : (mergeChildren children layers).length =
      childLayerCount children layers := by
    simp [mergeChildren, List.length_map, List.length_range]
  rw [lengthEquation] at indexBound
  have atIndex :=
    getD_map_range (fun depth =>
      children.zipIdx.flatMap fun child =>
        prefixLayer child.2 ((layers child.1).getD depth []))
      (childLayerCount children layers) k [] indexBound
  have mergeEquation :
      mergeChildren children layers =
        (List.range (childLayerCount children layers)).map fun depth =>
          children.zipIdx.flatMap fun child =>
            prefixLayer child.2 ((layers child.1).getD depth []) := by
    rfl
  rw [mergeEquation, atIndex, List.mem_flatMap] at present
  obtain ⟨indexed, indexedPresent, inPrefix⟩ := present
  rw [prefixLayer, List.mem_map] at inPrefix
  obtain ⟨old, oldPresent, identity⟩ := inPrefix
  exact ⟨indexed.1, indexed.2, old, indexedPresent, oldPresent, identity.symm⟩

private theorem childLayerCount_le
    {V α : Type*} {bound : Nat} {children : List (OfficialRuleMajorKey V)}
    {layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α))}
    (short : ∀ child ∈ children, (layers child).length ≤ bound) :
    childLayerCount children layers ≤ bound := by
  unfold childLayerCount
  suffices ∀ initial, initial ≤ bound →
      List.foldl (fun longest child => max longest (layers child).length) initial children ≤
        bound by
    exact this 0 (Nat.zero_le _)
  intro initial initialBound
  induction children generalizing initial with
  | nil => simpa using initialBound
  | cons child children ih =>
      apply ih
      · intro tail present
        exact short tail (List.mem_cons_of_mem child present)
      · exact Nat.max_le.mpr ⟨initialBound, short child (by simp)⟩

private theorem projection_getElem?
    {V α : Type*} (observe : OfficialCIPNode V → α)
    (sources : List (List (OfficialSparseEntry (OfficialCIPNode V))))
    (k index : Nat) :
    ((mapSourceLayers observe sources).getD k [])[index]? =
      ((sources.getD k [])[index]?).map (mapObservation observe) := by
  rw [mapSourceLayers_getD]
  simp

/-- Adequate fuel compiles the same outward source tree, the same relative addresses, and the
same Rule 1a and Rule 2 projections under both observers. -/
theorem expansion_twin
    (input : CertifiedLocalizedCIPInput) (sentinel : Nat) :
    ∀ fuel node n,
      OutwardRanked node →
      node.depth = n →
      n + fuel < sentinel →
      MoleculeGraph.OfficialExpansionCompleteWithin input.executableOfficialCIPChildren
        fuel node →
      ∃ actual hybrid,
        buildOfficialRuleMajorKeyWith rule1bRootDistance input.moleculeGraph
            input.executableOfficialCIPChildren fuel node = some actual ∧
        buildOfficialRuleMajorKeyWith (hybridDuplicatePriority sentinel) input.moleculeGraph
            input.executableOfficialCIPChildren fuel node = some hybrid ∧
        ExpansionTwin input sentinel fuel n actual hybrid := by
  intro fuel
  induction fuel with
  | zero =>
      intro node n ranked depthAligned bound complete
      have noChildren : input.executableOfficialCIPChildren node = [] := by
        simpa [MoleculeGraph.OfficialExpansionCompleteWithin] using complete
      refine ⟨officialRuleMajorRootKeyWith rule1bRootDistance input.moleculeGraph node true,
        officialRuleMajorRootKeyWith (hybridDuplicatePriority sentinel)
          input.moleculeGraph node true, ?_, ?_,
        twin_root input sentinel 0 n node ranked depthAligned⟩
      · simp [buildOfficialRuleMajorKeyWith, noChildren]
      · simp [buildOfficialRuleMajorKeyWith, noChildren]
  | succ fuel ih =>
      intro node n ranked depthAligned bound complete
      let children := input.executableOfficialCIPChildren node
      by_cases terminal : children.isEmpty = true
      · have noChildren : children = [] := List.isEmpty_iff.mp terminal
        refine ⟨officialRuleMajorRootKeyWith rule1bRootDistance input.moleculeGraph node true,
          officialRuleMajorRootKeyWith (hybridDuplicatePriority sentinel)
            input.moleculeGraph node true, ?_, ?_,
          twin_root input sentinel (fuel + 1) n node ranked depthAligned⟩
        · simp [buildOfficialRuleMajorKeyWith, children, noChildren]
        · simp [buildOfficialRuleMajorKeyWith, children, noChildren]
      · have childBound : (n + 1) + fuel < sentinel := by omega
        have specification : ∀ child ∈ children, OutwardRanked child ∧ child.depth = n + 1 ∧
            MoleculeGraph.OfficialExpansionCompleteWithin input.executableOfficialCIPChildren
              fuel child := by
          intro child present
          have step := outwardRanked_of_executableChild input ranked present
          refine ⟨step.1, by rw [step.2, depthAligned], complete child present⟩
        obtain ⟨keysActual, keysHybrid, actualKeys, hybridKeys, keyTwins⟩ :=
          buildNodeList input sentinel fuel (n + 1) childBound
            (fun child childRanked childDepth childComplete =>
              ih child (n + 1) childRanked childDepth childBound childComplete)
            children specification
        obtain ⟨sortedActual, sortedHybrid, actualSorted, hybridSorted, sortedTwins⟩ :=
          sort?_twin input sentinel fuel (n + 1) childBound keyTwins
        let rootActual := officialRuleMajorRootKeyWith rule1bRootDistance
          input.moleculeGraph node false
        let rootHybrid := officialRuleMajorRootKeyWith (hybridDuplicatePriority sentinel)
          input.moleculeGraph node false
        let actual := assemble rootActual sortedActual
        let hybrid := assemble rootHybrid sortedHybrid
        have sourcePairs := forall2_sources input sortedTwins
        have merged := mergeChildren_sources_congr sourcePairs
        have rootSources : rootActual.sourceNodes = [[([], node)]] ∧
            rootHybrid.sourceNodes = [[([], node)]] := by
          simp [rootActual, rootHybrid, officialRuleMajorRootKeyWith]
        have supportBound : actual.sourceNodes.length ≤ fuel + 2 := by
          have childSupport : ∀ child ∈ sortedActual, child.sourceNodes.length ≤ fuel + 1 := by
            intro child present
            obtain ⟨_, _, twin⟩ := exists_twin_of_mem input sortedTwins present
            exact twin.support
          have countBound :=
            childLayerCount_le (layers := fun key => key.sourceNodes) childSupport
          have lengthMerge : (mergeChildren sortedActual (fun key => key.sourceNodes)).length =
              childLayerCount sortedActual (fun key => key.sourceNodes) := by
            simp [mergeChildren, List.length_map, List.length_range]
          simp only [actual, assemble, List.length_append, rootSources.1]
          rw [lengthMerge]
          have counted : childLayerCount sortedActual (fun key => key.sourceNodes) ≤ fuel + 1 :=
            countBound
          simp only [List.length_singleton]
          omega
        have depthGraded : SphereDepthGraded n actual.sourceNodes := by
          intro k entry present
          cases k with
          | zero =>
              simp only [actual, assemble, rootSources.1, List.singleton_append,
                List.getD_cons_zero] at present
              simp at present
              rcases present with rfl
              exact ⟨ranked, by simp [depthAligned]⟩
          | succ k =>
              have inMerge : entry ∈
                  (mergeChildren sortedActual (fun key => key.sourceNodes)).getD k [] := by
                simpa [actual, assemble, rootSources.1, List.singleton_append,
                  List.getD_cons_succ] using present
              obtain ⟨child, slot, old, childIndexed, oldPresent, identity⟩ :=
                mem_mergeChildren_getD inMerge
              have childPresent : child ∈ sortedActual :=
                List.fst_mem_of_mem_zipIdx childIndexed
              obtain ⟨_, _, childTwin⟩ := exists_twin_of_mem input sortedTwins childPresent
              have oldGraded := childTwin.graded k old oldPresent
              have oldAddress := childTwin.addressed k old oldPresent
              cases identity
              exact ⟨oldGraded.1, by rw [oldGraded.2]; omega⟩
        have addressGraded : SphereAddressGraded actual.sourceNodes := by
          intro k entry present
          cases k with
          | zero =>
              simp only [actual, assemble, rootSources.1, List.singleton_append,
                List.getD_cons_zero] at present
              simp at present
              rcases present with rfl
              simp
          | succ k =>
              have inMerge : entry ∈
                  (mergeChildren sortedActual (fun key => key.sourceNodes)).getD k [] := by
                simpa [actual, assemble, rootSources.1, List.singleton_append,
                  List.getD_cons_succ] using present
              obtain ⟨child, _, old, childIndexed, oldPresent, identity⟩ :=
                mem_mergeChildren_getD inMerge
              have childPresent : child ∈ sortedActual :=
                List.fst_mem_of_mem_zipIdx childIndexed
              obtain ⟨_, _, childTwin⟩ := exists_twin_of_mem input sortedTwins childPresent
              have oldAddress := childTwin.addressed k old oldPresent
              cases identity
              simp [oldAddress]
        have doneActual : actual.complete = true := by
          change sortedActual.all OfficialRuleMajorKey.complete = true
          rw [List.all_eq_true]
          intro key present
          obtain ⟨_, _, twin⟩ := exists_twin_of_mem input sortedTwins present
          exact twin.done
        have doneHybrid : hybrid.complete = true := by
          change sortedHybrid.all OfficialRuleMajorKey.complete = true
          rw [List.all_eq_true]
          intro key present
          obtain ⟨_, _, twin⟩ := twin_of_mem_right input sortedTwins present
          exact Eq.trans twin.completeEq.symm twin.done
        have alignedActual : SourceAlignedWith rule1bRootDistance input.moleculeGraph actual := by
          apply SourceAlignedWith.assemble
          · exact officialRuleMajorRootKeyWith_sourceAlignedWith _ _ _ _
          · intro child present
            obtain ⟨_, _, twin⟩ := exists_twin_of_mem input sortedTwins present
            exact twin.alignActual
        have alignedHybrid :
            SourceAlignedWith (hybridDuplicatePriority sentinel) input.moleculeGraph hybrid := by
          apply SourceAlignedWith.assemble
          · exact officialRuleMajorRootKeyWith_sourceAlignedWith _ _ _ _
          · intro child present
            obtain ⟨_, _, twin⟩ := twin_of_mem_right input sortedTwins present
            exact twin.alignHybrid
        refine ⟨actual, hybrid, ?_, ?_, ?_⟩
        · unfold buildOfficialRuleMajorKeyWith
          simp [children, terminal, actualKeys, actualSorted, actual, rootActual]
        · unfold buildOfficialRuleMajorKeyWith
          simp [children, terminal, hybridKeys, hybridSorted, hybrid, rootHybrid]
        · refine ⟨?_, ?_, doneActual, depthGraded, addressGraded, supportBound,
            alignedActual, alignedHybrid⟩
          · simp only [actual, hybrid, assemble, rootSources.1, rootSources.2, merged]
          · rw [doneActual, doneHybrid]

/-- Two outward arms that start at the same stored depth have the same rule-major seniority
under the actual distance and under the hybrid sentinel. -/
theorem outwardArm_compare_eq_hybrid
    (input : CertifiedLocalizedCIPInput) (sentinel fuel n : Nat)
    (nodeLeft nodeRight : OfficialCIPNode input.Atom)
    (rankedLeft : OutwardRanked nodeLeft) (rankedRight : OutwardRanked nodeRight)
    (depthLeft : nodeLeft.depth = n) (depthRight : nodeRight.depth = n)
    (bound : n + fuel < sentinel)
    (completeLeft : MoleculeGraph.OfficialExpansionCompleteWithin
      input.executableOfficialCIPChildren fuel nodeLeft)
    (completeRight : MoleculeGraph.OfficialExpansionCompleteWithin
      input.executableOfficialCIPChildren fuel nodeRight) :
    ∃ actualLeft hybridLeft actualRight hybridRight,
      buildOfficialRuleMajorKeyWith rule1bRootDistance input.moleculeGraph
          input.executableOfficialCIPChildren fuel nodeLeft = some actualLeft ∧
      buildOfficialRuleMajorKeyWith (hybridDuplicatePriority sentinel) input.moleculeGraph
          input.executableOfficialCIPChildren fuel nodeLeft = some hybridLeft ∧
      buildOfficialRuleMajorKeyWith rule1bRootDistance input.moleculeGraph
          input.executableOfficialCIPChildren fuel nodeRight = some actualRight ∧
      buildOfficialRuleMajorKeyWith (hybridDuplicatePriority sentinel) input.moleculeGraph
          input.executableOfficialCIPChildren fuel nodeRight = some hybridRight ∧
      compare actualLeft actualRight = compare hybridLeft hybridRight ∧
      ExpansionTwin input sentinel fuel n actualLeft hybridLeft ∧
      ExpansionTwin input sentinel fuel n actualRight hybridRight := by
  obtain ⟨actualLeft, hybridLeft, actualLeftBuilt, hybridLeftBuilt, leftTwin⟩ :=
    expansion_twin input sentinel fuel nodeLeft n rankedLeft depthLeft bound completeLeft
  obtain ⟨actualRight, hybridRight, actualRightBuilt, hybridRightBuilt, rightTwin⟩ :=
    expansion_twin input sentinel fuel nodeRight n rankedRight depthRight bound completeRight
  exact ⟨actualLeft, hybridLeft, actualRight, hybridRight,
    actualLeftBuilt, hybridLeftBuilt, actualRightBuilt, hybridRightBuilt,
    compare_of_twins input leftTwin rightTwin bound, leftTwin, rightTwin⟩

theorem outwardArm_compare_eq_hybrid_sentinel
    (input : CertifiedLocalizedCIPInput) (fuel n : Nat)
    (nodeLeft nodeRight : OfficialCIPNode input.Atom)
    (rankedLeft : OutwardRanked nodeLeft) (rankedRight : OutwardRanked nodeRight)
    (depthLeft : nodeLeft.depth = n) (depthRight : nodeRight.depth = n)
    (completeLeft : MoleculeGraph.OfficialExpansionCompleteWithin
      input.executableOfficialCIPChildren fuel nodeLeft)
    (completeRight : MoleculeGraph.OfficialExpansionCompleteWithin
      input.executableOfficialCIPChildren fuel nodeRight) :
    ∃ actualLeft hybridLeft actualRight hybridRight,
      buildOfficialRuleMajorKeyWith rule1bRootDistance input.moleculeGraph
          input.executableOfficialCIPChildren fuel nodeLeft = some actualLeft ∧
      buildOfficialRuleMajorKeyWith (hybridDuplicatePriority (n + fuel + 1))
          input.moleculeGraph input.executableOfficialCIPChildren fuel nodeLeft =
        some hybridLeft ∧
      buildOfficialRuleMajorKeyWith rule1bRootDistance input.moleculeGraph
          input.executableOfficialCIPChildren fuel nodeRight = some actualRight ∧
      buildOfficialRuleMajorKeyWith (hybridDuplicatePriority (n + fuel + 1))
          input.moleculeGraph input.executableOfficialCIPChildren fuel nodeRight =
        some hybridRight ∧
      compare actualLeft actualRight = compare hybridLeft hybridRight := by
  obtain ⟨actualLeft, hybridLeft, actualRight, hybridRight, h1, h2, h3, h4, compared, _, _⟩ :=
    outwardArm_compare_eq_hybrid input (n + fuel + 1) fuel n nodeLeft nodeRight
      rankedLeft rankedRight depthLeft depthRight (by omega) completeLeft completeRight
  exact ⟨actualLeft, hybridLeft, actualRight, hybridRight, h1, h2, h3, h4, compared⟩

private theorem source_mem_of_getElem?
    {V : Type*} {sources : List (List (OfficialSparseEntry (OfficialCIPNode V)))}
    {k index : Nat} {entry : OfficialSparseEntry (OfficialCIPNode V)}
    (present : (sources.getD k [])[index]? = some entry) :
    entry ∈ sources.getD k [] :=
  List.mem_of_getElem? present

/-- Equal Rule 1a and Rule 1b projections at one occupied hierarchical position recover the
address, the atomic number, and the provenance class. The class test uses the known sphere
depth, not a valence or a pre-chosen provenance hypothesis. -/
theorem alignedCell_sameClass
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (depth0 : Nat)
    (keyLeft keyRight : OfficialRuleMajorKey V)
    (alignedLeft : SourceAlignedWith rule1bRootDistance m keyLeft)
    (alignedRight : SourceAlignedWith rule1bRootDistance m keyRight)
    (sameRule1a : keyLeft.rule1a = keyRight.rule1a)
    (sameRule1b : keyLeft.rule1b = keyRight.rule1b)
    (gradedLeft : SphereDepthGraded depth0 keyLeft.sourceNodes)
    (gradedRight : SphereDepthGraded depth0 keyRight.sourceNodes)
    (addressedLeft : SphereAddressGraded keyLeft.sourceNodes)
    {k index : Nat} {entryLeft : OfficialSparseEntry (OfficialCIPNode V)}
    (occupied : (keyLeft.sourceNodes.getD k [])[index]? = some entryLeft) :
    ∃ entryRight, (keyRight.sourceNodes.getD k [])[index]? = some entryRight ∧
      entryLeft.1 = entryRight.1 ∧
      entryLeft.1.length = k ∧
      entryLeft.2.depth = depth0 + k ∧
      entryRight.2.depth = depth0 + k ∧
      (ofLex (m.officialNodeAtomLabel entryLeft.2)).1 =
        (ofLex (m.officialNodeAtomLabel entryRight.2)).1 ∧
      entryLeft.2.rule1bRootDistance = entryRight.2.rule1bRootDistance ∧
      observedClass entryLeft.2 = observedClass entryRight.2 := by
  have leftDepth := gradedLeft k entryLeft (source_mem_of_getElem? occupied)
  have leftAddress := addressedLeft k entryLeft (source_mem_of_getElem? occupied)
  have rule1bProjection := projection_getElem? rule1bRootDistance keyLeft.sourceNodes k index
  have rule1bProjectionRight :=
    projection_getElem? rule1bRootDistance keyRight.sourceNodes k index
  have sameProjection :
      ((mapSourceLayers rule1bRootDistance keyLeft.sourceNodes).getD k [])[index]? =
        ((mapSourceLayers rule1bRootDistance keyRight.sourceNodes).getD k [])[index]? := by
    rw [← alignedLeft.2.1, ← alignedRight.2.1, sameRule1b]
  rw [rule1bProjection, rule1bProjectionRight, occupied] at sameProjection
  have rightCellNotNone : (keyRight.sourceNodes.getD k [])[index]? ≠ none := by
    intro absent
    rw [absent] at sameProjection
    simp at sameProjection
  have rightCellExists : ∃ entryRight,
      (keyRight.sourceNodes.getD k [])[index]? = some entryRight := by
    cases cell : (keyRight.sourceNodes.getD k [])[index]? with
    | none => exact False.elim (rightCellNotNone cell)
    | some entryRight => exact ⟨entryRight, rfl⟩
  obtain ⟨entryRight, rightOccupied⟩ := rightCellExists
  rw [rightOccupied] at sameProjection
  have pairEquality : (entryLeft.1, entryLeft.2.rule1bRootDistance) =
      (entryRight.1, entryRight.2.rule1bRootDistance) := by
    simpa [mapObservation] using sameProjection
  have sameAddress : entryLeft.1 = entryRight.1 :=
    congrArg (fun pair : List Nat × Nat => pair.1) pairEquality
  have sameDistance : entryLeft.2.rule1bRootDistance = entryRight.2.rule1bRootDistance :=
    congrArg (fun pair : List Nat × Nat => pair.2) pairEquality
  have rightDepth := gradedRight k entryRight (source_mem_of_getElem? rightOccupied)
  have atomicProjection := projection_getElem?
    (fun node => (ofLex (m.officialNodeAtomLabel node)).1) keyLeft.sourceNodes k index
  have atomicProjectionRight := projection_getElem?
    (fun node => (ofLex (m.officialNodeAtomLabel node)).1) keyRight.sourceNodes k index
  have sameAtomicProjection :
      ((mapSourceLayers (fun node => (ofLex (m.officialNodeAtomLabel node)).1)
          keyLeft.sourceNodes).getD k [])[index]? =
        ((mapSourceLayers (fun node => (ofLex (m.officialNodeAtomLabel node)).1)
          keyRight.sourceNodes).getD k [])[index]? := by
    rw [← alignedLeft.1, ← alignedRight.1, sameRule1a]
  rw [atomicProjection, atomicProjectionRight, occupied, rightOccupied] at sameAtomicProjection
  simp [mapObservation] at sameAtomicProjection
  refine ⟨entryRight, rightOccupied, sameAddress, leftAddress, leftDepth.2,
    rightDepth.2, sameAtomicProjection.2, sameDistance, ?_⟩
  exact observedClass_eq_of_same_depth leftDepth.1 rightDepth.1 leftDepth.2 rightDepth.2
    sameDistance

end TetraStereo.OneCenter.OutwardRule1bObserverEquivalence

assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.duplicateRootDistance_eq_firstIndex
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.duplicateRootDistance_lt_of_mem
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.history_length_eq_depth_add_one
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.outwardRanked_root
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.outwardRanked_of_executableChild
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.executable_ring_child_ancestor
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.hybridDuplicatePriority_real
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.hybridDuplicatePriority_ring
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.hybridDuplicatePriority_multiple
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.compareRule1b_actual_eq_hybrid
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.hybrid_real_ne_actual
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.observedClass_of_rule1b
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.observedClass_eq_of_same_depth
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.compareRule1bLayers_actual_eq_hybrid
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.subtree_depth_invariant
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.carrierOccurrence_ranked_depth
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.outwardExtension_depth
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.outwardFrame_step
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.parentFrame_not_outwardExtension
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.expansion_twin
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.outwardArm_compare_eq_hybrid
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.outwardArm_compare_eq_hybrid_sentinel
assert_kernel_only TetraStereo.OneCenter.OutwardRule1bObserverEquivalence.alignedCell_sameClass
