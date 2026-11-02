import TetraStereo.OneCenter.CIPAuthoritativeSparseScheduleConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace RawMolecule

/-!
# Zero-filled meaning of sparse authoritative layers

The compiled constitutional key omits absent sibling slots.  The independent hierarchy instead
observes those addresses as zero.  This file supplies the representation theorem between those
views.  Its only substantive side condition is the chemical one: every retained Rule-1a
observation is strictly above zero.  That condition is false for wildcard pseudo-atoms, which are
therefore excluded by authority-facing chemical admission rather than silently treated as atoms.
-/

/-- One address after aligning two sparse layers, with missing observations filled by `zero`. -/
structure AlignedSparseCanonicalEntry (α : Type*) where
  address : List ℕ
  left : α
  right : α

/-- Merge two path-ordered sparse layers into a common zero-filled address layer. -/
def alignSparseCanonicalLayer {α : Type*} (zero : α) :
    (left right : List (List ℕ × α)) → List (AlignedSparseCanonicalEntry α)
  | [], [] => []
  | [], (rightPath, rightValue) :: rightTail =>
      ⟨rightPath, zero, rightValue⟩ ::
        alignSparseCanonicalLayer zero [] rightTail
  | (leftPath, leftValue) :: leftTail, [] =>
      ⟨leftPath, leftValue, zero⟩ ::
        alignSparseCanonicalLayer zero leftTail []
  | (leftPath, leftValue) :: leftTail,
      (rightPath, rightValue) :: rightTail =>
      match compareCanonicalPath leftPath rightPath with
      | .lt =>
          ⟨leftPath, leftValue, zero⟩ ::
            alignSparseCanonicalLayer zero leftTail
              ((rightPath, rightValue) :: rightTail)
      | .eq =>
          ⟨leftPath, leftValue, rightValue⟩ ::
            alignSparseCanonicalLayer zero leftTail rightTail
      | .gt =>
          ⟨rightPath, zero, rightValue⟩ ::
            alignSparseCanonicalLayer zero
              ((leftPath, leftValue) :: leftTail) rightTail
termination_by left right => left.length + right.length

@[simp] theorem alignSparseCanonicalLayer_addresses_left_empty
    {α : Type*} (zero : α) : ∀ right : List (List ℕ × α),
    (alignSparseCanonicalLayer zero [] right).map
        AlignedSparseCanonicalEntry.address = right.map Prod.fst
  | [] => by simp [alignSparseCanonicalLayer]
  | (_, _) :: right => by
      simp [alignSparseCanonicalLayer,
        alignSparseCanonicalLayer_addresses_left_empty zero right]

@[simp] theorem alignSparseCanonicalLayer_addresses_right_empty
    {α : Type*} (zero : α) : ∀ left : List (List ℕ × α),
    (alignSparseCanonicalLayer zero left []).map
        AlignedSparseCanonicalEntry.address = left.map Prod.fst
  | [] => by simp [alignSparseCanonicalLayer]
  | (_, _) :: left => by
      simp [alignSparseCanonicalLayer,
        alignSparseCanonicalLayer_addresses_right_empty zero left]

/-- The aligned address support is exactly the union of the two sparse supports. -/
theorem mem_alignSparseCanonicalLayer_addresses
    {α : Type*} (zero : α) (address : List ℕ) :
    ∀ left right : List (List ℕ × α),
    address ∈ (alignSparseCanonicalLayer zero left right).map
        AlignedSparseCanonicalEntry.address ↔
      address ∈ left.map Prod.fst ∨ address ∈ right.map Prod.fst
  | [], [] => by simp [alignSparseCanonicalLayer]
  | [], rightHead :: right => by simp
  | leftHead :: left, [] => by simp
  | (leftPath, leftValue) :: leftTail,
      (rightPath, rightValue) :: rightTail => by
      cases compared : compareCanonicalPath leftPath rightPath with
      | lt =>
          rw [alignSparseCanonicalLayer]
          simp only [compared, List.map_cons, List.mem_cons]
          rw [mem_alignSparseCanonicalLayer_addresses zero address leftTail
            ((rightPath, rightValue) :: rightTail)]
          simp only [List.map_cons, List.mem_cons]
          aesop
      | gt =>
          rw [alignSparseCanonicalLayer]
          simp only [compared, List.map_cons, List.mem_cons]
          rw [mem_alignSparseCanonicalLayer_addresses zero address
            ((leftPath, leftValue) :: leftTail) rightTail]
          simp only [List.map_cons, List.mem_cons]
          aesop
      | eq =>
          have pathsEqual := (compareCanonicalPath_eq_iff leftPath rightPath).mp compared
          subst rightPath
          rw [alignSparseCanonicalLayer]
          simp only [compared, List.map_cons, List.mem_cons]
          rw [mem_alignSparseCanonicalLayer_addresses zero address leftTail rightTail]
          aesop

/-- The structural path comparator is precisely Lean's strict lexicographic list order. -/
theorem compareCanonicalPath_eq_lt_iff : ∀ left right : List ℕ,
    compareCanonicalPath left right = .lt ↔ left < right
  | [], [] => by simp [compareCanonicalPath, List.compareLex]
  | [], _ :: _ => by simp [compareCanonicalPath, List.compareLex]
  | _ :: _, [] => by simp [compareCanonicalPath, List.compareLex]
  | leftHead :: left, rightHead :: right => by
      simp only [compareCanonicalPath, List.compareLex]
      rcases lt_trichotomy leftHead rightHead with less | equal | greater
      · have compared : compare leftHead rightHead = .lt := Nat.compare_eq_lt.mpr less
        rw [compared, List.cons_lt_cons_iff]
        simp [less]
      · subst rightHead
        have headEqual : compare leftHead leftHead = .eq := by simp
        rw [headEqual, List.cons_lt_cons_self]
        simpa [compareCanonicalPath] using
          compareCanonicalPath_eq_lt_iff left right
      · have compared : compare leftHead rightHead = .gt := Nat.compare_eq_gt.mpr greater
        rw [compared, List.cons_lt_cons_iff]
        simp [not_lt_of_ge greater.le, ne_of_gt greater]

/-- Merging two strictly path-ordered sparse layers preserves strict path order. -/
theorem alignSparseCanonicalLayer_addresses_pairwise
    {α : Type*} (zero : α) :
    ∀ left right : List (List ℕ × α),
    (left.map Prod.fst).Pairwise (fun first second => first < second) →
    (right.map Prod.fst).Pairwise (fun first second => first < second) →
    ((alignSparseCanonicalLayer zero left right).map
      AlignedSparseCanonicalEntry.address).Pairwise
        (fun first second => first < second)
  | [], right, _, rightOrdered => by
      rw [alignSparseCanonicalLayer_addresses_left_empty]
      exact rightOrdered
  | left, [], leftOrdered, _ => by
      rw [alignSparseCanonicalLayer_addresses_right_empty]
      exact leftOrdered
  | (leftPath, leftValue) :: leftTail,
      (rightPath, rightValue) :: rightTail, leftOrdered, rightOrdered => by
      have leftParts := List.pairwise_cons.mp leftOrdered
      have rightParts := List.pairwise_cons.mp rightOrdered
      cases compared : compareCanonicalPath leftPath rightPath with
      | lt =>
          have cross : leftPath < rightPath := by
            exact (compareCanonicalPath_eq_lt_iff leftPath rightPath).mp compared
          rw [alignSparseCanonicalLayer]
          simp only [compared, List.map_cons, List.pairwise_cons]
          constructor
          · intro address present
            have support := (mem_alignSparseCanonicalLayer_addresses
              zero address leftTail ((rightPath, rightValue) :: rightTail)).mp present
            rcases support with leftPresent | rightPresent
            · exact leftParts.1 address leftPresent
            · simp only [List.map_cons, List.mem_cons] at rightPresent
              rcases rightPresent with rfl | rightTailPresent
              · exact cross
              · exact cross.trans (rightParts.1 address rightTailPresent)
          · exact alignSparseCanonicalLayer_addresses_pairwise zero leftTail
              ((rightPath, rightValue) :: rightTail) leftParts.2 rightOrdered
      | gt =>
          have cross : rightPath < leftPath := by
            have reverse : compareCanonicalPath rightPath leftPath = .lt := by
              have swapped : compareCanonicalPath rightPath leftPath =
                  (compareCanonicalPath leftPath rightPath).swap := by
                change List.compareLex compare rightPath leftPath =
                  (List.compareLex compare leftPath rightPath).swap
                exact Std.OrientedCmp.eq_swap
                  (cmp := List.compareLex compare) (a := rightPath) (b := leftPath)
              rw [swapped, compared]
              rfl
            exact (compareCanonicalPath_eq_lt_iff rightPath leftPath).mp reverse
          rw [alignSparseCanonicalLayer]
          simp only [compared, List.map_cons, List.pairwise_cons]
          constructor
          · intro address present
            have support := (mem_alignSparseCanonicalLayer_addresses
              zero address ((leftPath, leftValue) :: leftTail) rightTail).mp present
            rcases support with leftPresent | rightPresent
            · simp only [List.map_cons, List.mem_cons] at leftPresent
              rcases leftPresent with rfl | leftTailPresent
              · exact cross
              · exact cross.trans (leftParts.1 address leftTailPresent)
            · exact rightParts.1 address rightPresent
          · exact alignSparseCanonicalLayer_addresses_pairwise zero
              ((leftPath, leftValue) :: leftTail) rightTail leftOrdered rightParts.2
      | eq =>
          have pathsEqual := (compareCanonicalPath_eq_iff leftPath rightPath).mp compared
          subst rightPath
          rw [alignSparseCanonicalLayer]
          simp only [compared, List.map_cons, List.pairwise_cons]
          constructor
          · intro address present
            have support := (mem_alignSparseCanonicalLayer_addresses
              zero address leftTail rightTail).mp present
            rcases support with leftPresent | rightPresent
            · exact leftParts.1 address leftPresent
            · exact rightParts.1 address rightPresent
          · exact alignSparseCanonicalLayer_addresses_pairwise zero leftTail rightTail
              leftParts.2 rightParts.2

/-- Every left sparse entry is retained with its value in the aligned layer. -/
theorem exists_mem_alignSparseCanonicalLayer_of_mem_left
    {alpha : Type*} (zero : alpha) (target : List ℕ × alpha) :
    ∀ left right : List (List ℕ × alpha), target ∈ left →
      ∃ entry, entry ∈ alignSparseCanonicalLayer zero left right ∧
        entry.address = target.1 ∧ entry.left = target.2
  | [], _, present => by simp at present
  | leftHead :: leftTail, [], present => by
      rcases leftHead with ⟨leftPath, leftValue⟩
      rcases List.mem_cons.mp present with rfl | tailPresent
      · refine ⟨⟨leftPath, leftValue, zero⟩, ?_, rfl, rfl⟩
        rw [alignSparseCanonicalLayer]
        exact List.mem_cons_self
      · obtain ⟨entry, entryPresent, addressEq, valueEq⟩ :=
          exists_mem_alignSparseCanonicalLayer_of_mem_left
            zero target leftTail [] tailPresent
        refine ⟨entry, ?_, addressEq, valueEq⟩
        rw [alignSparseCanonicalLayer]
        exact List.mem_cons_of_mem _ entryPresent
  | leftHead :: leftTail, rightHead :: rightTail, present => by
      rcases leftHead with ⟨leftPath, leftValue⟩
      rcases rightHead with ⟨rightPath, rightValue⟩
      cases compared : compareCanonicalPath leftPath rightPath with
      | lt =>
          rcases List.mem_cons.mp present with head | tailPresent
          · subst target
            exact ⟨⟨leftPath, leftValue, zero⟩,
              by simp [alignSparseCanonicalLayer, compared], rfl, rfl⟩
          · obtain ⟨entry, entryPresent, addressEq, valueEq⟩ :=
              exists_mem_alignSparseCanonicalLayer_of_mem_left zero target leftTail
                ((rightPath, rightValue) :: rightTail) tailPresent
            exact ⟨entry, by simp [alignSparseCanonicalLayer, compared, entryPresent],
              addressEq, valueEq⟩
      | eq =>
          rcases List.mem_cons.mp present with head | tailPresent
          · subst target
            exact ⟨⟨leftPath, leftValue, rightValue⟩,
              by simp [alignSparseCanonicalLayer, compared], rfl, rfl⟩
          · obtain ⟨entry, entryPresent, addressEq, valueEq⟩ :=
              exists_mem_alignSparseCanonicalLayer_of_mem_left
                zero target leftTail rightTail tailPresent
            exact ⟨entry, by simp [alignSparseCanonicalLayer, compared, entryPresent],
              addressEq, valueEq⟩
      | gt =>
          obtain ⟨entry, entryPresent, addressEq, valueEq⟩ :=
            exists_mem_alignSparseCanonicalLayer_of_mem_left zero target
              ((leftPath, leftValue) :: leftTail) rightTail present
          exact ⟨entry, by simp [alignSparseCanonicalLayer, compared, entryPresent],
            addressEq, valueEq⟩

/-- Every right sparse entry is retained with its value in the aligned layer. -/
theorem exists_mem_alignSparseCanonicalLayer_of_mem_right
    {alpha : Type*} (zero : alpha) (target : List ℕ × alpha) :
    ∀ left right : List (List ℕ × alpha), target ∈ right →
      ∃ entry, entry ∈ alignSparseCanonicalLayer zero left right ∧
        entry.address = target.1 ∧ entry.right = target.2
  | [], [], present => by simp at present
  | [], rightHead :: rightTail, present => by
      rcases rightHead with ⟨rightPath, rightValue⟩
      rcases List.mem_cons.mp present with rfl | tailPresent
      · refine ⟨⟨rightPath, zero, rightValue⟩, ?_, rfl, rfl⟩
        rw [alignSparseCanonicalLayer]
        exact List.mem_cons_self
      · obtain ⟨entry, entryPresent, addressEq, valueEq⟩ :=
          exists_mem_alignSparseCanonicalLayer_of_mem_right
            zero target [] rightTail tailPresent
        refine ⟨entry, ?_, addressEq, valueEq⟩
        rw [alignSparseCanonicalLayer]
        exact List.mem_cons_of_mem _ entryPresent
  | _ :: _, [], present => by simp at present
  | leftHead :: leftTail, rightHead :: rightTail, present => by
      rcases leftHead with ⟨leftPath, leftValue⟩
      rcases rightHead with ⟨rightPath, rightValue⟩
      cases compared : compareCanonicalPath leftPath rightPath with
      | lt =>
          obtain ⟨entry, entryPresent, addressEq, valueEq⟩ :=
            exists_mem_alignSparseCanonicalLayer_of_mem_right zero target leftTail
              ((rightPath, rightValue) :: rightTail) present
          exact ⟨entry, by simp [alignSparseCanonicalLayer, compared, entryPresent],
            addressEq, valueEq⟩
      | eq =>
          rcases List.mem_cons.mp present with head | tailPresent
          · subst target
            have pathsEqual := (compareCanonicalPath_eq_iff leftPath rightPath).mp compared
            subst rightPath
            exact ⟨⟨leftPath, leftValue, rightValue⟩,
              by simp [alignSparseCanonicalLayer, compared], rfl, rfl⟩
          · obtain ⟨entry, entryPresent, addressEq, valueEq⟩ :=
              exists_mem_alignSparseCanonicalLayer_of_mem_right
                zero target leftTail rightTail tailPresent
            exact ⟨entry, by simp [alignSparseCanonicalLayer, compared, entryPresent],
              addressEq, valueEq⟩
      | gt =>
          rcases List.mem_cons.mp present with head | tailPresent
          · subst target
            exact ⟨⟨rightPath, zero, rightValue⟩,
              by simp [alignSparseCanonicalLayer, compared], rfl, rfl⟩
          · obtain ⟨entry, entryPresent, addressEq, valueEq⟩ :=
              exists_mem_alignSparseCanonicalLayer_of_mem_right zero target
                ((leftPath, leftValue) :: leftTail) rightTail tailPresent
            exact ⟨entry, by simp [alignSparseCanonicalLayer, compared, entryPresent],
              addressEq, valueEq⟩

/-- An aligned address absent from the left sparse support receives the left zero value. -/
theorem AlignedSparseCanonicalEntry.left_eq_zero_of_not_mem
    {alpha : Type*} (zero : alpha) : ∀ left right : List (List ℕ × alpha),
    ∀ entry, entry ∈ alignSparseCanonicalLayer zero left right →
      entry.address ∉ left.map Prod.fst → entry.left = zero
  | [], [], entry, present, _ => by simp [alignSparseCanonicalLayer] at present
  | [], (rightPath, rightValue) :: rightTail, entry, present, _ => by
      rw [alignSparseCanonicalLayer] at present
      rcases List.mem_cons.mp present with rfl | tailPresent
      · rfl
      · exact AlignedSparseCanonicalEntry.left_eq_zero_of_not_mem
          zero [] rightTail entry tailPresent (by simp)
  | leftHead :: leftTail, [], entry, present, absent => by
      rcases leftHead with ⟨leftPath, leftValue⟩
      rw [alignSparseCanonicalLayer] at present
      rcases List.mem_cons.mp present with rfl | tailPresent
      · exact (absent (by simp)).elim
      · exact AlignedSparseCanonicalEntry.left_eq_zero_of_not_mem zero leftTail []
          entry tailPresent (by
            intro tailMember
            exact absent (by simp [tailMember]))
  | (leftPath, leftValue) :: leftTail,
      (rightPath, rightValue) :: rightTail, entry, present, absent => by
      cases compared : compareCanonicalPath leftPath rightPath with
      | lt =>
          simp only [alignSparseCanonicalLayer, compared, List.mem_cons] at present
          rcases present with rfl | tailPresent
          · exact (absent (by simp)).elim
          · exact AlignedSparseCanonicalEntry.left_eq_zero_of_not_mem zero leftTail
              ((rightPath, rightValue) :: rightTail) entry tailPresent (by
                intro tailMember
                exact absent (by simp [tailMember]))
      | eq =>
          simp only [alignSparseCanonicalLayer, compared, List.mem_cons] at present
          rcases present with rfl | tailPresent
          · exact (absent (by simp)).elim
          · exact AlignedSparseCanonicalEntry.left_eq_zero_of_not_mem
              zero leftTail rightTail entry tailPresent (by
                intro tailMember
                exact absent (by simp [tailMember]))
      | gt =>
          simp only [alignSparseCanonicalLayer, compared, List.mem_cons] at present
          rcases present with rfl | tailPresent
          · rfl
          · exact AlignedSparseCanonicalEntry.left_eq_zero_of_not_mem zero
              ((leftPath, leftValue) :: leftTail) rightTail entry tailPresent absent

/-- An aligned address absent from the right sparse support receives the right zero value. -/
theorem AlignedSparseCanonicalEntry.right_eq_zero_of_not_mem
    {alpha : Type*} (zero : alpha) : ∀ left right : List (List ℕ × alpha),
    ∀ entry, entry ∈ alignSparseCanonicalLayer zero left right →
      entry.address ∉ right.map Prod.fst → entry.right = zero
  | [], [], entry, present, _ => by simp [alignSparseCanonicalLayer] at present
  | (leftPath, leftValue) :: leftTail, [], entry, present, _ => by
      rw [alignSparseCanonicalLayer] at present
      rcases List.mem_cons.mp present with rfl | tailPresent
      · rfl
      · exact AlignedSparseCanonicalEntry.right_eq_zero_of_not_mem
          zero leftTail [] entry tailPresent (by simp)
  | [], rightHead :: rightTail, entry, present, absent => by
      rcases rightHead with ⟨rightPath, rightValue⟩
      rw [alignSparseCanonicalLayer] at present
      rcases List.mem_cons.mp present with rfl | tailPresent
      · exact (absent (by simp)).elim
      · exact AlignedSparseCanonicalEntry.right_eq_zero_of_not_mem zero [] rightTail
          entry tailPresent (by
            intro tailMember
            exact absent (by simp [tailMember]))
  | (leftPath, leftValue) :: leftTail,
      (rightPath, rightValue) :: rightTail, entry, present, absent => by
      cases compared : compareCanonicalPath leftPath rightPath with
      | lt =>
          simp only [alignSparseCanonicalLayer, compared, List.mem_cons] at present
          rcases present with rfl | tailPresent
          · rfl
          · exact AlignedSparseCanonicalEntry.right_eq_zero_of_not_mem zero leftTail
              ((rightPath, rightValue) :: rightTail) entry tailPresent absent
      | eq =>
          simp only [alignSparseCanonicalLayer, compared, List.mem_cons] at present
          rcases present with rfl | tailPresent
          · have pathsEqual := (compareCanonicalPath_eq_iff leftPath rightPath).mp compared
            subst rightPath
            exact (absent (by simp)).elim
          · exact AlignedSparseCanonicalEntry.right_eq_zero_of_not_mem
              zero leftTail rightTail entry tailPresent (by
                intro tailMember
                exact absent (by simp [tailMember]))
      | gt =>
          simp only [alignSparseCanonicalLayer, compared, List.mem_cons] at present
          rcases present with rfl | tailPresent
          · exact (absent (by simp)).elim
          · exact AlignedSparseCanonicalEntry.right_eq_zero_of_not_mem zero
              ((leftPath, leftValue) :: leftTail) rightTail entry tailPresent
                (by
                  intro tailMember
                  exact absent (by simp [tailMember]))

/-- At an address present on the left, alignment retains exactly its sparse value. -/
theorem AlignedSparseCanonicalEntry.left_eq_of_mem
    {alpha : Type*} (zero : alpha)
    (left right : List (List ℕ × alpha))
    (leftOrdered : (left.map Prod.fst).Pairwise (fun first second => first < second))
    (rightOrdered : (right.map Prod.fst).Pairwise (fun first second => first < second))
    (entry : AlignedSparseCanonicalEntry alpha)
    (entryPresent : entry ∈ alignSparseCanonicalLayer zero left right)
    (source : List ℕ × alpha) (sourcePresent : source ∈ left)
    (sameAddress : entry.address = source.1) :
    entry.left = source.2 := by
  obtain ⟨witness, witnessPresent, witnessAddress, witnessValue⟩ :=
    exists_mem_alignSparseCanonicalLayer_of_mem_left zero source left right sourcePresent
  have addressOrdered := alignSparseCanonicalLayer_addresses_pairwise
    zero left right leftOrdered rightOrdered
  have addressNodup : ((alignSparseCanonicalLayer zero left right).map
      AlignedSparseCanonicalEntry.address).Nodup :=
    addressOrdered.imp fun {first second} less => ne_of_lt less
  have entryEq : entry = witness :=
    List.inj_on_of_nodup_map addressNodup entryPresent witnessPresent
      (sameAddress.trans witnessAddress.symm)
  subst witness
  exact witnessValue

/-- At an address present on the right, alignment retains exactly its sparse value. -/
theorem AlignedSparseCanonicalEntry.right_eq_of_mem
    {alpha : Type*} (zero : alpha)
    (left right : List (List ℕ × alpha))
    (leftOrdered : (left.map Prod.fst).Pairwise (fun first second => first < second))
    (rightOrdered : (right.map Prod.fst).Pairwise (fun first second => first < second))
    (entry : AlignedSparseCanonicalEntry alpha)
    (entryPresent : entry ∈ alignSparseCanonicalLayer zero left right)
    (source : List ℕ × alpha) (sourcePresent : source ∈ right)
    (sameAddress : entry.address = source.1) :
    entry.right = source.2 := by
  obtain ⟨witness, witnessPresent, witnessAddress, witnessValue⟩ :=
    exists_mem_alignSparseCanonicalLayer_of_mem_right zero source left right sourcePresent
  have addressOrdered := alignSparseCanonicalLayer_addresses_pairwise
    zero left right leftOrdered rightOrdered
  have addressNodup : ((alignSparseCanonicalLayer zero left right).map
      AlignedSparseCanonicalEntry.address).Nodup :=
    addressOrdered.imp fun {first second} less => ne_of_lt less
  have entryEq : entry = witness :=
    List.inj_on_of_nodup_map addressNodup entryPresent witnessPresent
      (sameAddress.trans witnessAddress.symm)
  subst witness
  exact witnessValue

@[simp] theorem alignSparseCanonicalLayer_left_length_eq_right_length
    {α : Type*} (zero : α) (left right : List (List ℕ × α)) :
    ((alignSparseCanonicalLayer zero left right).map
      AlignedSparseCanonicalEntry.left).length =
    ((alignSparseCanonicalLayer zero left right).map
      AlignedSparseCanonicalEntry.right).length := by
  simp

private theorem compareCanonicalPath_reverse_lt
    {left right : List ℕ} (compared : compareCanonicalPath left right = .lt) :
    compareCanonicalPath right left = .gt := by
  have swapped : compareCanonicalPath right left =
      (compareCanonicalPath left right).swap := by
    change List.compareLex compare right left =
      (List.compareLex compare left right).swap
    exact Std.OrientedCmp.eq_swap
      (cmp := List.compareLex compare) (a := right) (b := left)
  rw [swapped, compared]
  rfl

private theorem compareCanonicalPath_reverse_gt
    {left right : List ℕ} (compared : compareCanonicalPath left right = .gt) :
    compareCanonicalPath right left = .lt := by
  have swapped : compareCanonicalPath right left =
      (compareCanonicalPath left right).swap := by
    change List.compareLex compare right left =
      (List.compareLex compare left right).swap
    exact Std.OrientedCmp.eq_swap
      (cmp := List.compareLex compare) (a := right) (b := left)
  rw [swapped, compared]
  rfl

private theorem compareSparseCanonicalEntry_of_path_lt
    {α : Type*} (compareValue : α → α → Ordering)
    (leftPath rightPath : List ℕ) (leftValue rightValue : α)
    (compared : compareCanonicalPath leftPath rightPath = .lt) :
    compareSparseCanonicalEntry compareValue (leftPath, leftValue)
      (rightPath, rightValue) = .gt := by
  have reverse := compareCanonicalPath_reverse_lt compared
  simp [compareSparseCanonicalEntry, compareLex, Ordering.byKey, flip, reverse]

private theorem compareSparseCanonicalEntry_of_path_gt
    {α : Type*} (compareValue : α → α → Ordering)
    (leftPath rightPath : List ℕ) (leftValue rightValue : α)
    (compared : compareCanonicalPath leftPath rightPath = .gt) :
    compareSparseCanonicalEntry compareValue (leftPath, leftValue)
      (rightPath, rightValue) = .lt := by
  have reverse := compareCanonicalPath_reverse_gt compared
  simp [compareSparseCanonicalEntry, compareLex, Ordering.byKey, flip, reverse]

/-- Sparse positional comparison is ordinary lexicographic comparison after zero-filling the
union of the two path supports, provided every actually present observation beats zero. -/
theorem compareSparseCanonicalLayer_eq_compareLex_aligned
    {α : Type*} (compareValue : α → α → Ordering) (zero : α)
    (zeroSelf : compareValue zero zero = .eq) :
    ∀ left right : List (List ℕ × α),
      (∀ entry, entry ∈ left → compareValue entry.2 zero = .gt) →
      (∀ entry, entry ∈ right → compareValue zero entry.2 = .lt) →
      compareSparseCanonicalLayer compareValue left right =
        List.compareLex compareValue
          ((alignSparseCanonicalLayer zero left right).map
            AlignedSparseCanonicalEntry.left)
          ((alignSparseCanonicalLayer zero left right).map
            AlignedSparseCanonicalEntry.right)
  | [], [], _, _ => by
      unfold compareSparseCanonicalLayer alignSparseCanonicalLayer
      simp only [List.compareLex, List.map]
  | [], (rightPath, rightValue) :: rightTail, _, rightPositive => by
      have headPositive := rightPositive (rightPath, rightValue) (by simp)
      simp only [compareSparseCanonicalLayer, List.compareLex,
        alignSparseCanonicalLayer, List.map_cons]
      rw [headPositive]
  | (leftPath, leftValue) :: leftTail, [], leftPositive, _ => by
      have headPositive := leftPositive (leftPath, leftValue) (by simp)
      simp only [compareSparseCanonicalLayer, List.compareLex,
        alignSparseCanonicalLayer, List.map_cons]
      rw [headPositive]
  | (leftPath, leftValue) :: leftTail,
      (rightPath, rightValue) :: rightTail, leftPositive, rightPositive => by
      have leftHeadPositive := leftPositive (leftPath, leftValue) (by simp)
      have rightHeadPositive := rightPositive (rightPath, rightValue) (by simp)
      have leftTailPositive : ∀ entry, entry ∈ leftTail →
          compareValue entry.2 zero = .gt := by
        intro entry present
        exact leftPositive entry (by simp [present])
      have rightTailPositive : ∀ entry, entry ∈ rightTail →
          compareValue zero entry.2 = .lt := by
        intro entry present
        exact rightPositive entry (by simp [present])
      cases pathCompared : compareCanonicalPath leftPath rightPath with
      | lt =>
          have entryCompared := compareSparseCanonicalEntry_of_path_lt compareValue
            leftPath rightPath leftValue rightValue pathCompared
          simp only [compareSparseCanonicalLayer, List.compareLex, entryCompared,
            alignSparseCanonicalLayer, pathCompared, List.map_cons]
          rw [leftHeadPositive]
      | gt =>
          have entryCompared := compareSparseCanonicalEntry_of_path_gt compareValue
            leftPath rightPath leftValue rightValue pathCompared
          simp only [compareSparseCanonicalLayer, List.compareLex, entryCompared,
            alignSparseCanonicalLayer, pathCompared, List.map_cons]
          rw [rightHeadPositive]
      | eq =>
          have pathsEqual := (compareCanonicalPath_eq_iff leftPath rightPath).mp pathCompared
          subst rightPath
          have recursive := compareSparseCanonicalLayer_eq_compareLex_aligned
            compareValue zero zeroSelf leftTail rightTail leftTailPositive rightTailPositive
          simp only [compareSparseCanonicalLayer, List.compareLex,
            alignSparseCanonicalLayer, pathCompared, List.map_cons]
          rw [compareSparseCanonicalEntry_samePath]
          cases valuesCompared : compareValue leftValue rightValue with
          | lt => rfl
          | gt => rfl
          | eq => simpa [valuesCompared] using recursive

/-- Zero-fill corresponding spheres and retain the union address schedule sphere by sphere. -/
def alignSparseCanonicalLayers {α : Type*} (zero : α) :
    (left right : List (List (List ℕ × α))) →
      List (List (AlignedSparseCanonicalEntry α))
  | [], [] => []
  | [], rightLayer :: right =>
      alignSparseCanonicalLayer zero [] rightLayer ::
        alignSparseCanonicalLayers zero [] right
  | leftLayer :: left, [] =>
      alignSparseCanonicalLayer zero leftLayer [] ::
        alignSparseCanonicalLayers zero left []
  | leftLayer :: left, rightLayer :: right =>
      alignSparseCanonicalLayer zero leftLayer rightLayer ::
        alignSparseCanonicalLayers zero left right

/-- Every left entry of a sparse hierarchy is retained, at the same address and value, in the
flattened aligned hierarchy. -/
theorem exists_mem_alignSparseCanonicalLayers_flatten_of_mem_left
    {alpha : Type*} (zero : alpha) (target : List ℕ × alpha) :
    ∀ left right : List (List (List ℕ × alpha)), target ∈ left.flatten →
      ∃ entry, entry ∈ (alignSparseCanonicalLayers zero left right).flatten ∧
        entry.address = target.1 ∧ entry.left = target.2
  | [], _, present => by simp at present
  | leftLayer :: left, [], present => by
      simp only [List.flatten_cons, List.mem_append] at present
      rcases present with layerPresent | tailPresent
      · obtain ⟨entry, entryPresent, addressEq, valueEq⟩ :=
          exists_mem_alignSparseCanonicalLayer_of_mem_left
            zero target leftLayer [] layerPresent
        refine ⟨entry, ?_, addressEq, valueEq⟩
        simp [alignSparseCanonicalLayers, entryPresent]
      · obtain ⟨entry, entryPresent, addressEq, valueEq⟩ :=
          exists_mem_alignSparseCanonicalLayers_flatten_of_mem_left
            zero target left [] tailPresent
        refine ⟨entry, ?_, addressEq, valueEq⟩
        simp [alignSparseCanonicalLayers, entryPresent]
  | leftLayer :: left, rightLayer :: right, present => by
      simp only [List.flatten_cons, List.mem_append] at present
      rcases present with layerPresent | tailPresent
      · obtain ⟨entry, entryPresent, addressEq, valueEq⟩ :=
          exists_mem_alignSparseCanonicalLayer_of_mem_left
            zero target leftLayer rightLayer layerPresent
        refine ⟨entry, ?_, addressEq, valueEq⟩
        simp [alignSparseCanonicalLayers, entryPresent]
      · obtain ⟨entry, entryPresent, addressEq, valueEq⟩ :=
          exists_mem_alignSparseCanonicalLayers_flatten_of_mem_left
            zero target left right tailPresent
        refine ⟨entry, ?_, addressEq, valueEq⟩
        simp [alignSparseCanonicalLayers, entryPresent]

/-- Every right entry of a sparse hierarchy is retained, at the same address and value, in the
flattened aligned hierarchy. -/
theorem exists_mem_alignSparseCanonicalLayers_flatten_of_mem_right
    {alpha : Type*} (zero : alpha) (target : List ℕ × alpha) :
    ∀ left right : List (List (List ℕ × alpha)), target ∈ right.flatten →
      ∃ entry, entry ∈ (alignSparseCanonicalLayers zero left right).flatten ∧
        entry.address = target.1 ∧ entry.right = target.2
  | [], [], present => by simp at present
  | [], rightLayer :: right, present => by
      simp only [List.flatten_cons, List.mem_append] at present
      rcases present with layerPresent | tailPresent
      · obtain ⟨entry, entryPresent, addressEq, valueEq⟩ :=
          exists_mem_alignSparseCanonicalLayer_of_mem_right
            zero target [] rightLayer layerPresent
        refine ⟨entry, ?_, addressEq, valueEq⟩
        simp [alignSparseCanonicalLayers, entryPresent]
      · obtain ⟨entry, entryPresent, addressEq, valueEq⟩ :=
          exists_mem_alignSparseCanonicalLayers_flatten_of_mem_right
            zero target [] right tailPresent
        refine ⟨entry, ?_, addressEq, valueEq⟩
        simp [alignSparseCanonicalLayers, entryPresent]
  | _ :: _, [], present => by simp at present
  | leftLayer :: left, rightLayer :: right, present => by
      simp only [List.flatten_cons, List.mem_append] at present
      rcases present with layerPresent | tailPresent
      · obtain ⟨entry, entryPresent, addressEq, valueEq⟩ :=
          exists_mem_alignSparseCanonicalLayer_of_mem_right
            zero target leftLayer rightLayer layerPresent
        refine ⟨entry, ?_, addressEq, valueEq⟩
        simp [alignSparseCanonicalLayers, entryPresent]
      · obtain ⟨entry, entryPresent, addressEq, valueEq⟩ :=
          exists_mem_alignSparseCanonicalLayers_flatten_of_mem_right
            zero target left right tailPresent
        refine ⟨entry, ?_, addressEq, valueEq⟩
        simp [alignSparseCanonicalLayers, entryPresent]

/-- The flattened aligned schedule is exactly the union of the two flattened sparse supports. -/
theorem mem_alignSparseCanonicalLayers_flatten_addresses
    {alpha : Type*} (zero : alpha) (address : List ℕ) :
    ∀ left right : List (List (List ℕ × alpha)),
    address ∈ (alignSparseCanonicalLayers zero left right).flatten.map
        AlignedSparseCanonicalEntry.address ↔
      address ∈ left.flatten.map Prod.fst ∨ address ∈ right.flatten.map Prod.fst
  | [], [] => by simp [alignSparseCanonicalLayers]
  | [], rightLayer :: right => by
      simp only [alignSparseCanonicalLayers, List.flatten_cons, List.map_append,
        List.mem_append, List.flatten_nil, List.map_nil, List.not_mem_nil, false_or]
      rw [mem_alignSparseCanonicalLayer_addresses,
        mem_alignSparseCanonicalLayers_flatten_addresses zero address [] right]
      simp
  | leftLayer :: left, [] => by
      simp only [alignSparseCanonicalLayers, List.flatten_cons, List.map_append,
        List.mem_append, List.flatten_nil, List.map_nil, List.not_mem_nil, or_false]
      rw [mem_alignSparseCanonicalLayer_addresses,
        mem_alignSparseCanonicalLayers_flatten_addresses zero address left []]
      simp
  | leftLayer :: left, rightLayer :: right => by
      simp only [alignSparseCanonicalLayers, List.flatten_cons, List.map_append,
        List.mem_append]
      rw [mem_alignSparseCanonicalLayer_addresses,
        mem_alignSparseCanonicalLayers_flatten_addresses zero address left right]
      aesop

/-- Outside the flattened left support, every aligned left projection is the zero filler. -/
theorem AlignedSparseCanonicalEntry.left_eq_zero_of_not_mem_flatten
    {alpha : Type*} (zero : alpha) :
    ∀ left right : List (List (List ℕ × alpha)),
    ∀ entry, entry ∈ (alignSparseCanonicalLayers zero left right).flatten →
      entry.address ∉ left.flatten.map Prod.fst → entry.left = zero
  | [], [], entry, present, _ => by simp [alignSparseCanonicalLayers] at present
  | [], rightLayer :: right, entry, present, absent => by
      simp only [alignSparseCanonicalLayers, List.flatten_cons,
        List.mem_append] at present
      rcases present with layerPresent | tailPresent
      · exact entry.left_eq_zero_of_not_mem zero [] rightLayer layerPresent (by simp)
      · exact entry.left_eq_zero_of_not_mem_flatten zero [] right tailPresent (by simp)
  | leftLayer :: left, [], entry, present, absent => by
      simp only [alignSparseCanonicalLayers, List.flatten_cons,
        List.mem_append] at present
      rcases present with layerPresent | tailPresent
      · exact entry.left_eq_zero_of_not_mem zero leftLayer [] layerPresent (by
          intro layerAddress
          apply absent
          simp only [List.flatten_cons, List.map_append, List.mem_append]
          exact Or.inl layerAddress)
      · exact entry.left_eq_zero_of_not_mem_flatten zero left [] tailPresent (by
          intro tailAddress
          apply absent
          simp only [List.flatten_cons, List.map_append, List.mem_append]
          exact Or.inr tailAddress)
  | leftLayer :: left, rightLayer :: right, entry, present, absent => by
      simp only [alignSparseCanonicalLayers, List.flatten_cons,
        List.mem_append] at present
      rcases present with layerPresent | tailPresent
      · exact entry.left_eq_zero_of_not_mem zero leftLayer rightLayer layerPresent (by
          intro layerAddress
          apply absent
          simp only [List.flatten_cons, List.map_append, List.mem_append]
          exact Or.inl layerAddress)
      · exact entry.left_eq_zero_of_not_mem_flatten zero left right tailPresent (by
          intro tailAddress
          apply absent
          simp only [List.flatten_cons, List.map_append, List.mem_append]
          exact Or.inr tailAddress)

/-- Outside the flattened right support, every aligned right projection is the zero filler. -/
theorem AlignedSparseCanonicalEntry.right_eq_zero_of_not_mem_flatten
    {alpha : Type*} (zero : alpha) :
    ∀ left right : List (List (List ℕ × alpha)),
    ∀ entry, entry ∈ (alignSparseCanonicalLayers zero left right).flatten →
      entry.address ∉ right.flatten.map Prod.fst → entry.right = zero
  | [], [], entry, present, _ => by simp [alignSparseCanonicalLayers] at present
  | [], rightLayer :: right, entry, present, absent => by
      simp only [alignSparseCanonicalLayers, List.flatten_cons,
        List.mem_append] at present
      rcases present with layerPresent | tailPresent
      · exact entry.right_eq_zero_of_not_mem zero [] rightLayer layerPresent (by
          intro layerAddress
          apply absent
          simp only [List.flatten_cons, List.map_append, List.mem_append]
          exact Or.inl layerAddress)
      · exact entry.right_eq_zero_of_not_mem_flatten zero [] right tailPresent (by
          intro tailAddress
          apply absent
          simp only [List.flatten_cons, List.map_append, List.mem_append]
          exact Or.inr tailAddress)
  | leftLayer :: left, [], entry, present, _ => by
      simp only [alignSparseCanonicalLayers, List.flatten_cons,
        List.mem_append] at present
      rcases present with layerPresent | tailPresent
      · exact entry.right_eq_zero_of_not_mem zero leftLayer [] layerPresent (by simp)
      · exact entry.right_eq_zero_of_not_mem_flatten zero left [] tailPresent (by simp)
  | leftLayer :: left, rightLayer :: right, entry, present, absent => by
      simp only [alignSparseCanonicalLayers, List.flatten_cons,
        List.mem_append] at present
      rcases present with layerPresent | tailPresent
      · exact entry.right_eq_zero_of_not_mem zero leftLayer rightLayer layerPresent (by
          intro layerAddress
          apply absent
          simp only [List.flatten_cons, List.map_append, List.mem_append]
          exact Or.inl layerAddress)
      · exact entry.right_eq_zero_of_not_mem_flatten zero left right tailPresent (by
          intro tailAddress
          apply absent
          simp only [List.flatten_cons, List.map_append, List.mem_append]
          exact Or.inr tailAddress)

/-- Global aligned-address uniqueness upgrades left support membership to exact value recovery. -/
theorem AlignedSparseCanonicalEntry.left_eq_of_mem_flatten
    {alpha : Type*} (zero : alpha)
    (left right : List (List (List ℕ × alpha)))
    (addressesNodup : ((alignSparseCanonicalLayers zero left right).flatten.map
      AlignedSparseCanonicalEntry.address).Nodup)
    (entry : AlignedSparseCanonicalEntry alpha)
    (entryPresent : entry ∈ (alignSparseCanonicalLayers zero left right).flatten)
    (source : List ℕ × alpha) (sourcePresent : source ∈ left.flatten)
    (sameAddress : entry.address = source.1) : entry.left = source.2 := by
  obtain ⟨witness, witnessPresent, witnessAddress, witnessValue⟩ :=
    exists_mem_alignSparseCanonicalLayers_flatten_of_mem_left
      zero source left right sourcePresent
  have entryEq : entry = witness :=
    List.inj_on_of_nodup_map addressesNodup entryPresent witnessPresent
      (sameAddress.trans witnessAddress.symm)
  subst witness
  exact witnessValue

/-- Global aligned-address uniqueness upgrades right support membership to exact value recovery. -/
theorem AlignedSparseCanonicalEntry.right_eq_of_mem_flatten
    {alpha : Type*} (zero : alpha)
    (left right : List (List (List ℕ × alpha)))
    (addressesNodup : ((alignSparseCanonicalLayers zero left right).flatten.map
      AlignedSparseCanonicalEntry.address).Nodup)
    (entry : AlignedSparseCanonicalEntry alpha)
    (entryPresent : entry ∈ (alignSparseCanonicalLayers zero left right).flatten)
    (source : List ℕ × alpha) (sourcePresent : source ∈ right.flatten)
    (sameAddress : entry.address = source.1) : entry.right = source.2 := by
  obtain ⟨witness, witnessPresent, witnessAddress, witnessValue⟩ :=
    exists_mem_alignSparseCanonicalLayers_flatten_of_mem_right
      zero source left right sourcePresent
  have entryEq : entry = witness :=
    List.inj_on_of_nodup_map addressesNodup entryPresent witnessPresent
      (sameAddress.trans witnessAddress.symm)
  subst witness
  exact witnessValue

/-- The two zero-filled projections of an aligned sparse hierarchy have identical length. -/
theorem alignSparseCanonicalLayers_flattened_length_eq
    {α : Type*} (zero : α)
    (left right : List (List (List ℕ × α))) :
    ((alignSparseCanonicalLayers zero left right).flatten.map
      AlignedSparseCanonicalEntry.left).length =
    ((alignSparseCanonicalLayers zero left right).flatten.map
      AlignedSparseCanonicalEntry.right).length := by
  induction left generalizing right with
  | nil =>
      induction right with
      | nil => simp [alignSparseCanonicalLayers]
      | cons rightLayer right inductionHypothesis =>
          simp only [alignSparseCanonicalLayers, List.flatten_cons,
            List.map_append, List.length_append]
          rw [alignSparseCanonicalLayer_left_length_eq_right_length,
            inductionHypothesis]
  | cons leftLayer left inductionHypothesis =>
      cases right with
      | nil =>
          simp only [alignSparseCanonicalLayers, List.flatten_cons,
            List.map_append, List.length_append]
          rw [alignSparseCanonicalLayer_left_length_eq_right_length,
            inductionHypothesis []]
      | cons rightLayer right =>
          simp only [alignSparseCanonicalLayers, List.flatten_cons,
            List.map_append, List.length_append]
          rw [alignSparseCanonicalLayer_left_length_eq_right_length,
            inductionHypothesis right]

/-- Nested sphere-major sparse comparison is lexicographic comparison of the flattened
zero-filled union schedule. -/
theorem compareSparseCanonicalLayers_eq_compareLex_aligned
    {α : Type*} (compareValue : α → α → Ordering) (zero : α)
    (zeroSelf : compareValue zero zero = .eq) :
    ∀ left right : List (List (List ℕ × α)),
      (∀ layer, layer ∈ left → layer ≠ []) →
      (∀ layer, layer ∈ right → layer ≠ []) →
      (∀ layer, layer ∈ left → ∀ entry, entry ∈ layer →
        compareValue entry.2 zero = .gt) →
      (∀ layer, layer ∈ right → ∀ entry, entry ∈ layer →
        compareValue zero entry.2 = .lt) →
      compareSparseCanonicalLayers compareValue left right =
        List.compareLex compareValue
          ((alignSparseCanonicalLayers zero left right).flatten.map
            AlignedSparseCanonicalEntry.left)
          ((alignSparseCanonicalLayers zero left right).flatten.map
            AlignedSparseCanonicalEntry.right)
  | [], [], _, _, _, _ => by
      unfold compareSparseCanonicalLayers alignSparseCanonicalLayers
      simp only [List.compareLex, List.flatten_nil, List.map]
  | [], rightLayer :: right, _, rightNonempty, _, rightPositive => by
      have layerCompared := compareSparseCanonicalLayer_eq_compareLex_aligned
        compareValue zero zeroSelf [] rightLayer
        (by simp) (fun entry present => rightPositive rightLayer (by simp) entry present)
      have layerLength := alignSparseCanonicalLayer_left_length_eq_right_length
        zero [] rightLayer
      have recursive := compareSparseCanonicalLayers_eq_compareLex_aligned
        compareValue zero zeroSelf [] right (by simp)
        (fun layer present => rightNonempty layer (by simp [present])) (by simp)
        (fun layer present => rightPositive layer (by simp [present]))
      simp only [compareSparseCanonicalLayers, List.compareLex,
        alignSparseCanonicalLayers, List.flatten_cons, List.map_append]
      rw [compareLex_append_of_length_eq compareValue
        ((alignSparseCanonicalLayer zero [] rightLayer).map
          AlignedSparseCanonicalEntry.left)
        ((alignSparseCanonicalLayer zero [] rightLayer).map
          AlignedSparseCanonicalEntry.right)
        ((alignSparseCanonicalLayers zero [] right).flatten.map
          AlignedSparseCanonicalEntry.left)
        ((alignSparseCanonicalLayers zero [] right).flatten.map
          AlignedSparseCanonicalEntry.right) layerLength]
      rw [← layerCompared]
      have layerStrict : compareSparseCanonicalLayer compareValue [] rightLayer = .lt := by
        cases rightLayer with
        | nil => exact ((rightNonempty [] (by simp)) rfl).elim
        | cons head tail => rfl
      rw [layerStrict]
      rfl
  | leftLayer :: left, [], leftNonempty, _, leftPositive, _ => by
      have layerCompared := compareSparseCanonicalLayer_eq_compareLex_aligned
        compareValue zero zeroSelf leftLayer []
        (fun entry present => leftPositive leftLayer (by simp) entry present) (by simp)
      have layerLength := alignSparseCanonicalLayer_left_length_eq_right_length
        zero leftLayer []
      have recursive := compareSparseCanonicalLayers_eq_compareLex_aligned
        compareValue zero zeroSelf left []
        (fun layer present => leftNonempty layer (by simp [present])) (by simp)
        (fun layer present => leftPositive layer (by simp [present])) (by simp)
      simp only [compareSparseCanonicalLayers, List.compareLex,
        alignSparseCanonicalLayers, List.flatten_cons, List.map_append]
      rw [compareLex_append_of_length_eq compareValue
        ((alignSparseCanonicalLayer zero leftLayer []).map
          AlignedSparseCanonicalEntry.left)
        ((alignSparseCanonicalLayer zero leftLayer []).map
          AlignedSparseCanonicalEntry.right)
        ((alignSparseCanonicalLayers zero left []).flatten.map
          AlignedSparseCanonicalEntry.left)
        ((alignSparseCanonicalLayers zero left []).flatten.map
          AlignedSparseCanonicalEntry.right) layerLength]
      rw [← layerCompared]
      have layerStrict : compareSparseCanonicalLayer compareValue leftLayer [] = .gt := by
        cases leftLayer with
        | nil => exact ((leftNonempty [] (by simp)) rfl).elim
        | cons head tail => rfl
      rw [layerStrict]
      rfl
  | leftLayer :: left, rightLayer :: right,
      leftNonempty, rightNonempty, leftPositive, rightPositive => by
      have layerCompared := compareSparseCanonicalLayer_eq_compareLex_aligned
        compareValue zero zeroSelf leftLayer rightLayer
        (fun entry present => leftPositive leftLayer (by simp) entry present)
        (fun entry present => rightPositive rightLayer (by simp) entry present)
      have layerLength := alignSparseCanonicalLayer_left_length_eq_right_length
        zero leftLayer rightLayer
      have recursive := compareSparseCanonicalLayers_eq_compareLex_aligned
        compareValue zero zeroSelf left right
        (fun layer present => leftNonempty layer (by simp [present]))
        (fun layer present => rightNonempty layer (by simp [present]))
        (fun layer present => leftPositive layer (by simp [present]))
        (fun layer present => rightPositive layer (by simp [present]))
      simp only [compareSparseCanonicalLayers, List.compareLex,
        alignSparseCanonicalLayers, List.flatten_cons, List.map_append]
      rw [compareLex_append_of_length_eq compareValue
        ((alignSparseCanonicalLayer zero leftLayer rightLayer).map
          AlignedSparseCanonicalEntry.left)
        ((alignSparseCanonicalLayer zero leftLayer rightLayer).map
          AlignedSparseCanonicalEntry.right)
        ((alignSparseCanonicalLayers zero left right).flatten.map
          AlignedSparseCanonicalEntry.left)
        ((alignSparseCanonicalLayers zero left right).flatten.map
          AlignedSparseCanonicalEntry.right) layerLength]
      rw [← layerCompared]
      cases layerDecision : compareSparseCanonicalLayer compareValue
          leftLayer rightLayer with
      | lt => rfl
      | gt => rfl
      | eq => simpa [layerDecision] using recursive

/-! ## Semantic ordering of the zero-filled union schedule -/

/-- Generic sphere/path scheduling invariant for sparse layers. -/
structure SparseCanonicalLayersScheduledFrom {α : Type*}
    (offset : ℕ) (layers : List (List (List ℕ × α))) : Prop where
  layerOrdered : ∀ depth,
    ((layers.getD depth []).map Prod.fst).Pairwise
      (fun first second => first < second)
  depthCorrect : ∀ depth entry, entry ∈ layers.getD depth [] →
    entry.1.length = offset + depth

/-- Source scheduling is preserved by any observation projection. -/
theorem CanonicalSourceLayersScheduledFrom.map_observation
    {α : Type*} (offset : ℕ) (layers : List (List CanonicalSourceEntry))
    (scheduled : CanonicalSourceLayersScheduledFrom offset layers)
    (observe : CanonicalBranchNode → α) :
    SparseCanonicalLayersScheduledFrom offset
      (mapCanonicalSourceLayers observe layers) := by
  constructor
  · intro depth
    by_cases inRange : depth < layers.length
    · have mappedRange : depth < (mapCanonicalSourceLayers observe layers).length := by
        simpa [mapCanonicalSourceLayers] using inRange
      have ordered := scheduled.layerOrdered depth
      simpa [mapCanonicalSourceLayers, List.getD, inRange, mappedRange,
        List.map_map, Function.comp_def] using ordered
    · have mappedOut : ¬depth < (mapCanonicalSourceLayers observe layers).length := by
        simpa [mapCanonicalSourceLayers] using inRange
      simp [List.getD, mappedOut]
  · intro depth entry present
    by_cases inRange : depth < layers.length
    · have mappedRange : depth < (mapCanonicalSourceLayers observe layers).length := by
        simpa [mapCanonicalSourceLayers] using inRange
      have getMapped :
          (mapCanonicalSourceLayers observe layers).getD depth [] =
            (layers.getD depth []).map
              (fun source => (source.1, observe source.2)) := by
        simp [mapCanonicalSourceLayers, List.getD, inRange]
      rw [getMapped] at present
      simp only [List.mem_map] at present
      rcases present with ⟨source, sourcePresent, rfl⟩
      have sourcePresent' : source ∈ layers.getD depth [] := by
        simpa [List.getD, inRange] using sourcePresent
      exact scheduled.depthCorrect depth source sourcePresent'
    · have mappedOut : ¬depth < (mapCanonicalSourceLayers observe layers).length := by
        simpa [mapCanonicalSourceLayers] using inRange
      simp [List.getD, mappedOut] at present

/-- Looking up an aligned sphere is the same as aligning the two corresponding sparse spheres. -/
theorem alignSparseCanonicalLayers_getD
    {α : Type*} (zero : α) :
    ∀ depth left right,
    (alignSparseCanonicalLayers zero left right).getD depth [] =
      alignSparseCanonicalLayer zero (left.getD depth []) (right.getD depth [])
  | 0, [], [] => by simp [alignSparseCanonicalLayers, List.getD,
      alignSparseCanonicalLayer]
  | 0, [], _ :: _ => by simp [alignSparseCanonicalLayers, List.getD]
  | 0, _ :: _, [] => by simp [alignSparseCanonicalLayers, List.getD]
  | 0, _ :: _, _ :: _ => by simp [alignSparseCanonicalLayers, List.getD]
  | _ + 1, [], [] => by simp [alignSparseCanonicalLayers, List.getD,
      alignSparseCanonicalLayer]
  | depth + 1, [], _ :: right => by
      simpa [alignSparseCanonicalLayers, List.getD] using
        alignSparseCanonicalLayers_getD zero depth [] right
  | depth + 1, _ :: left, [] => by
      simpa [alignSparseCanonicalLayers, List.getD] using
        alignSparseCanonicalLayers_getD zero depth left []
  | depth + 1, _ :: left, _ :: right => by
      simpa [alignSparseCanonicalLayers, List.getD] using
        alignSparseCanonicalLayers_getD zero depth left right

/-- Aligned zero-filled layers inherit strict within-sphere path ordering and exact sphere depth. -/
structure AlignedSparseCanonicalLayersScheduledFrom {α : Type*}
    (offset : ℕ) (layers : List (List (AlignedSparseCanonicalEntry α))) : Prop where
  layerOrdered : ∀ depth,
    ((layers.getD depth []).map AlignedSparseCanonicalEntry.address).Pairwise
      (fun first second => first < second)
  depthCorrect : ∀ depth entry, entry ∈ layers.getD depth [] →
    entry.address.length = offset + depth

/-- Aligning two sparse schedules beginning at the same sphere preserves the schedule invariant. -/
theorem SparseCanonicalLayersScheduledFrom.align
    {α : Type*} (zero : α) (offset : ℕ)
    (left right : List (List (List ℕ × α)))
    (leftScheduled : SparseCanonicalLayersScheduledFrom offset left)
    (rightScheduled : SparseCanonicalLayersScheduledFrom offset right) :
    AlignedSparseCanonicalLayersScheduledFrom offset
      (alignSparseCanonicalLayers zero left right) := by
  constructor
  · intro depth
    rw [alignSparseCanonicalLayers_getD]
    exact alignSparseCanonicalLayer_addresses_pairwise zero
      (left.getD depth []) (right.getD depth [])
      (leftScheduled.layerOrdered depth) (rightScheduled.layerOrdered depth)
  · intro depth entry present
    rw [alignSparseCanonicalLayers_getD] at present
    have support := (mem_alignSparseCanonicalLayer_addresses zero entry.address
      (left.getD depth []) (right.getD depth [])).mp (by
        exact List.mem_map.mpr ⟨entry, present, rfl⟩)
    rcases support with leftPresent | rightPresent
    · rcases List.mem_map.mp leftPresent with ⟨leftEntry, leftEntryPresent, addressEq⟩
      exact (congrArg List.length addressEq).symm.trans
        (leftScheduled.depthCorrect depth leftEntry leftEntryPresent)
    · rcases List.mem_map.mp rightPresent with ⟨rightEntry, rightEntryPresent, addressEq⟩
      exact (congrArg List.length addressEq).symm.trans
        (rightScheduled.depthCorrect depth rightEntry rightEntryPresent)

private theorem alignedHierarchyAddressBefore_of_length_lt
    {left right : List ℕ} (less : left.length < right.length) :
    DeclarativeCIP.HierarchyAddressBefore left right := by
  simp [DeclarativeCIP.HierarchyAddressBefore, DeclarativeCIP.HierarchyAddressKey,
    List.cons_lt_cons_iff, less]

private theorem alignedHierarchyAddressBefore_of_length_eq_of_lt
    {left right : List ℕ} (lengthEq : left.length = right.length)
    (less : left < right) : DeclarativeCIP.HierarchyAddressBefore left right := by
  simp [DeclarativeCIP.HierarchyAddressBefore, DeclarativeCIP.HierarchyAddressKey,
    lengthEq, less]

/-- An aligned sparse schedule flattens to strict sphere-major semantic address order. -/
theorem AlignedSparseCanonicalLayersScheduledFrom.flattened_pairwise
    {α : Type*} (offset : ℕ)
    (layers : List (List (AlignedSparseCanonicalEntry α)))
    (scheduled : AlignedSparseCanonicalLayersScheduledFrom offset layers) :
    (layers.flatten.map AlignedSparseCanonicalEntry.address).Pairwise
      DeclarativeCIP.HierarchyAddressBefore := by
  have scheduleEq : layers.flatten.map AlignedSparseCanonicalEntry.address =
      layers.zipIdx.flatMap
        (fun layer => layer.1.map AlignedSparseCanonicalEntry.address) := by
    rw [List.map_flatten]
    unfold List.flatMap
    apply congrArg List.flatten
    calc
      layers.map (List.map AlignedSparseCanonicalEntry.address) =
          (layers.zipIdx.map Prod.fst).map
            (List.map AlignedSparseCanonicalEntry.address) := by
            rw [List.zipIdx_map_fst]
      _ = layers.zipIdx.map
          (fun layer => layer.1.map AlignedSparseCanonicalEntry.address) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro layer _
            rfl
  rw [scheduleEq]
  apply List.pairwise_flatMap.mpr
  constructor
  · intro layer layerPresent
    have layerIndex : layer.2 < layers.length :=
      List.snd_lt_of_mem_zipIdx layerPresent
    have getLayer : layers.getD layer.2 [] = layer.1 := by
      have fstEq := List.fst_eq_of_mem_zipIdx layerPresent
      simpa [List.getD, layerIndex] using fstEq.symm
    have ordered := scheduled.layerOrdered layer.2
    rw [getLayer] at ordered
    exact ordered.imp_of_mem fun leftPresent rightPresent less => by
      rcases List.mem_map.mp leftPresent with ⟨leftEntry, leftEntryPresent, rfl⟩
      rcases List.mem_map.mp rightPresent with ⟨rightEntry, rightEntryPresent, rfl⟩
      have depthCorrect := scheduled.depthCorrect layer.2
      rw [getLayer] at depthCorrect
      exact alignedHierarchyAddressBefore_of_length_eq_of_lt
        ((depthCorrect leftEntry leftEntryPresent).trans
          (depthCorrect rightEntry rightEntryPresent).symm) less
  · have indices : layers.zipIdx.Pairwise (fun left right => left.2 < right.2) := by
      apply List.pairwise_map.mp
      rw [List.zipIdx_map_snd]
      exact List.pairwise_lt_range'
    exact indices.imp_of_mem
      fun {leftLayer rightLayer} leftLayerPresent rightLayerPresent indicesLess => by
        intro leftPath leftPathPresent rightPath rightPathPresent
        have leftIndex : leftLayer.2 < layers.length :=
          List.snd_lt_of_mem_zipIdx leftLayerPresent
        have rightIndex : rightLayer.2 < layers.length :=
          List.snd_lt_of_mem_zipIdx rightLayerPresent
        have leftLayerEq : layers.getD leftLayer.2 [] = leftLayer.1 := by
          have fstEq := List.fst_eq_of_mem_zipIdx leftLayerPresent
          simpa [List.getD, leftIndex] using fstEq.symm
        have rightLayerEq : layers.getD rightLayer.2 [] = rightLayer.1 := by
          have fstEq := List.fst_eq_of_mem_zipIdx rightLayerPresent
          simpa [List.getD, rightIndex] using fstEq.symm
        rcases List.mem_map.mp leftPathPresent with
          ⟨leftEntry, leftEntryPresent, rfl⟩
        rcases List.mem_map.mp rightPathPresent with
          ⟨rightEntry, rightEntryPresent, rfl⟩
        have leftDepth := scheduled.depthCorrect leftLayer.2 leftEntry (by
          rw [leftLayerEq]
          exact leftEntryPresent)
        have rightDepth := scheduled.depthCorrect rightLayer.2 rightEntry (by
          rw [rightLayerEq]
          exact rightEntryPresent)
        apply alignedHierarchyAddressBefore_of_length_lt
        omega

end RawMolecule

end TetraStereo.OneCenter
