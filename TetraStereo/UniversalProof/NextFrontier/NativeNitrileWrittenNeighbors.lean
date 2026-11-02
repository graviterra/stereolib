import TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule

private def prefixAdjacent (left right : Nat) : Prop :=
  ((left = 0 ∧ right = 1) ∨ (left = 1 ∧ right = 0)) ∨
  ((left = 0 ∧ right = 2) ∨ (left = 2 ∧ right = 0)) ∨
  ((left = 2 ∧ right = 3) ∨ (left = 3 ∧ right = 2)) ∨
  ((left = 0 ∧ right = 4) ∨ (left = 4 ∧ right = 0)) ∨
  ((left = 4 ∧ right = 5) ∨ (left = 5 ∧ right = 4))

private def tailAdjacent (n left right : Nat) : Prop :=
  (left = 4 ∧ right = 6) ∨ (left = 6 ∧ right = 4) ∨
    (6 ≤ left ∧ left < n + 6 ∧ right = left + 1) ∨
    (6 ≤ right ∧ right < n + 6 ∧ left = right + 1)

private theorem tail_connections (n left right : Nat) :
    (∃ offset, offset < n + 1 ∧
      ((tailParent offset = left ∧ offset + 6 = right) ∨
        (tailParent offset = right ∧ offset + 6 = left))) ↔
      tailAdjacent n left right := by
  constructor
  · rintro ⟨offset, bound, connection⟩
    by_cases root : offset = 0
    · subst offset
      simp only [tailParent, if_true, Nat.zero_add] at connection
      unfold tailAdjacent
      omega
    · rw [tailParent, if_neg root] at connection
      unfold tailAdjacent
      omega
  · intro connection
    rcases connection with first | reverseFirst | forward | reverse
    · exact ⟨0, by omega, Or.inl ⟨first.1.symm, first.2.symm⟩⟩
    · exact ⟨0, by omega, Or.inr ⟨reverseFirst.2.symm, reverseFirst.1.symm⟩⟩
    · refine ⟨left - 5, by omega, Or.inl ?_⟩
      have nonzero : left - 5 ≠ 0 := by omega
      simp only [tailParent, if_neg nonzero]
      omega
    · refine ⟨right - 5, by omega, Or.inr ?_⟩
      have nonzero : right - 5 ≠ 0 := by omega
      simp only [tailParent, if_neg nonzero]
      omega

private theorem record_connections (source target : Nat) (kind : ParsedBondKind)
    (left right : Nat) :
    RawBond.connects ⟨source, target, kind⟩ left right = true ↔
      ((left = source ∧ right = target) ∨ (left = target ∧ right = source)) := by
  simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro (⟨first, second⟩ | ⟨first, second⟩)
    · exact Or.inl ⟨first.symm, second.symm⟩
    · exact Or.inr ⟨second.symm, first.symm⟩
  · rintro (⟨first, second⟩ | ⟨first, second⟩)
    · exact Or.inl ⟨first.symm, second.symm⟩
    · exact Or.inr ⟨second.symm, first.symm⟩

private theorem prefix_connections (left right : Nat) :
    (∃ bond ∈ prefixBonds, bond.connects left right = true) ↔
      prefixAdjacent left right := by
  constructor
  · rintro ⟨bond, retained, connected⟩
    simp only [prefixBonds, List.mem_cons, List.not_mem_nil, or_false] at retained
    rcases retained with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ((record_connections 0 1 .single left right).mp connected)
    · exact Or.inr (Or.inl ((record_connections 0 2 .single left right).mp connected))
    · exact Or.inr (Or.inr (Or.inl
        ((record_connections 2 3 .triple left right).mp connected)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ((record_connections 0 4 .single left right).mp connected))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ((record_connections 4 5 .single left right).mp connected))))
  · intro connected
    rcases connected with first | second | third | fourth | fifth
    · refine ⟨⟨0, 1, .single⟩, by simp [prefixBonds], ?_⟩
      exact (record_connections 0 1 .single left right).mpr first
    · refine ⟨⟨0, 2, .single⟩, by simp [prefixBonds], ?_⟩
      exact (record_connections 0 2 .single left right).mpr second
    · refine ⟨⟨2, 3, .triple⟩, by simp [prefixBonds], ?_⟩
      exact (record_connections 2 3 .triple left right).mpr third
    · refine ⟨⟨0, 4, .single⟩, by simp [prefixBonds], ?_⟩
      exact (record_connections 0 4 .single left right).mpr fourth
    · refine ⟨⟨4, 5, .single⟩, by simp [prefixBonds], ?_⟩
      exact (record_connections 4 5 .single left right).mpr fifth

private theorem raw_connections (parity : TetrahedralInputParity) (n left right : Nat) :
    (∃ bond ∈ (raw parity n).bonds, bond.connects left right = true) ↔
      prefixAdjacent left right ∨ tailAdjacent n left right := by
  have splitBonds : (∃ bond ∈ (raw parity n).bonds, bond.connects left right = true) ↔
      (∃ bond ∈ prefixBonds, bond.connects left right = true) ∨
        (∃ bond ∈ tailBonds n, bond.connects left right = true) := by
    constructor
    · rintro ⟨bond, retained, connected⟩
      change bond ∈ prefixBonds ++ tailBonds n at retained
      rcases List.mem_append.mp retained with first | last
      · exact Or.inl ⟨bond, first, connected⟩
      · exact Or.inr ⟨bond, last, connected⟩
    · rintro (⟨bond, retained, connected⟩ | ⟨bond, retained, connected⟩)
      · exact ⟨bond, List.mem_append_left _ retained, connected⟩
      · exact ⟨bond, List.mem_append_right _ retained, connected⟩
  rw [splitBonds]
  apply or_congr
  · exact prefix_connections left right
  · have tailEq : (∃ bond ∈ tailBonds n, bond.connects left right = true) ↔
        ∃ offset, offset < n + 1 ∧
          ((tailParent offset = left ∧ offset + 6 = right) ∨
            (tailParent offset = right ∧ offset + 6 = left)) := by
      simp [tailBonds, RawBond.connects]
    exact tailEq.trans (tail_connections n left right)

private theorem list_append_lookup {Alpha : Type} (left right : List Alpha) (index : Nat) :
    (left ++ right)[left.length + index]? = right[index]? := by
  induction left with
  | nil => simp
  | cons head tail ih =>
      rw [List.cons_append, List.length_cons]
      rw [show tail.length + 1 + index = (tail.length + index) + 1 by omega]
      rw [List.getElem?_cons_succ]
      exact ih

theorem raw_tail_written_neighbors (parity : TetrahedralInputParity) (n offset : Nat)
    (bound : offset ≤ n) :
    (raw parity n).writtenNeighbors (offset + 6) =
      [tailParent offset] ++ if offset < n then [offset + 7] else [] := by
  have lookup : (raw parity n).neighborOrder[offset + 6]? =
      some ([tailParent offset] ++ if offset < n then [offset + 7] else []) := by
    change (([[1, 2, 4], [0], [0, 3], [2], [0, 5, 6], [4]] : List (List Nat)) ++
      tailRows n)[offset + 6]? = _
    rw [show offset + 6 =
      ([[1, 2, 4], [0], [0, 3], [2], [0, 5, 6], [4]] : List (List Nat)).length + offset by
        simp; omega]
    rw [list_append_lookup]
    exact getElem?_map_range _ _ _ (by omega)
  unfold writtenNeighbors
  rw [lookup]

private theorem raw_row_connections (parity : TetrahedralInputParity) (n center ligand : Nat)
    (bound : center < n + 7) :
    ligand ∈ (raw parity n).writtenNeighbors center ↔
      prefixAdjacent center ligand ∨ tailAdjacent n center ligand := by
  rcases lt_or_ge center 6 with small | large
  · interval_cases center <;>
      simp [raw, writtenNeighbors, prefixAdjacent, tailAdjacent] <;> omega
  · obtain ⟨offset, rfl⟩ : ∃ offset, center = offset + 6 := ⟨center - 6, by omega⟩
    rw [raw_tail_written_neighbors parity n offset (by omega)]
    by_cases root : offset = 0
    · subst offset
      by_cases internal : 0 < n <;>
        simp [prefixAdjacent, tailAdjacent, tailParent, internal] <;> omega
    · by_cases internal : offset < n <;>
        simp [prefixAdjacent, tailAdjacent, tailParent, root, internal] <;> omega

theorem raw_written_row_nodup (parity : TetrahedralInputParity) (n center : Nat)
    (bound : center < n + 7) :
    ((raw parity n).writtenNeighbors center).Nodup := by
  rcases lt_or_ge center 6 with small | large
  · interval_cases center <;> simp [raw, writtenNeighbors]
  · obtain ⟨offset, rfl⟩ : ∃ offset, center = offset + 6 := ⟨center - 6, by omega⟩
    rw [raw_tail_written_neighbors parity n offset (by omega)]
    have earlier := tail_parent_lt offset
    by_cases internal : offset < n
    · simp [internal]
      omega
    · simp [internal]

/-! This elementary positivity bridge is kept local to avoid pulling the semantic graph
realization dependency tree into the physical parser-admission certificate. -/
private theorem physical_fold_positive (bonds : List RawBond) (left right start : Nat) :
    0 < bonds.foldl (fun order bond =>
      if bond.directedConnects left right then max order bond.kind.order else order) start ↔
      0 < start ∨ ∃ bond ∈ bonds, bond.directedConnects left right = true := by
  induction bonds generalizing start with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons, ih]
      by_cases directed : head.directedConnects left right = true
      · have positive : 0 < head.kind.order := by cases head.kind <;> decide
        simp [directed, positive]
      · simp [directed]

private theorem physical_positive_iff_connection (mol : RawMolecule) {left right : Nat}
    (distinct : left ≠ right) :
    0 < mol.bondOrder left right ↔ ∃ bond ∈ mol.bonds, bond.connects left right = true := by
  unfold bondOrder directedBondOrder
  simp only [distinct, ↓reduceIte, lt_max_iff, physical_fold_positive,
    Nat.lt_irrefl, false_or]
  constructor
  · rintro (⟨bond, retained, directed⟩ | ⟨bond, retained, directed⟩)
    · exact ⟨bond, retained, by simpa only [RawBond.connects, Bool.or_eq_true]
        using (Or.inl directed : bond.directedConnects left right = true ∨
          bond.directedConnects right left = true)⟩
    · exact ⟨bond, retained, by simpa only [RawBond.connects, Bool.or_eq_true]
        using (Or.inr directed : bond.directedConnects left right = true ∨
          bond.directedConnects right left = true)⟩
  · rintro ⟨bond, retained, connected⟩
    simp only [RawBond.connects, Bool.or_eq_true] at connected
    rcases connected with forward | reverse
    · exact Or.inl ⟨bond, retained, forward⟩
    · exact Or.inr ⟨bond, retained, reverse⟩

theorem raw_written_row_bounded (parity : TetrahedralInputParity) (n center ligand : Nat)
    (bound : center < n + 7) (member : ligand ∈ (raw parity n).writtenNeighbors center) :
    ligand < n + 7 := by
  have adjacent := (raw_row_connections parity n center ligand bound).1 member
  unfold prefixAdjacent tailAdjacent at adjacent
  omega

theorem raw_written_neighbor_iff_positive (parity : TetrahedralInputParity)
    (n center ligand : Nat) (bound : center < n + 7) :
    ligand ∈ (raw parity n).writtenNeighbors center ↔
      0 < (raw parity n).bondOrder center ligand := by
  rw [raw_row_connections parity n center ligand bound, ← raw_connections]
  by_cases same : center = ligand
  · subst ligand
    simp only [bondOrder_self, Nat.lt_irrefl, iff_false]
    rintro ⟨bond, retained, connected⟩
    have distinct := (raw_wellFormed parity n bond retained).2.2
    simp only [RawBond.connects, Bool.or_eq_true,
      Bool.and_eq_true, beq_iff_eq] at connected
    omega
  · exact (physical_positive_iff_connection _ same).symm

/-- Every actual stored source row is exact; no expected parser result or output descriptor is
an admission hypothesis. -/
theorem raw_written_exact (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).WrittenNeighborExact := by
  apply WrittenNeighborExact.of_at
  intro center
  have bound : center.val < n + 7 := by simpa only [raw_atomCount] using center.isLt
  refine ⟨raw_written_row_nodup parity n center.val bound, ?_, ?_⟩
  · intro ligand member
    rw [raw_atomCount]
    exact raw_written_row_bounded parity n center.val ligand bound member
  · intro ligand
    exact raw_written_neighbor_iff_positive parity n center.val ligand.val bound

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
