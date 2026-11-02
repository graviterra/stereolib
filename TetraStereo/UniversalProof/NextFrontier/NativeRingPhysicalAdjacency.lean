import TetraStereo.UniversalProof.NextFrontier.NativeRingPhysicalStructure
import TetraStereo.OneCenter.ProductionCIPRule1aGraphRealization

set_option autoImplicit false

namespace TetraStereo.UniversalProof.GeneralRingPhysicalAdmission

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingDomain

theorem connects_true_iff (bond : RawBond) (u v : ℕ) :
    bond.connects u v = true ↔
      (bond.source = u ∧ bond.target = v) ∨ (bond.source = v ∧ bond.target = u) := by
  simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]

theorem ringRaw_bondOrder_pos_iff_connect (n : Nat) (parity : TetrahedralInputParity)
    {center ligand : Nat} (distinct : center ≠ ligand) :
    0 < (ringRaw n parity).bondOrder center ligand ↔
      ∃ bond ∈ ringBonds n, bond.connects center ligand = true := by
  rw [RawMolecule.bondOrder_pos_iff_exists_bond (ringRaw n parity) distinct, ringRaw_bonds]

theorem ringRaw_row_zero_iff (n : ℕ) (_parity : TetrahedralInputParity) (l : ℕ) :
    l ∈ [1, 2, n + 4] ↔ ∃ b ∈ ringBonds n, b.connects 0 l = true := by
  constructor
  · intro h
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with h | h | h
    · subst h; exact ⟨_, prefix0_mem n, by decide⟩
    · subst h; exact ⟨_, prefix1_mem n, by decide⟩
    · subst h; exact ⟨_, closureBond_mem n, by unfold closureBond RawBond.connects; simp⟩
  · rintro ⟨b, hb, hconn⟩
    have hconnect := (connects_true_iff b 0 l).mp hconn
    rw [mem_ringBonds] at hb
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rcases hb with rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl
    · change (0 = 0 ∧ 1 = l) ∨ (0 = l ∧ 1 = 0) at hconnect
      omega
    · change (0 = 0 ∧ 2 = l) ∨ (0 = l ∧ 2 = 0) at hconnect
      omega
    · change (2 = 0 ∧ 3 = l) ∨ (2 = l ∧ 3 = 0) at hconnect
      omega
    · change ((if j = 0 then 2 else j + 3) = 0 ∧ j + 4 = l) ∨
        ((if j = 0 then 2 else j + 3) = l ∧ j + 4 = 0) at hconnect
      by_cases h0 : j = 0 <;> simp only [h0, if_true, if_false] at hconnect <;> omega
    · change (n + 4 = 0 ∧ 0 = l) ∨ (n + 4 = l ∧ 0 = 0) at hconnect
      omega

theorem ringRaw_row_one_iff (n : ℕ) (_parity : TetrahedralInputParity) (l : ℕ) :
    l ∈ [0] ↔ ∃ b ∈ ringBonds n, b.connects 1 l = true := by
  constructor
  · intro h
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    subst h; exact ⟨_, prefix0_mem n, by decide⟩
  · rintro ⟨b, hb, hconn⟩
    have hconnect := (connects_true_iff b 1 l).mp hconn
    rw [mem_ringBonds] at hb
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rcases hb with rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl
    · change (0 = 1 ∧ 1 = l) ∨ (0 = l ∧ 1 = 1) at hconnect
      omega
    · change (0 = 1 ∧ 2 = l) ∨ (0 = l ∧ 2 = 1) at hconnect
      omega
    · change (2 = 1 ∧ 3 = l) ∨ (2 = l ∧ 3 = 1) at hconnect
      omega
    · change ((if j = 0 then 2 else j + 3) = 1 ∧ j + 4 = l) ∨
        ((if j = 0 then 2 else j + 3) = l ∧ j + 4 = 1) at hconnect
      by_cases h0 : j = 0 <;> simp only [h0, if_true, if_false] at hconnect <;> omega
    · change (n + 4 = 1 ∧ 0 = l) ∨ (n + 4 = l ∧ 0 = 1) at hconnect
      omega

theorem ringRaw_row_two_iff (n : ℕ) (_parity : TetrahedralInputParity) (l : ℕ) :
    l ∈ [0, 3, 4] ↔ ∃ b ∈ ringBonds n, b.connects 2 l = true := by
  constructor
  · intro h
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with h | h | h
    · subst h; exact ⟨_, prefix1_mem n, by decide⟩
    · subst h; exact ⟨_, prefix2_mem n, by decide⟩
    · subst h; exact ⟨_, chainBond_mem n 0 (by omega), by decide⟩
  · rintro ⟨b, hb, hconn⟩
    have hconnect := (connects_true_iff b 2 l).mp hconn
    rw [mem_ringBonds] at hb
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rcases hb with rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl
    · change (0 = 2 ∧ 1 = l) ∨ (0 = l ∧ 1 = 2) at hconnect
      omega
    · change (0 = 2 ∧ 2 = l) ∨ (0 = l ∧ 2 = 2) at hconnect
      omega
    · change (2 = 2 ∧ 3 = l) ∨ (2 = l ∧ 3 = 2) at hconnect
      omega
    · change ((if j = 0 then 2 else j + 3) = 2 ∧ j + 4 = l) ∨
        ((if j = 0 then 2 else j + 3) = l ∧ j + 4 = 2) at hconnect
      by_cases h0 : j = 0 <;> simp only [h0, if_true, if_false] at hconnect <;> omega
    · change (n + 4 = 2 ∧ 0 = l) ∨ (n + 4 = l ∧ 0 = 2) at hconnect
      omega

theorem ringRaw_row_three_iff (n : ℕ) (_parity : TetrahedralInputParity) (l : ℕ) :
    l ∈ [2] ↔ ∃ b ∈ ringBonds n, b.connects 3 l = true := by
  constructor
  · intro h
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    subst h; exact ⟨_, prefix2_mem n, by decide⟩
  · rintro ⟨b, hb, hconn⟩
    have hconnect := (connects_true_iff b 3 l).mp hconn
    rw [mem_ringBonds] at hb
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rcases hb with rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl
    · change (0 = 3 ∧ 1 = l) ∨ (0 = l ∧ 1 = 3) at hconnect
      omega
    · change (0 = 3 ∧ 2 = l) ∨ (0 = l ∧ 2 = 3) at hconnect
      omega
    · change (2 = 3 ∧ 3 = l) ∨ (2 = l ∧ 3 = 3) at hconnect
      omega
    · change ((if j = 0 then 2 else j + 3) = 3 ∧ j + 4 = l) ∨
        ((if j = 0 then 2 else j + 3) = l ∧ j + 4 = 3) at hconnect
      by_cases h0 : j = 0 <;> simp only [h0, if_true, if_false] at hconnect <;> omega
    · change (n + 4 = 3 ∧ 0 = l) ∨ (n + 4 = l ∧ 0 = 3) at hconnect
      omega

theorem ringRaw_row_chain_iff (n : ℕ) (_parity : TetrahedralInputParity) (k : ℕ) (hk : k ≤ n)
    (l : ℕ) :
    l ∈ chainRow n k ↔ ∃ b ∈ ringBonds n, b.connects (k + 4) l = true := by
  constructor
  · intro h
    simp only [chainRow, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with h | h
    · refine ⟨chainBond k, chainBond_mem n k (by omega), ?_⟩
      refine (connects_true_iff _ (k + 4) l).mpr (Or.inr ⟨?_, ?_⟩)
      · rw [chainBond_source_eq]; exact h.symm
      · rfl
    · by_cases hkn : k < n
      · simp only [if_pos hkn] at h
        refine ⟨chainBond (k + 1), chainBond_mem n (k + 1) (by omega), ?_⟩
        refine (connects_true_iff _ (k + 4) l).mpr (Or.inl ⟨?_, ?_⟩)
        · rw [chainBond_source_eq]
          simp only [show k + 1 ≠ 0 by omega, if_false]
        · rw [chainBond_target_eq]; omega
      · have hkn' : k = n := by omega
        simp only [if_neg hkn] at h
        subst h
        refine ⟨closureBond n, closureBond_mem n, ?_⟩
        refine (connects_true_iff _ (k + 4) 0).mpr (Or.inl ⟨?_, ?_⟩)
        · unfold closureBond; rw [hkn']
        · rfl
  · rintro ⟨b, hb, hconn⟩
    have hconnect := (connects_true_iff b (k + 4) l).mp hconn
    rw [mem_ringBonds] at hb
    simp only [chainRow, List.mem_cons, List.mem_nil_iff, or_false]
    rcases hb with rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl
    · change (0 = (k + 4) ∧ 1 = l) ∨ (0 = l ∧ 1 = (k + 4)) at hconnect
      omega
    · change (0 = (k + 4) ∧ 2 = l) ∨ (0 = l ∧ 2 = (k + 4)) at hconnect
      omega
    · change (2 = (k + 4) ∧ 3 = l) ∨ (2 = l ∧ 3 = (k + 4)) at hconnect
      omega
    · change ((if j = 0 then 2 else j + 3) = (k + 4) ∧ j + 4 = l) ∨
        ((if j = 0 then 2 else j + 3) = l ∧ j + 4 = (k + 4)) at hconnect
      split_ifs at hconnect ⊢ <;> omega
    · change (n + 4 = (k + 4) ∧ 0 = l) ∨ (n + 4 = l ∧ 0 = (k + 4)) at hconnect
      split_ifs <;> omega

theorem chainRow_nodup (n k : Nat) : (chainRow n k).Nodup := by
  have different : (if k = 0 then 2 else k + 3) ≠
      (if k < n then k + 5 else 0) := by
    split_ifs <;> omega
  unfold chainRow
  exact List.Nodup.cons (by simpa only [List.mem_singleton] using different)
    (List.nodup_singleton _)

theorem ringRaw_writtenNeighbors_zero (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).writtenNeighbors 0 = [1, 2, n + 4] := rfl

theorem ringRaw_writtenNeighbors_one (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).writtenNeighbors 1 = [0] := rfl

theorem ringRaw_writtenNeighbors_two (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).writtenNeighbors 2 = [0, 3, 4] := rfl

theorem ringRaw_writtenNeighbors_three (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).writtenNeighbors 3 = [2] := rfl

theorem ringRaw_writtenNeighbors_chain (n : Nat) (parity : TetrahedralInputParity)
    (k : Nat) (bound : k < n + 1) :
    (ringRaw n parity).writtenNeighbors (k + 4) = chainRow n k := by
  have lookup : (ringRows n)[k + 4]? = some (chainRow n k) := by
    unfold ringRows
    rw [show k + 4 =
      ([[1, 2, n + 4], [0], [0, 3, 4], [2]] : List (List Nat)).length + k by simp; omega]
    rw [getElem?_append_right']
    exact getElem?_map_range (chainRow n) (n + 1) k bound
  change (match (ringRows n)[k + 4]? with | some row => row | none => _) = chainRow n k
  rw [lookup]

theorem ringRaw_written_neighbors_nodup (n : ℕ) (parity : TetrahedralInputParity)
    (c : ℕ) (hc : c < n + 5) : ((ringRaw n parity).writtenNeighbors c).Nodup := by
  rcases lt_or_ge c 4 with hsmall | hbig
  · interval_cases c
    · rw [ringRaw_writtenNeighbors_zero]
      exact List.Nodup.cons (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega)
        (List.Nodup.cons (by simp only [List.mem_singleton]; omega) (List.nodup_singleton _))
    · rw [ringRaw_writtenNeighbors_one]; exact List.nodup_singleton _
    · rw [ringRaw_writtenNeighbors_two]
      exact List.Nodup.cons (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega)
        (List.Nodup.cons (by simp only [List.mem_singleton]; omega) (List.nodup_singleton _))
    · rw [ringRaw_writtenNeighbors_three]; exact List.nodup_singleton _
  · obtain ⟨k, rfl⟩ : ∃ k, c = k + 4 := ⟨c - 4, by omega⟩
    rw [ringRaw_writtenNeighbors_chain n parity k (by omega)]
    exact chainRow_nodup n k

theorem ringRaw_written_neighbors_bounded (n : ℕ) (parity : TetrahedralInputParity)
    (c : ℕ) (hc : c < n + 5) {l : ℕ}
    (hl : l ∈ (ringRaw n parity).writtenNeighbors c) : l < n + 5 := by
  rcases lt_or_ge c 4 with hsmall | hbig
  · interval_cases c
    · rw [ringRaw_writtenNeighbors_zero] at hl
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl | rfl <;> omega
    · rw [ringRaw_writtenNeighbors_one] at hl
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
      omega
    · rw [ringRaw_writtenNeighbors_two] at hl
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl | rfl <;> omega
    · rw [ringRaw_writtenNeighbors_three] at hl
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
      omega
  · obtain ⟨k, rfl⟩ : ∃ k, c = k + 4 := ⟨c - 4, by omega⟩
    rw [ringRaw_writtenNeighbors_chain n parity k (by omega)] at hl
    simp only [chainRow, List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with hl | hl
    · by_cases h0 : k = 0 <;> simp only [h0, if_true, if_false] at hl <;> omega
    · by_cases hlt : k < n <;> simp only [hlt, if_true, if_false] at hl <;> omega

theorem ringRaw_bondOrder_pos_iff_mem_written (n : ℕ) (parity : TetrahedralInputParity)
    (c : ℕ) (hc : c < n + 5) (l : ℕ) :
    l ∈ (ringRaw n parity).writtenNeighbors c ↔ 0 < (ringRaw n parity).bondOrder c l := by
  by_cases hcl : c = l
  · subst hcl
    rw [show (ringRaw n parity).bondOrder c c = 0 by
      unfold RawMolecule.bondOrder; rw [if_pos rfl]]
    constructor
    · intro hmem
      rcases lt_or_ge c 4 with hsmall | hbig
      · interval_cases c
        · rw [ringRaw_writtenNeighbors_zero] at hmem
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
          omega
        · rw [ringRaw_writtenNeighbors_one] at hmem
          simp only [List.mem_singleton] at hmem
          omega
        · rw [ringRaw_writtenNeighbors_two] at hmem
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
          omega
        · rw [ringRaw_writtenNeighbors_three] at hmem
          simp only [List.mem_singleton] at hmem
          omega
      · obtain ⟨k, rfl⟩ : ∃ k, c = k + 4 := ⟨c - 4, by omega⟩
        rw [ringRaw_writtenNeighbors_chain n parity k (by omega)] at hmem
        simp only [chainRow, List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with hmem | hmem
        · by_cases h0 : k = 0 <;> simp only [h0, if_true, if_false] at hmem <;> omega
        · by_cases hlt : k < n <;> simp only [hlt, if_true, if_false] at hmem <;> omega
    · intro h; exact absurd h (lt_irrefl 0)
  · rw [ringRaw_bondOrder_pos_iff_connect n parity hcl]
    rcases lt_or_ge c 4 with hsmall | hbig
    · interval_cases c
      · rw [ringRaw_writtenNeighbors_zero]; exact ringRaw_row_zero_iff n parity l
      · rw [ringRaw_writtenNeighbors_one]; exact ringRaw_row_one_iff n parity l
      · rw [ringRaw_writtenNeighbors_two]; exact ringRaw_row_two_iff n parity l
      · rw [ringRaw_writtenNeighbors_three]; exact ringRaw_row_three_iff n parity l
    · obtain ⟨k, rfl⟩ : ∃ k, c = k + 4 := ⟨c - 4, by omega⟩
      rw [ringRaw_writtenNeighbors_chain n parity k (by omega)]
      exact ringRaw_row_chain_iff n parity k (by omega) l

theorem ringRaw_writtenNeighborExact (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).WrittenNeighborExact := by
  apply WrittenNeighborExact.of_at
  intro center
  have hc : center.val < n + 5 := by
    rw [← atom_count n parity]
    exact center.isLt
  refine ⟨ringRaw_written_neighbors_nodup n parity center.val hc, ?_, ?_⟩
  · intro ligand hl
    rw [atom_count n parity]
    exact ringRaw_written_neighbors_bounded n parity center.val hc hl
  · intro ligand
    exact ringRaw_bondOrder_pos_iff_mem_written n parity center.val hc ligand.val

def incidentBool (c : ℕ) (b : RawBond) : Bool := b.source == c || b.target == c

def otherEndpoint (c : ℕ) (b : RawBond) : ℕ := if b.source == c then b.target else b.source

theorem otherEndpoint_connect (b : RawBond) (c : ℕ) (h : incidentBool c b = true) :
    b.connects c (otherEndpoint c b) = true := by
  unfold incidentBool at h
  rw [Bool.or_eq_true] at h
  unfold otherEndpoint
  by_cases hs : (b.source == c) = true
  · rw [if_pos hs]
    exact (connects_true_iff b c b.target).mpr (Or.inl ⟨beq_iff_eq.mp hs, rfl⟩)
  · rw [if_neg hs]
    rcases h with h | h
    · exact absurd h hs
    · exact (connects_true_iff b c b.source).mpr (Or.inr ⟨rfl, beq_iff_eq.mp h⟩)

theorem edgeKey_eq_of_connects {b : RawBond} {c o : ℕ} (h : b.connects c o = true) :
    b.edgeKey = (min c o, max c o) := by
  rcases (connects_true_iff b c o).mp h with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · unfold RawBond.edgeKey; rw [hs, ht]
  · unfold RawBond.edgeKey; rw [hs, ht, Nat.min_comm, Nat.max_comm]

theorem otherEndpoint_inj_on_filter (n : ℕ) (c : ℕ) :
    ∀ b₁ ∈ (ringBonds n).filter (incidentBool c),
      ∀ b₂ ∈ (ringBonds n).filter (incidentBool c),
        otherEndpoint c b₁ = otherEndpoint c b₂ → b₁ = b₂ := by
  intro b₁ h₁ b₂ h₂ heq
  have m₁ : b₁ ∈ ringBonds n ∧ incidentBool c b₁ = true := List.mem_filter.mp h₁
  have m₂ : b₂ ∈ ringBonds n ∧ incidentBool c b₂ = true := List.mem_filter.mp h₂
  have e₁ := edgeKey_eq_of_connects (otherEndpoint_connect b₁ c m₁.2)
  have e₂ := edgeKey_eq_of_connects (otherEndpoint_connect b₂ c m₂.2)
  refine ringBonds_edgeKey_inj n b₁ m₁.1 b₂ m₂.1 ?_
  rw [e₁, e₂, heq]

theorem incidentBondOrderSum_eq_length (bonds : List RawBond) (c : ℕ)
    (hall : ∀ b ∈ bonds, b.kind.order = 1) :
    bonds.foldl (fun total b =>
        if b.source == c || b.target == c then total + b.kind.order else total) 0
      = (bonds.filter (fun b => b.source == c || b.target == c)).length := by
  have key : ∀ (bonds : List RawBond) (acc : ℕ),
      (∀ b ∈ bonds, b.kind.order = 1) →
      bonds.foldl (fun total b =>
          if b.source == c || b.target == c then total + b.kind.order else total) acc
        = acc + (bonds.filter (fun b => b.source == c || b.target == c)).length := by
    intro bonds
    induction bonds with
    | nil => intro acc _; simp
    | cons hd tl ih =>
        intro acc hb
        rw [List.foldl_cons, List.filter_cons]
        have htl : ∀ b ∈ tl, b.kind.order = 1 := fun b hb' => hb b (List.mem_cons_of_mem hd hb')
        have hhd : hd.kind.order = 1 := hb hd (List.mem_cons_self)
        cases active : (hd.source == c || hd.target == c) with
        | false =>
            simpa only [active, Bool.false_eq_true, ↓reduceIte] using ih acc htl
        | true =>
            simp only [↓reduceIte, hhd, List.length_cons]
            rw [ih (acc + 1) htl]
            omega
  simpa only [Nat.zero_add] using key bonds 0 hall

theorem ringRaw_written_row_length_zero (n : ℕ) (parity : TetrahedralInputParity) :
    ((ringRaw n parity).writtenNeighbors 0).length = 3 := by
  rw [ringRaw_writtenNeighbors_zero]; rfl

theorem ringRaw_written_row_length_one (n : ℕ) (parity : TetrahedralInputParity) :
    ((ringRaw n parity).writtenNeighbors 1).length = 1 := by
  rw [ringRaw_writtenNeighbors_one]; rfl

theorem ringRaw_written_row_length_two (n : ℕ) (parity : TetrahedralInputParity) :
    ((ringRaw n parity).writtenNeighbors 2).length = 3 := by
  rw [ringRaw_writtenNeighbors_two]; rfl

theorem ringRaw_written_row_length_three (n : ℕ) (parity : TetrahedralInputParity) :
    ((ringRaw n parity).writtenNeighbors 3).length = 1 := by
  rw [ringRaw_writtenNeighbors_three]; rfl

theorem ringRaw_written_row_length_chain (n : ℕ) (parity : TetrahedralInputParity)
    (k : ℕ) (hk : k ≤ n) :
    ((ringRaw n parity).writtenNeighbors (k + 4)).length = 2 := by
  rw [ringRaw_writtenNeighbors_chain n parity k (by omega)]; rfl

theorem ringRaw_incidentSum_le_row (n : ℕ) (parity : TetrahedralInputParity)
    (c : ℕ) (hc : c < n + 5) :
    (ringRaw n parity).incidentBondOrderSum c ≤
      ((ringRaw n parity).writtenNeighbors c).length := by
  have hsum : (ringRaw n parity).incidentBondOrderSum c =
      ((ringBonds n).filter (incidentBool c)).length := by
    unfold RawMolecule.incidentBondOrderSum
    rw [ringRaw_bonds]
    exact incidentBondOrderSum_eq_length _ c
      (by intro b hb; rw [ringBonds_kind_single n b hb]; rfl)
  rw [hsum]
  have hbsnodup : ((ringBonds n).filter (incidentBool c)).Nodup :=
    (ringBonds_nodup n).filter (incidentBool c)
  have hmapnodup : (((ringBonds n).filter (incidentBool c)).map (otherEndpoint c)).Nodup :=
    (List.nodup_map_iff_inj_on hbsnodup).mpr
      (fun a ha b hb h => otherEndpoint_inj_on_filter n c a ha b hb h)
  have hsubset : ∀ a ∈ ((ringBonds n).filter (incidentBool c)).map (otherEndpoint c),
      a ∈ (ringRaw n parity).writtenNeighbors c := by
    intro a ha
    rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
    have hb' : b ∈ ringBonds n ∧ incidentBool c b = true := List.mem_filter.mp hb
    have hbo : 0 < (ringRaw n parity).bondOrder c (otherEndpoint c b) := by
      apply (RawMolecule.bondOrder_pos_iff_exists_bond (ringRaw n parity) ?_).mpr
      · exact ⟨b, by simpa only [ringRaw_bonds] using hb'.1,
          otherEndpoint_connect b c hb'.2⟩
      · intro same
        rcases (connects_true_iff b c (otherEndpoint c b)).mp
          (otherEndpoint_connect b c hb'.2) with ⟨source, target⟩ | ⟨source, target⟩
        · exact (ringBonds_bounds n b hb'.1).2.2
            (source.trans (same.trans target.symm))
        · exact (ringBonds_bounds n b hb'.1).2.2
            (source.trans (same.symm.trans target.symm))
    exact (ringRaw_bondOrder_pos_iff_mem_written n parity c hc (otherEndpoint c b)).mpr hbo
  have hperm : List.Subperm
      (((ringBonds n).filter (incidentBool c)).map (otherEndpoint c))
      ((ringRaw n parity).writtenNeighbors c) :=
    List.subperm_of_subset hmapnodup hsubset
  have hlen := List.Subperm.length_le hperm
  rw [List.length_map] at hlen
  exact hlen

theorem ringRaw_incidentSum_two_le (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).incidentBondOrderSum 2 ≤ 3 := by
  have := ringRaw_incidentSum_le_row n parity 2 (by omega)
  rwa [ringRaw_written_row_length_two n parity] at this

theorem ringRaw_incidentSum_chain_le (n : ℕ) (parity : TetrahedralInputParity) (k : ℕ) (hk : k ≤ n) :
    (ringRaw n parity).incidentBondOrderSum (k + 4) ≤ 2 := by
  have := ringRaw_incidentSum_le_row n parity (k + 4) (by omega)
  rwa [ringRaw_written_row_length_chain n parity k hk] at this

/-- Complete chronological provenance table for the independent physical ring. -/
theorem ringRaw_predecessor_count (n : Nat) (parity : TetrahedralInputParity) :
    (ringRaw n parity).introductionPredecessors.length = (ringRaw n parity).atomCount := by
  simp [ringRaw, ringPredecessors, atomCount]

theorem ringRaw_predecessor_chain (n k : Nat) (parity : TetrahedralInputParity)
    (bound : k < n + 1) :
    (ringRaw n parity).introductionPredecessors[k + 4]? =
      some (some (if k = 0 then 2 else k + 3)) := by
  change (ringPredecessors n)[k + 4]? = _
  unfold ringPredecessors
  rw [show k + 4 = ([none, some 0, some 0, some 2] : List (Option Nat)).length + k by
    simp; omega]
  rw [getElem?_append_right']
  exact getElem?_map_range _ _ _ bound

/-- Every declared non-root predecessor is an earlier atom, an actual introduction edge, and
precisely the first written neighbor. The eventual closing bond into atom zero cannot change it. -/
theorem ringRaw_introduction_valid (n : Nat) (parity : TetrahedralInputParity) :
    (ringRaw n parity).introductionPredecessorsValid? = true := by
  unfold RawMolecule.introductionPredecessorsValid?
  rw [ringRaw_predecessor_count]
  simp only [Nat.le_refl, decide_true, Bool.true_and, List.all_eq_true, List.mem_range]
  intro index bound
  rw [atom_count] at bound
  rcases lt_or_ge index 4 with small | large
  · interval_cases index
    · rfl
    · change (decide (0 < 1) && ((ringRaw n parity).bonds.any _) &&
        (((ringRaw n parity).writtenNeighbors 1).head? == some 0)) = true
      rw [ringRaw_writtenNeighbors_one]
      simp only [Nat.zero_lt_succ, decide_true, Bool.true_and, List.head?_cons,
        beq_self_eq_true, Bool.and_true]
      apply List.any_eq_true.mpr
      exact ⟨_, prefix0_mem n, by decide⟩
    · change (decide (0 < 2) && ((ringRaw n parity).bonds.any _) &&
        (((ringRaw n parity).writtenNeighbors 2).head? == some 0)) = true
      rw [ringRaw_writtenNeighbors_two]
      simp only [Nat.zero_lt_succ, decide_true, Bool.true_and, List.head?_cons,
        beq_self_eq_true, Bool.and_true]
      apply List.any_eq_true.mpr
      exact ⟨_, prefix1_mem n, by decide⟩
    · change (decide (2 < 3) && ((ringRaw n parity).bonds.any _) &&
        (((ringRaw n parity).writtenNeighbors 3).head? == some 2)) = true
      rw [ringRaw_writtenNeighbors_three]
      simp only [show (2 : Nat) < 3 by decide, decide_true, Bool.true_and, List.head?_cons,
        beq_self_eq_true, Bool.and_true]
      apply List.any_eq_true.mpr
      exact ⟨_, prefix2_mem n, by decide⟩
  · obtain ⟨k, rfl⟩ : ∃ k, index = k + 4 := ⟨index - 4, by omega⟩
    rw [ringRaw_predecessor_chain n k parity (by omega),
      ringRaw_writtenNeighbors_chain n parity k (by omega)]
    have earlier : (if k = 0 then 2 else k + 3) < k + 4 := by split <;> omega
    simp only [earlier, decide_true, Bool.true_and, chainRow, List.head?_cons,
      beq_self_eq_true, Bool.and_true]
    apply List.any_eq_true.mpr
    exact ⟨chainBond k, chainBond_mem n k (by omega), by simp [chainBond]⟩

theorem ringRaw_parser_introduction_valid (n : Nat) (parity : TetrahedralInputParity) :
    (ringRaw n parity).parserIntroductionValid? = true := by
  simp [RawMolecule.parserIntroductionValid?, ringRaw_predecessor_count,
    ringRaw_introduction_valid]

end TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
