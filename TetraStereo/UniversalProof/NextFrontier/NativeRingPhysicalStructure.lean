import TetraStereo.UniversalProof.NextFrontier.NativeRingDomain
import TetraStereo.OneCenter.ExplicitHydrogens

set_option autoImplicit false

namespace TetraStereo.UniversalProof.GeneralRingPhysicalAdmission

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingDomain

theorem listGet?_append_right {α : Type} (xs ys : List α) (k : ℕ) :
    listGet? (xs ++ ys) (xs.length + k) = listGet? ys k := by
  induction xs generalizing k with
  | nil => simp
  | cons a xs ih =>
      have hlen : (a :: xs).length + k = xs.length + k + 1 := by
        simp [List.length_cons]; omega
      rw [hlen, List.cons_append]
      simp only [listGet?]
      exact ih k

theorem listGet?_replicate {α : Type} (k : ℕ) (a : α) (i : ℕ) :
    listGet? (List.replicate k a) i = if i < k then some a else none := by
  induction k generalizing i with
  | zero => simp [listGet?]
  | succ k ih =>
      cases i with
      | zero => simp only [List.replicate_succ, listGet?, Nat.zero_lt_succ, if_true]
      | succ i =>
          rw [List.replicate_succ]
          simp only [listGet?]
          rw [ih i]
          by_cases h : i < k <;> simp [h]

theorem getElem?_append_right' {α : Type} (xs ys : List α) (k : ℕ) :
    (xs ++ ys)[xs.length + k]? = ys[k]? := by
  induction xs generalizing k with
  | nil => simp
  | cons a xs ih =>
      rw [List.cons_append, List.length_cons]
      rw [show xs.length + 1 + k = (xs.length + k) + 1 by omega]
      rw [List.getElem?_cons_succ]
      exact ih k

def ringPrefix (parity : TetrahedralInputParity) : List AtomSpec :=
  [taggedCarbon parity,
   { AtomSpec.aliphatic .F with explicitHydrogens? := some 0 },
   carbon 1,
   { AtomSpec.aliphatic .Cl with explicitHydrogens? := some 0 }]

def ringTail (n : ℕ) : List AtomSpec := List.replicate (n + 1) (carbon 2)

def ringAtoms (n : ℕ) (parity : TetrahedralInputParity) : List AtomSpec :=
  ringPrefix parity ++ ringTail n

def chainBonds (n : ℕ) : List RawBond := (List.range (n + 1)).map chainBond

def closureBond (n : ℕ) : RawBond := ⟨n + 4, 0, ParsedBondKind.single⟩

def ringBonds (n : ℕ) : List RawBond :=
  [⟨0, 1, ParsedBondKind.single⟩, ⟨0, 2, ParsedBondKind.single⟩, ⟨2, 3, ParsedBondKind.single⟩]
    ++ chainBonds n ++ [closureBond n]

def ringRows (n : ℕ) : List (List ℕ) :=
  [[1, 2, n + 4], [0], [0, 3, 4], [2]] ++ (List.range (n + 1)).map (chainRow n)

@[simp] theorem ringRaw_atoms (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).atoms = ringAtoms n parity := rfl

@[simp] theorem ringRaw_bonds (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).bonds = ringBonds n := rfl

@[simp] theorem ringRaw_neighborOrder (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).neighborOrder = ringRows n := rfl

theorem ringPrefix_length (parity : TetrahedralInputParity) :
    (ringPrefix parity).length = 4 := rfl

theorem ringTail_length (n : ℕ) : (ringTail n).length = n + 1 := by
  simp [ringTail]

theorem ringRaw_atomAt_zero (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).atomAt? 0 = some (taggedCarbon parity) := rfl

theorem ringRaw_atomAt_one (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).atomAt? 1 =
      some { AtomSpec.aliphatic .F with explicitHydrogens? := some 0 } := rfl

theorem ringRaw_atomAt_two (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).atomAt? 2 = some (carbon 1) := rfl

theorem ringRaw_atomAt_three (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).atomAt? 3 =
      some { AtomSpec.aliphatic .Cl with explicitHydrogens? := some 0 } := rfl

theorem ringRaw_atomAt_chain (n : ℕ) (parity : TetrahedralInputParity) (k : ℕ) (hk : k ≤ n) :
    (ringRaw n parity).atomAt? (k + 4) = some (carbon 2) := by
  show listGet? (ringAtoms n parity) (k + 4) = some (carbon 2)
  rw [ringAtoms]
  rw [show k + 4 = (ringPrefix parity).length + k by rw [ringPrefix_length]; omega]
  rw [listGet?_append_right]
  unfold ringTail
  rw [listGet?_replicate]
  rw [if_pos (by omega)]

theorem ringRaw_atomAt?_bounded (n : Nat) (parity : TetrahedralInputParity) {idx : Nat}
    {atom : AtomSpec} (lookup : (ringRaw n parity).atomAt? idx = some atom) : idx < n + 5 := by
  have bound := listGet?_eq_some_implies_lt (ringRaw n parity).atoms idx atom lookup
  change idx < (ringRaw n parity).atomCount at bound
  rw [TetraStereo.UniversalProof.NativeRingDomain.atom_count n parity] at bound
  exact bound

theorem ringRaw_atom_element_ordinary (n : ℕ) (parity : TetrahedralInputParity) :
    ∀ atom ∈ (ringRaw n parity).atoms, atom.element ≠ Element.wildcard ∧ atom.aromatic = false := by
  intro atom hmem
  rw [ringRaw_atoms] at hmem
  unfold ringAtoms at hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · unfold ringPrefix at hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl <;>
      simp [taggedCarbon, carbon, AtomSpec.aliphatic]
  · unfold ringTail at hmem
    have : atom = carbon 2 := (List.mem_replicate.mp hmem).2
    subst this
    simp [carbon, AtomSpec.aliphatic]

theorem ringRaw_hydrogen_inventory (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).atoms.map AtomSpec.explicitHydrogens =
      hydrogenInventory n :=
  hydrogen_inventory_actual_atoms n parity

theorem ringRaw_hydrogen_count (n : ℕ) (parity : TetrahedralInputParity) :
    ((ringRaw n parity).atoms.map AtomSpec.explicitHydrogens).sum = 2 * n + 4 := by
  rw [ringRaw_hydrogen_inventory]
  exact hydrogen_count n

theorem rule2Mass_carbon : ∃ mass, RawMolecule.rule2MassPico? Element.C none = some mass := by
  obtain ⟨mass, h⟩ := CIPRule2MassData.every_current_atomic_number_has_an_ordinary_value 6 (by decide)
  exact ⟨mass, by simpa [RawMolecule.rule2MassPico?, Element.atomicNumber] using h⟩

theorem rule2Mass_fluorine : ∃ mass, RawMolecule.rule2MassPico? Element.F none = some mass := by
  obtain ⟨mass, h⟩ := CIPRule2MassData.every_current_atomic_number_has_an_ordinary_value 9 (by decide)
  exact ⟨mass, by simpa [RawMolecule.rule2MassPico?, Element.atomicNumber] using h⟩

theorem rule2Mass_chlorine : ∃ mass, RawMolecule.rule2MassPico? Element.Cl none = some mass := by
  obtain ⟨mass, h⟩ := CIPRule2MassData.every_current_atomic_number_has_an_ordinary_value 17 (by decide)
  exact ⟨mass, by simpa [RawMolecule.rule2MassPico?, Element.atomicNumber] using h⟩

theorem ringRaw_rule2MassesKnown (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).Rule2MassesKnown := by
  intro atom hmem
  rw [ringRaw_atoms] at hmem
  unfold ringAtoms at hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · unfold ringPrefix at hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact rule2Mass_carbon
    · exact rule2Mass_fluorine
    · exact rule2Mass_carbon
    · exact rule2Mass_chlorine
  · unfold ringTail at hmem
    have : atom = carbon 2 := (List.mem_replicate.mp hmem).2
    subst this
    exact rule2Mass_carbon

theorem mem_ringBonds (n : ℕ) (b : RawBond) :
    b ∈ ringBonds n ↔
      b = ⟨0, 1, ParsedBondKind.single⟩ ∨ b = ⟨0, 2, ParsedBondKind.single⟩ ∨
        b = ⟨2, 3, ParsedBondKind.single⟩ ∨
        (∃ j, j < n + 1 ∧ chainBond j = b) ∨ b = closureBond n := by
  unfold ringBonds chainBonds
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
    List.mem_map, List.mem_range, or_assoc]

theorem chainBond_source_eq (j : ℕ) :
    (chainBond j).source = if j = 0 then 2 else j + 3 := rfl

theorem chainBond_target_eq (j : ℕ) : (chainBond j).target = j + 4 := rfl

theorem ringBonds_kind_single (n : ℕ) :
    ∀ b ∈ ringBonds n, b.kind = ParsedBondKind.single := by
  intro b hb
  rw [mem_ringBonds] at hb
  rcases hb with rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl <;> rfl

theorem prefix0_mem (n : ℕ) : (⟨0, 1, ParsedBondKind.single⟩ : RawBond) ∈ ringBonds n := by
  rw [mem_ringBonds]; exact Or.inl rfl

theorem prefix1_mem (n : ℕ) : (⟨0, 2, ParsedBondKind.single⟩ : RawBond) ∈ ringBonds n := by
  rw [mem_ringBonds]; exact Or.inr (Or.inl rfl)

theorem prefix2_mem (n : ℕ) : (⟨2, 3, ParsedBondKind.single⟩ : RawBond) ∈ ringBonds n := by
  rw [mem_ringBonds]; exact Or.inr (Or.inr (Or.inl rfl))

theorem chainBond_mem (n j : ℕ) (hj : j < n + 1) : chainBond j ∈ ringBonds n := by
  rw [mem_ringBonds]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, hj, rfl⟩)))

theorem closureBond_mem (n : ℕ) : closureBond n ∈ ringBonds n := by
  rw [mem_ringBonds]; exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem ringBonds_orientation (n : ℕ) (b : RawBond) (hb : b ∈ ringBonds n) :
    b.source < b.target ∨ b = closureBond n := by
  rw [mem_ringBonds] at hb
  rcases hb with rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl
  · left; decide
  · left; decide
  · left; decide
  · left
    rw [chainBond_source_eq, chainBond_target_eq]
    by_cases h : j = 0 <;> simp only [h, if_true, if_false] <;> omega
  · right; rfl

theorem chainBond_bounds (n j : ℕ) (hj : j < n + 1) :
    (chainBond j).source < n + 5 ∧ (chainBond j).target < n + 5 ∧
      (chainBond j).source ≠ (chainBond j).target := by
  rw [chainBond_source_eq, chainBond_target_eq]
  by_cases h : j = 0 <;> simp only [h, if_true, if_false] <;> omega

theorem ringBonds_bounds (n : ℕ) (b : RawBond) (hb : b ∈ ringBonds n) :
    b.source < n + 5 ∧ b.target < n + 5 ∧ b.source ≠ b.target := by
  rw [mem_ringBonds] at hb
  rcases hb with rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl
  · change 0 < n + 5 ∧ 1 < n + 5 ∧ (0 : ℕ) ≠ 1
    omega
  · change 0 < n + 5 ∧ 2 < n + 5 ∧ (0 : ℕ) ≠ 2
    omega
  · change 2 < n + 5 ∧ 3 < n + 5 ∧ (2 : ℕ) ≠ 3
    omega
  · exact chainBond_bounds n j hj
  · change n + 4 < n + 5 ∧ 0 < n + 5 ∧ n + 4 ≠ 0
    omega

theorem ringRaw_wellFormed (n : Nat) (parity : TetrahedralInputParity) :
    (ringRaw n parity).WellFormed := by
  intro bond member
  have bounds := ringBonds_bounds n bond (by simpa only [ringRaw_bonds] using member)
  simpa only [RawMolecule.BondEndpointsOK, atom_count n parity] using bounds

theorem range_map_nodup {α : Type} {f : ℕ → α} {k : ℕ}
    (hinj : ∀ a b, a < k → b < k → f a = f b → a = b) :
    ((List.range k).map f).Nodup :=
  (List.nodup_map_iff_inj_on List.nodup_range).mpr
    (fun a ha b hb h => hinj a b (List.mem_range.mp ha) (List.mem_range.mp hb) h)

theorem chainBonds_nodup (n : ℕ) : (chainBonds n).Nodup := by
  unfold chainBonds
  exact range_map_nodup (fun a b _ _ h => by
    have := congrArg RawBond.target h
    rw [chainBond_target_eq, chainBond_target_eq] at this
    omega)

theorem ringPrefix_nodup : (([⟨0, 1, ParsedBondKind.single⟩, ⟨0, 2, ParsedBondKind.single⟩,
    ⟨2, 3, ParsedBondKind.single⟩] : List RawBond)).Nodup := by decide

theorem ringPrefix_disjoint_chain (n : ℕ) :
    (([⟨0, 1, ParsedBondKind.single⟩, ⟨0, 2, ParsedBondKind.single⟩,
        ⟨2, 3, ParsedBondKind.single⟩] : List RawBond)).Disjoint (chainBonds n) := by
  apply List.disjoint_left.mpr
  intro b hb hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
  rw [chainBonds] at hc
  rcases List.mem_map.mp hc with ⟨j, hj, chain_eq⟩
  rcases hb with hb | hb | hb
  · subst hb
    have hsrc := congrArg RawBond.source chain_eq
    rw [chainBond_source_eq] at hsrc
    by_cases h : j = 0 <;> simp only [h, if_true, if_false] at hsrc <;> omega
  · subst hb
    have hsrc := congrArg RawBond.source chain_eq
    rw [chainBond_source_eq] at hsrc
    by_cases h : j = 0 <;> simp only [h, if_true, if_false] at hsrc <;> omega
  · subst hb
    have htgt := congrArg RawBond.target chain_eq
    rw [chainBond_target_eq] at htgt
    change j + 4 = 3 at htgt
    omega

theorem ringPrefix_disjoint_closure (n : ℕ) :
    (([⟨0, 1, ParsedBondKind.single⟩, ⟨0, 2, ParsedBondKind.single⟩,
        ⟨2, 3, ParsedBondKind.single⟩] : List RawBond)).Disjoint [closureBond n] := by
  apply List.disjoint_left.mpr
  intro b hb hc
  simp only [List.mem_singleton] at hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> unfold closureBond at hc <;> injection hc with hs ht <;> omega

theorem chainBonds_disjoint_closure (n : ℕ) : (chainBonds n).Disjoint [closureBond n] := by
  apply List.disjoint_left.mpr
  intro b hb hc
  simp only [List.mem_singleton] at hc
  rw [chainBonds] at hb
  rcases List.mem_map.mp hb with ⟨j, hj, rfl⟩
  have htgt := congrArg RawBond.target hc
  rw [chainBond_target_eq] at htgt
  change j + 4 = 0 at htgt
  omega

theorem ringBonds_nodup (n : ℕ) : (ringBonds n).Nodup := by
  have h1 : (chainBonds n ++ [closureBond n]).Nodup :=
    List.nodup_append'.mpr ⟨chainBonds_nodup n, List.nodup_singleton _,
      chainBonds_disjoint_closure n⟩
  have h2 : (([⟨0, 1, ParsedBondKind.single⟩, ⟨0, 2, ParsedBondKind.single⟩,
      ⟨2, 3, ParsedBondKind.single⟩] : List RawBond)
        ++ (chainBonds n ++ [closureBond n])).Nodup :=
    List.nodup_append'.mpr ⟨ringPrefix_nodup, h1, by
      rw [List.disjoint_left]
      intro a ha hb
      rcases List.mem_append.mp hb with hb | hb
      · exact (List.disjoint_left.mp (ringPrefix_disjoint_chain n)) ha hb
      · exact (List.disjoint_left.mp (ringPrefix_disjoint_closure n)) ha hb⟩
  simpa only [ringBonds, List.append_assoc] using h2

theorem edgeKey_eq_of_lt {b : RawBond} (h : b.source < b.target) :
    b.edgeKey = (b.source, b.target) := by
  unfold RawBond.edgeKey
  rw [Nat.min_eq_left (Nat.le_of_lt h), Nat.max_eq_right (Nat.le_of_lt h)]

theorem eq_of_edgeKey_eq {b₁ b₂ : RawBond} (h₁ : b₁.source < b₁.target)
    (h₂ : b₂.source < b₂.target)
    (k₁ : b₁.kind = ParsedBondKind.single) (k₂ : b₂.kind = ParsedBondKind.single)
    (hk : b₁.edgeKey = b₂.edgeKey) : b₁ = b₂ := by
  rw [edgeKey_eq_of_lt h₁, edgeKey_eq_of_lt h₂] at hk
  injection hk with hs ht
  cases b₁; cases b₂; simp_all

theorem closure_edgeKey (n : ℕ) : (closureBond n).edgeKey = (0, n + 4) := by
  change (min (n + 4) 0, max (n + 4) 0) = (0, n + 4)
  simp only [Nat.min_zero, Nat.max_zero]

theorem ringBonds_closure_of_edgeKey (n : ℕ) :
    ∀ b ∈ ringBonds n, b.edgeKey = (0, n + 4) → b = closureBond n := by
  intro b hb hk
  rw [mem_ringBonds] at hb
  rcases hb with rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl
  · exfalso
    change ((0, 1) : ℕ × ℕ) = (0, n + 4) at hk
    have ht := congrArg Prod.snd hk
    change 1 = n + 4 at ht
    omega
  · exfalso
    change ((0, 2) : ℕ × ℕ) = (0, n + 4) at hk
    have ht := congrArg Prod.snd hk
    change 2 = n + 4 at ht
    omega
  · exfalso
    change ((2, 3) : ℕ × ℕ) = (0, n + 4) at hk
    have ht := congrArg Prod.snd hk
    change 3 = n + 4 at ht
    omega
  · exfalso
    rw [show (chainBond j).edgeKey =
        (min (chainBond j).source (chainBond j).target,
         max (chainBond j).source (chainBond j).target) from rfl] at hk
    injection hk with h1 h2
    rw [chainBond_source_eq, chainBond_target_eq] at h1
    by_cases h : j = 0
    · simp only [h, if_true] at h1
      exact absurd h1 (by decide)
    · simp only [h, if_false] at h1
      rw [Nat.min_eq_left (by omega : j + 3 ≤ j + 4)] at h1
      omega
  · rfl

theorem ringBonds_edgeKey_inj (n : ℕ) :
    ∀ a ∈ ringBonds n, ∀ b ∈ ringBonds n, a.edgeKey = b.edgeKey → a = b := by
  intro a ha b hb hk
  have ha' := ringBonds_orientation n a ha
  have hb' := ringBonds_orientation n b hb
  rcases ha' with ha_lt | ha_close
  · rcases hb' with hb_lt | hb_close
    · exact eq_of_edgeKey_eq ha_lt hb_lt (ringBonds_kind_single n a ha)
        (ringBonds_kind_single n b hb) hk
    · subst hb_close
      have : a = closureBond n :=
        ringBonds_closure_of_edgeKey n a ha (by rw [hk, closure_edgeKey n])
      subst this; rfl
  · subst ha_close
    have : b = closureBond n :=
      ringBonds_closure_of_edgeKey n b hb (by rw [← hk, closure_edgeKey n])
    subst this; rfl

theorem ringRaw_bondRecordsUnique (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).BondRecordsUnique := by
  change ((ringBonds n).map RawBond.edgeKey).Nodup
  exact (List.nodup_map_iff_inj_on (ringBonds_nodup n)).mpr
    (fun a ha b hb hk => ringBonds_edgeKey_inj n a ha b hb hk)

theorem ringRaw_admissible (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).Admissible :=
  ⟨ringRaw_wellFormed n parity, ringRaw_bondRecordsUnique n parity⟩

end TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
