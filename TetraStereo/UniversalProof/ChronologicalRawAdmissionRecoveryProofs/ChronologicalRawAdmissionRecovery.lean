import TetraStereo.UniversalProof.NativeFamilyRawSupport
import TetraStereo.OneCenter.ExplicitHydrogens

set_option autoImplicit false

namespace TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeFamilyRawSupportProofs.PositiveFamilyGeneratorRecovery






















/-! ## The independent per-row invariant -/

/-- Relational exactness of the stored written row at one real index: the row is duplicate-free,
every listed neighbour is a real atom, and row membership agrees with actual positive raw
`bondOrder` adjacency.  This is an input invariant, never a desired output. -/
def WrittenRowExactAt (mol : RawMolecule) (i : ℕ) : Prop :=
  (mol.writtenNeighbors i).Nodup ∧
    (∀ ligand, ligand ∈ mol.writtenNeighbors i → ligand < mol.atomCount) ∧
    (∀ ligand, ligand < mol.atomCount →
      (ligand ∈ mol.writtenNeighbors i ↔ 0 < mol.bondOrder i ligand))

/-- The complete independent input invariant of a stored written-neighbour table: the table has
exactly one stored row per real atom, and every real row satisfies `WrittenRowExactAt`. -/
def StoredRowExact (mol : RawMolecule) : Prop :=
  mol.neighborOrder.length = mol.atomCount ∧
    ∀ i : Fin mol.atomCount, WrittenRowExactAt mol i.val

/-! ## Chronological fresh-child append -/

/-- The stored written row of one atom after a fresh-child append.  Real old indices keep their
old written row, the designated parent additionally carries the fresh child, and the fresh index
carries the parent's singleton row. -/
def appendedRow (mol : RawMolecule) (parent : Fin mol.atomCount) (i : ℕ) : List ℕ :=
  if i < mol.atomCount then
    mol.writtenNeighbors i ++ (if i = parent.val then [mol.atomCount] else [])
  else [parent.val]

/-- The ordinary single bond introduced by one append step. -/
def freshBond (mol : RawMolecule) (parent : Fin mol.atomCount) : RawBond :=
  { source := parent.val, target := mol.atomCount, kind := ParsedBondKind.single }

/-- One actual chronological append step: a fresh child atom, the ordinary single
(parent, fresh) edge, the parent's stored row extended by the fresh index, and the child's
singleton written row. -/
def appendFreshChild (mol : RawMolecule) (parent : Fin mol.atomCount) (child : AtomSpec) :
    RawMolecule where
  atoms := mol.atoms ++ [child]
  bonds := mol.bonds ++ [freshBond mol parent]
  neighborOrder := (List.range (mol.atomCount + 1)).map (appendedRow mol parent)
  introductionPredecessors :=
    if mol.introductionPredecessors.length = mol.atomCount then
      mol.introductionPredecessors ++ [some parent.val]
    else mol.introductionPredecessors

@[simp] theorem appendFreshChild_atoms (mol : RawMolecule) (parent : Fin mol.atomCount)
    (child : AtomSpec) :
    (appendFreshChild mol parent child).atoms = mol.atoms ++ [child] := rfl

@[simp] theorem appendFreshChild_bonds (mol : RawMolecule) (parent : Fin mol.atomCount)
    (child : AtomSpec) :
    (appendFreshChild mol parent child).bonds = mol.bonds ++ [freshBond mol parent] := rfl

theorem appendFreshChild_atomCount (mol : RawMolecule) (parent : Fin mol.atomCount)
    (child : AtomSpec) :
    (appendFreshChild mol parent child).atomCount = mol.atomCount + 1 := by
  simp [RawMolecule.atomCount, appendFreshChild]

theorem appendedRow_old (mol : RawMolecule) (parent : Fin mol.atomCount) {i : ℕ}
    (h : i < mol.atomCount) :
    appendedRow mol parent i =
      mol.writtenNeighbors i ++ (if i = parent.val then [mol.atomCount] else []) := by
  unfold appendedRow
  rw [if_pos h]

theorem appendedRow_fresh (mol : RawMolecule) (parent : Fin mol.atomCount) {i : ℕ}
    (h : ¬ i < mol.atomCount) :
    appendedRow mol parent i = [parent.val] := by
  unfold appendedRow
  rw [if_neg h]

/-- The written-neighbour projection of one append step at any real new index. -/
theorem appendFreshChild_writtenNeighbors (mol : RawMolecule) (parent : Fin mol.atomCount)
    (child : AtomSpec) (i : ℕ) (h : i < mol.atomCount + 1) :
    (appendFreshChild mol parent child).writtenNeighbors i = appendedRow mol parent i := by
  unfold RawMolecule.writtenNeighbors appendFreshChild
  change (match ((List.range (mol.atomCount + 1)).map (appendedRow mol parent))[i]? with
    | some order => order
    | none => _) = appendedRow mol parent i
  rw [getElem?_map_range _ _ _ h]

/-! ## Positivity characterisation of raw bond order -/

/-- `connects` is the unordered or of the two directed incidence tests. -/
theorem connects_eq_or_directed (bond : RawBond) (u v : ℕ) :
    bond.connects u v = (bond.directedConnects u v || bond.directedConnects v u) := rfl

/-- Directed bond order is positive exactly at a bond written in that direction. -/
theorem directedBondOrder_pos_iff_connect (mol : RawMolecule) (u v : ℕ) :
    0 < mol.directedBondOrder u v ↔
      ∃ bond ∈ mol.bonds, bond.directedConnects u v = true := by
  constructor
  · intro h
    obtain ⟨bond, hb, hs, ht⟩ := exists_connecting_of_directedBondOrder_pos mol h
    exact ⟨bond, hb, by simp [RawBond.directedConnects, hs, ht]⟩
  · rintro ⟨bond, hb, hc⟩
    simp only [RawBond.directedConnects, Bool.and_eq_true, beq_iff_eq] at hc
    exact directedBondOrder_pos_of_connect mol bond hb hc.1 hc.2

theorem zero_lt_max (a b : ℕ) : 0 < max a b ↔ 0 < a ∨ 0 < b := by
  constructor
  · intro h
    rcases Nat.lt_or_ge a b with hab | hba
    · right; rwa [max_eq_right (le_of_lt hab)] at h
    · left; rwa [max_eq_left hba] at h
  · rintro (h | h)
    · exact lt_of_lt_of_le h (le_max_left a b)
    · exact lt_of_lt_of_le h (le_max_right a b)

/-- Raw `bondOrder` is positive exactly at a distinct pair carrying an actual connecting bond. -/
theorem bondOrder_pos_iff_connect (mol : RawMolecule) (left right : ℕ) :
    0 < mol.bondOrder left right ↔
      left ≠ right ∧ ∃ bond ∈ mol.bonds, bond.connects left right = true := by
  unfold RawMolecule.bondOrder
  by_cases hne : left = right
  · subst hne; simp
  · rw [if_neg hne, zero_lt_max, directedBondOrder_pos_iff_connect,
      directedBondOrder_pos_iff_connect]
    have hexp :
        (∃ bond ∈ mol.bonds, bond.directedConnects left right = true) ∨
            (∃ bond ∈ mol.bonds, bond.directedConnects right left = true) ↔
          ∃ bond ∈ mol.bonds, bond.connects left right = true := by
      constructor
      · rintro (⟨bond, hb, hc⟩ | ⟨bond, hb, hc⟩)
        · exact ⟨bond, hb, by rw [connects_eq_or_directed]; simp [hc]⟩
        · exact ⟨bond, hb, by rw [connects_eq_or_directed]; simp [hc]⟩
      · rintro ⟨bond, hb, hc⟩
        rw [connects_eq_or_directed, Bool.or_eq_true] at hc
        rcases hc with hc | hc
        · exact Or.inl ⟨bond, hb, hc⟩
        · exact Or.inr ⟨bond, hb, hc⟩
    rw [hexp]
    constructor
    · intro h; exact ⟨hne, h⟩
    · rintro ⟨-, h⟩; exact h

/-! ## Bond-order behaviour of one append step -/

theorem appendFreshChild_bondOrder_pos_old (mol : RawMolecule) (parent : Fin mol.atomCount)
    (child : AtomSpec) {u v : ℕ} (hu : u < mol.atomCount) (hv : v < mol.atomCount) :
    0 < (appendFreshChild mol parent child).bondOrder u v ↔ 0 < mol.bondOrder u v := by
  rw [bondOrder_pos_iff_connect, bondOrder_pos_iff_connect, appendFreshChild_bonds]
  constructor
  · rintro ⟨hne, ⟨bond, hmem, hconn⟩⟩
    rcases List.mem_append.mp hmem with hold | hnew
    · exact ⟨hne, bond, hold, hconn⟩
    · rw [List.mem_singleton] at hnew
      subst hnew
      unfold freshBond at hconn
      simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq] at hconn
      omega
  · rintro ⟨hne, ⟨bond, hb, hc⟩⟩
    exact ⟨hne, bond, List.mem_append_left _ hb, hc⟩

/-- A real old atom is adjacent to the fresh index exactly when it is the parent. -/
theorem appendFreshChild_bondOrder_pos_fresh_right (mol : RawMolecule)
    (parent : Fin mol.atomCount) (child : AtomSpec) (hwf : mol.WellFormed) {c : ℕ}
    (hc : c < mol.atomCount) :
    0 < (appendFreshChild mol parent child).bondOrder c mol.atomCount ↔ c = parent.val := by
  rw [bondOrder_pos_iff_connect, appendFreshChild_bonds]
  constructor
  · rintro ⟨hne, ⟨bond, hmem, hconn⟩⟩
    rcases List.mem_append.mp hmem with hold | hnew
    · have hb := hwf bond hold
      rcases hb with ⟨hsrc, htgt, _⟩
      simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq] at hconn
      rcases hconn with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> omega
    · rw [List.mem_singleton] at hnew
      subst hnew
      unfold freshBond at hconn
      simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq] at hconn
      rcases hconn with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h1.symm
      · omega
  · intro hceq
    refine ⟨by omega, ?_⟩
    refine ⟨freshBond mol parent, List.mem_append_right _ (by simp), ?_⟩
    subst hceq
    unfold freshBond
    simp [RawBond.connects]

/-- The fresh index is adjacent to a real old atom exactly when that atom is the parent. -/
theorem appendFreshChild_bondOrder_pos_fresh_left (mol : RawMolecule)
    (parent : Fin mol.atomCount) (child : AtomSpec) (hwf : mol.WellFormed) {l : ℕ}
    (hl : l < mol.atomCount) :
    0 < (appendFreshChild mol parent child).bondOrder mol.atomCount l ↔ l = parent.val := by
  rw [bondOrder_pos_iff_connect, appendFreshChild_bonds]
  constructor
  · rintro ⟨hne, ⟨bond, hmem, hconn⟩⟩
    rcases List.mem_append.mp hmem with hold | hnew
    · have hb := hwf bond hold
      rcases hb with ⟨hsrc, htgt, _⟩
      simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq] at hconn
      rcases hconn with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> omega
    · rw [List.mem_singleton] at hnew
      subst hnew
      unfold freshBond at hconn
      simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq] at hconn
      rcases hconn with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hplt := parent.isLt
        omega
      · exact h1.symm
  · intro hle
    refine ⟨by omega, ?_⟩
    refine ⟨freshBond mol parent, List.mem_append_right _ (by simp), ?_⟩
    subst hle
    unfold freshBond
    simp [RawBond.connects]

/-! ## Relational written-adjacency preservation (headline) -/

theorem appendFreshChild_storedRowExact (mol : RawMolecule) (parent : Fin mol.atomCount)
    (child : AtomSpec) (hwf : mol.WellFormed) (hrows : StoredRowExact mol) :
    StoredRowExact (appendFreshChild mol parent child) := by
  constructor
  · simp [appendFreshChild, RawMolecule.atomCount]
  · intro i
    unfold WrittenRowExactAt
    have iBound : i.val < mol.atomCount + 1 := by
      simpa only [appendFreshChild_atomCount] using i.isLt
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp iBound) with hlt | heq
    · have hrow := hrows.2 ⟨i.val, hlt⟩
      have hwn : (appendFreshChild mol parent child).writtenNeighbors i.val =
          mol.writtenNeighbors i.val ++
            (if i.val = parent.val then [mol.atomCount] else []) := by
        rw [appendFreshChild_writtenNeighbors mol parent child i.val iBound]
        exact appendedRow_old mol parent hlt
      rw [hwn]
      by_cases hp : i.val = parent.val
      · rw [if_pos hp]
        refine ⟨?_, ?_, ?_⟩
        · rw [List.nodup_append]
          refine ⟨hrow.1, by simp, ?_⟩
          intro a ha b hb
          rw [List.mem_singleton] at hb
          subst hb
          have := hrow.2.1 a ha
          omega
        · intro l hl
          rw [List.mem_append, List.mem_singleton] at hl
          rw [appendFreshChild_atomCount]
          rcases hl with hl | rfl
          · exact Nat.lt_trans (hrow.2.1 l hl) (Nat.lt_succ_self _)
          · exact Nat.lt_succ_self _
        · intro l hl
          rw [appendFreshChild_atomCount] at hl
          rw [List.mem_append, List.mem_singleton]
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hl) with hln | hln
          · rw [hrow.2.2 l hln, appendFreshChild_bondOrder_pos_old mol parent child hlt hln]
            constructor
            · intro h; rcases h with h | h
              · exact h
              · omega
            · intro h; exact Or.inl h
          · subst hln
            constructor
            · intro _
              rw [appendFreshChild_bondOrder_pos_fresh_right mol parent child hwf hlt]
              exact hp
            · intro _; exact Or.inr rfl
      · rw [if_neg hp, List.append_nil]
        refine ⟨hrow.1, ?_, ?_⟩
        · intro l hl
          rw [appendFreshChild_atomCount]
          exact Nat.lt_trans (hrow.2.1 l hl) (Nat.lt_succ_self _)
        · intro l hl
          rw [appendFreshChild_atomCount] at hl
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hl) with hln | hln
          · rw [hrow.2.2 l hln, appendFreshChild_bondOrder_pos_old mol parent child hlt hln]
          · rw [hln]
            constructor
            · intro hmem
              have := hrow.2.1 mol.atomCount hmem
              omega
            · intro hpos
              exact absurd
                ((appendFreshChild_bondOrder_pos_fresh_right mol parent child hwf hlt).mp hpos) hp
    · rw [heq]
      have hwn : (appendFreshChild mol parent child).writtenNeighbors mol.atomCount = [parent.val] := by
        rw [appendFreshChild_writtenNeighbors mol parent child mol.atomCount
          (Nat.lt_succ_self _)]
        exact appendedRow_fresh mol parent (Nat.lt_irrefl _)
      rw [hwn]
      refine ⟨by simp, ?_, ?_⟩
      · intro l hl
        rw [List.mem_singleton] at hl
        subst hl
        rw [appendFreshChild_atomCount]
        exact Nat.lt_succ_of_lt parent.isLt
      · intro l hl
        rw [appendFreshChild_atomCount] at hl
        rw [List.mem_singleton]
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hl) with hln | hln
        · rw [appendFreshChild_bondOrder_pos_fresh_left mol parent child hwf hln]
        · rw [hln]
          unfold RawMolecule.bondOrder
          rw [if_pos rfl]
          constructor
          · intro hmem
            exact absurd hmem.symm (Nat.ne_of_lt parent.isLt)
          · intro hpos
            exact absurd hpos (Nat.lt_irrefl 0)

/-- Executable reflection: the fresh-child append of an actually well-formed molecule with a stored
per-row exact table is itself `WrittenNeighborExact` for the real new atom count. -/
theorem appendFreshChild_writtenNeighborExact (mol : RawMolecule) (parent : Fin mol.atomCount)
    (child : AtomSpec) (hwf : mol.WellFormed) (hrows : StoredRowExact mol) :
    (appendFreshChild mol parent child).WrittenNeighborExact := by
  apply WrittenNeighborExact.of_at
  intro center
  have h := (appendFreshChild_storedRowExact mol parent child hwf hrows).2 center
  refine ⟨h.1, ?_, ?_⟩
  · intro ligand hl; exact h.2.1 ligand hl
  · intro ligand; exact h.2.2 ligand.val ligand.isLt

/-! ## Bridge from the accepted executable reflection -/

/-- An accepted `WrittenNeighborExact` real molecule yields the independent per-row invariant,
so the preserved append theorem consumes only genuinely independent inputs. -/
theorem writtenRowExactAt_of_writtenNeighborExact (mol : RawMolecule)
    (hexact : mol.WrittenNeighborExact) (i : ℕ) (hi : i < mol.atomCount) :
    WrittenRowExactAt mol i := by
  have h := WrittenNeighborExact.at mol hexact ⟨i, hi⟩
  exact ⟨h.1, fun l hl => h.2.1 l hl, fun l hl => h.2.2 ⟨l, hl⟩⟩

theorem storedRowExact_of_writtenExact (mol : RawMolecule)
    (hcount : mol.neighborOrder.length = mol.atomCount)
    (hexact : mol.WrittenNeighborExact) : StoredRowExact mol :=
  ⟨hcount, fun i => writtenRowExactAt_of_writtenNeighborExact mol hexact i.val i.isLt⟩

/-! ## Unordered edge uniqueness is preserved separately -/

theorem appendFreshChild_bondRecordsUnique (mol : RawMolecule) (parent : Fin mol.atomCount)
    (child : AtomSpec) (hwf : mol.WellFormed) (huniq : mol.BondRecordsUnique) :
    (appendFreshChild mol parent child).BondRecordsUnique := by
  unfold RawMolecule.BondRecordsUnique at huniq ⊢
  rw [appendFreshChild_bonds, List.map_append, List.nodup_append]
  refine ⟨huniq, by simp, ?_⟩
  intro a ha b hb
  obtain ⟨bond, hmem, rfl⟩ := List.mem_map.mp ha
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
  subst hb
  have hb' := hwf bond hmem
  have hfreshKey : RawBond.edgeKey (freshBond mol parent) = (parent.val, mol.atomCount) := by
    unfold freshBond RawBond.edgeKey
    rw [Nat.min_eq_left (le_of_lt parent.isLt), Nat.max_eq_right (le_of_lt parent.isLt)]
  intro hab
  have hsnd := congrArg Prod.snd hab
  rw [hfreshKey] at hsnd
  change max bond.source bond.target = mol.atomCount at hsnd
  have hmax : max bond.source bond.target < mol.atomCount := max_lt hb'.1 hb'.2.1
  omega

end TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery
