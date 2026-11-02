import TetraStereo.UniversalProof.NativeSingleBondRawSupport
import TetraStereo.UniversalProof.GeneralParserStateBridge
import TetraStereo.UniversalProof.ChronologicalFamilyRuntimeSourceBridge
import TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.ChronologicalFamilyPhysicalBridge

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.GeneralParserStateBridge
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery









/-- Independent six-atom block: backbone C, backbone H, tagged C, pendant H, F, Br. -/
def blockAtoms (parity : TetrahedralInputParity) : List AtomSpec :=
  [atomSpec .carbon, atomSpec .hydrogen, atomSpec (.taggedCarbon parity), atomSpec .hydrogen,
    atomSpec .fluorine, atomSpec .bromine]

/-- Independent chronological flat map of the six-atom blocks. -/
def roleAtoms : List TetrahedralInputParity → List AtomSpec
  | [] => []
  | parity :: rest => blockAtoms parity ++ roleAtoms rest

/-- Specification-level description of the six internal block offsets, independent of parsing. -/
def blockAtomSpec (parity : TetrahedralInputParity) (offset : ℕ) : AtomSpec :=
  match offset with
  | 0 => atomSpec .carbon
  | 1 => atomSpec .hydrogen
  | 2 => atomSpec (.taggedCarbon parity)
  | 3 => atomSpec .hydrogen
  | 4 => atomSpec .fluorine
  | _ => atomSpec .bromine

/-- The eight independent traversal roles of one family raw molecule. -/
inductive TraversalRole (parities : List TetrahedralInputParity) where
  | leftHydrogen
  | rightHydrogen
  | backbone (index : Fin parities.length)
  | backboneHydrogen (index : Fin parities.length)
  | taggedCarbon (index : Fin parities.length)
  | pendantHydrogen (index : Fin parities.length)
  | pendantFluorine (index : Fin parities.length)
  | pendantBromine (index : Fin parities.length)

/-- Independent written index of every role. -/
def roleIndex {ps : List TetrahedralInputParity} : TraversalRole ps → ℕ
  | .leftHydrogen => 0
  | .rightHydrogen => 6 * ps.length + 1
  | .backbone i => 1 + 6 * (i : ℕ)
  | .backboneHydrogen i => 2 + 6 * (i : ℕ)
  | .taggedCarbon i => 3 + 6 * (i : ℕ)
  | .pendantHydrogen i => 4 + 6 * (i : ℕ)
  | .pendantFluorine i => 5 + 6 * (i : ℕ)
  | .pendantBromine i => 6 + 6 * (i : ℕ)

/-- Independent atom specification of every role, exact in the tagged input parity. -/
def roleSpec {ps : List TetrahedralInputParity} : TraversalRole ps → AtomSpec
  | .leftHydrogen => atomSpec .hydrogen
  | .rightHydrogen => atomSpec .hydrogen
  | .backbone _ => atomSpec .carbon
  | .backboneHydrogen _ => atomSpec .hydrogen
  | .taggedCarbon i => atomSpec (.taggedCarbon (ps.get i))
  | .pendantHydrogen _ => atomSpec .hydrogen
  | .pendantFluorine _ => atomSpec .fluorine
  | .pendantBromine _ => atomSpec .bromine

/-- The requested parity carried by a role, when it is a tag role. -/
def roleParity? {ps : List TetrahedralInputParity} : TraversalRole ps → Option TetrahedralInputParity
  | .taggedCarbon i => some (ps.get i)
  | _ => none

/-- A bound offset selects one of the six internal roles at position `index`. -/
def internalRole (parities : List TetrahedralInputParity) (index : Fin parities.length)
    (offset : ℕ) : TraversalRole parities :=
  match offset with
  | 0 => .backbone index
  | 1 => .backboneHydrogen index
  | 2 => .taggedCarbon index
  | 3 => .pendantHydrogen index
  | 4 => .pendantFluorine index
  | _ => .pendantBromine index

theorem roleSpec_parity {parities : List TetrahedralInputParity}
    (role : TraversalRole parities) :
    (roleSpec role).tetrahedral? = roleParity? role := by
  cases role <;> rfl

/-! ### Raw append record projections -/

theorem blockResult_atoms (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) :
    (blockResult state parent parity).atoms = state.atoms ++ blockAtoms parity := by
  exact TetraStereo.UniversalProof.ChronologicalFamilyRuntimeSourceBridge.blockResult_atoms
    state parent parity

theorem blocksResult_atoms (parities : List TetrahedralInputParity) (state : ParseState)
    (parent : ℕ) :
    (blocksResult parities state parent).atoms = state.atoms ++ roleAtoms parities := by
  induction parities generalizing state parent with
  | nil => exact (List.append_nil state.atoms).symm
  | cons parity rest ih =>
      simp only [blocksResult]
      rw [ih, blockResult_atoms]
      simp only [roleAtoms, List.append_assoc]

theorem roleAtoms_length (parities : List TetrahedralInputParity) :
    (roleAtoms parities).length = 6 * parities.length := by
  induction parities with
  | nil => rfl
  | cons parity rest ih =>
      simp only [roleAtoms, List.length_append, ih, blockAtoms, List.length_cons,
        List.length_nil]
      omega

/-- Independent atom-list identity of the whole family raw molecule. -/
theorem familyRaw_atoms (parities : List TetrahedralInputParity) :
    (familyRaw parities).atoms =
      [atomSpec .hydrogen] ++ roleAtoms parities ++ [atomSpec .hydrogen] := by
  change ((blocksResult parities initialHydrogenState 0).atoms ++ [atomSpec .hydrogen]) = _
  rw [blocksResult_atoms]
  simp [initialHydrogenState]

/-! ### Local list-lookup helper lemmas (restated generically) -/

theorem listGet?_append_left {α : Type*} (left right : List α) (index : ℕ)
    (bound : index < left.length) :
    listGet? (left ++ right) index = listGet? left index := by
  induction left generalizing index with
  | nil => simp at bound
  | cons head tail ih =>
      cases index with
      | zero => rfl
      | succ index =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at bound
          simpa [listGet?] using ih index bound

theorem listGet?_append_right_of_length_le {α : Type*} (left right : List α) (index : ℕ)
    (bound : left.length ≤ index) :
    listGet? (left ++ right) index = listGet? right (index - left.length) := by
  induction left generalizing index with
  | nil => simp
  | cons head tail ih =>
      cases index with
      | zero => simp at bound
      | succ index =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at bound
          simpa [listGet?, Nat.succ_sub_succ_eq_sub] using ih index bound

/-- One six-atom block prepended to any tail. -/
theorem listGet?_cons_block (parity : TetrahedralInputParity) (rest : List AtomSpec) (m : ℕ) :
    listGet? (blockAtoms parity ++ rest) (6 + m) = listGet? rest m := by
  have bound : (blockAtoms parity).length ≤ 6 + m := by simp [blockAtoms]
  rw [listGet?_append_right_of_length_le (blockAtoms parity) rest (6 + m) bound]
  congr 1
  simp only [blockAtoms, List.length_cons, List.length_nil]
  omega

/-- Offset lookup inside one six-atom block. -/
theorem listGet?_blockAtoms (parity : TetrahedralInputParity) (offset : ℕ)
    (bound : offset < 6) :
    listGet? (blockAtoms parity) offset = some (blockAtomSpec parity offset) := by
  interval_cases offset <;> rfl

/-! ### Forward actual lookup at every role -/

theorem listGet?_roleAtoms_add (parities : List TetrahedralInputParity) (i : ℕ)
    (hi : i < parities.length) (offset : ℕ) (bound : offset < 6) :
    listGet? (roleAtoms parities) (6 * i + offset) =
      some (blockAtomSpec (parities.get ⟨i, hi⟩) offset) := by
  induction parities generalizing i with
  | nil => simp at hi
  | cons parity rest ih =>
      cases i with
      | zero =>
          have hidx : 6 * 0 + offset = offset := by omega
          rw [hidx]
          simp only [roleAtoms]
          rw [listGet?_append_left (blockAtoms parity) (roleAtoms rest) offset
            (by simp only [blockAtoms, List.length_cons, List.length_nil]; omega)]
          rw [listGet?_blockAtoms parity offset bound]
          simp
      | succ i =>
          have hrest : i < rest.length := by simpa using hi
          have hstep : 6 * (i + 1) + offset = 6 + (6 * i + offset) := by omega
          rw [hstep]
          simp only [roleAtoms]
          rw [listGet?_cons_block parity (roleAtoms rest) (6 * i + offset)]
          rw [ih i hrest]
          simp

theorem familyRaw_atomAt?_left (parities : List TetrahedralInputParity) :
    (familyRaw parities).atomAt? 0 = some (atomSpec .hydrogen) := by
  change listGet? (familyRaw parities).atoms 0 = _
  rw [familyRaw_atoms]
  rfl

theorem familyRaw_atomAt?_right (parities : List TetrahedralInputParity) :
    (familyRaw parities).atomAt? (6 * parities.length + 1) = some (atomSpec .hydrogen) := by
  change listGet? (familyRaw parities).atoms (6 * parities.length + 1) = _
  rw [familyRaw_atoms, List.append_assoc]
  rw [listGet?_append_right_of_length_le [atomSpec .hydrogen]
    (roleAtoms parities ++ [atomSpec .hydrogen]) (6 * parities.length + 1)
    (by simp only [List.length_cons, List.length_nil]; omega)]
  have hfirst : 6 * parities.length + 1 - 1 = 6 * parities.length := by omega
  change listGet? (roleAtoms parities ++ [atomSpec .hydrogen])
    (6 * parities.length + 1 - 1) = _
  rw [hfirst]
  rw [listGet?_append_right_of_length_le (roleAtoms parities) [atomSpec .hydrogen]
    (6 * parities.length) (by rw [roleAtoms_length])]
  have hsecond : 6 * parities.length - (roleAtoms parities).length = 0 := by
    rw [roleAtoms_length]; omega
  rw [hsecond]
  rfl

theorem familyRaw_atomAt?_internal (parities : List TetrahedralInputParity)
    (i : Fin parities.length) (offset : ℕ) (bound : offset < 6) :
    (familyRaw parities).atomAt? (1 + (6 * (i : ℕ) + offset)) =
      some (blockAtomSpec (parities.get i) offset) := by
  have hm : 6 * (i : ℕ) + offset < (roleAtoms parities).length := by
    rw [roleAtoms_length]
    have := i.isLt
    omega
  change listGet? (familyRaw parities).atoms (1 + (6 * (i : ℕ) + offset)) = _
  rw [familyRaw_atoms, List.append_assoc]
  rw [listGet?_append_right_of_length_le [atomSpec .hydrogen]
    (roleAtoms parities ++ [atomSpec .hydrogen]) (1 + (6 * (i : ℕ) + offset))
    (by simp only [List.length_cons, List.length_nil]; omega)]
  have hfirst : 1 + (6 * (i : ℕ) + offset) - 1 = 6 * (i : ℕ) + offset := by omega
  change listGet? (roleAtoms parities ++ [atomSpec .hydrogen])
    (1 + (6 * (i : ℕ) + offset) - 1) = _
  rw [hfirst]
  rw [listGet?_append_left (roleAtoms parities) [atomSpec .hydrogen]
    (6 * (i : ℕ) + offset) hm]
  exact listGet?_roleAtoms_add parities (i : ℕ) i.isLt offset bound

/-- Forward actual lookup: every role index carries exactly its independently specified atom. -/
theorem familyRaw_atomAt?_role (parities : List TetrahedralInputParity)
    (role : TraversalRole parities) :
    (familyRaw parities).atomAt? (roleIndex role) = some (roleSpec role) := by
  cases role with
  | leftHydrogen => exact familyRaw_atomAt?_left parities
  | rightHydrogen => exact familyRaw_atomAt?_right parities
  | backbone i =>
      rw [show roleIndex (.backbone i : TraversalRole parities) = 1 + (6 * (i : ℕ) + 0)
        by simp only [roleIndex]; omega]
      rw [familyRaw_atomAt?_internal parities i 0 (by omega)]
      rfl
  | backboneHydrogen i =>
      rw [show roleIndex (.backboneHydrogen i : TraversalRole parities) =
          1 + (6 * (i : ℕ) + 1) by simp only [roleIndex]; omega]
      rw [familyRaw_atomAt?_internal parities i 1 (by omega)]
      rfl
  | taggedCarbon i =>
      rw [show roleIndex (.taggedCarbon i : TraversalRole parities) =
          1 + (6 * (i : ℕ) + 2) by simp only [roleIndex]; omega]
      rw [familyRaw_atomAt?_internal parities i 2 (by omega)]
      rfl
  | pendantHydrogen i =>
      rw [show roleIndex (.pendantHydrogen i : TraversalRole parities) =
          1 + (6 * (i : ℕ) + 3) by simp only [roleIndex]; omega]
      rw [familyRaw_atomAt?_internal parities i 3 (by omega)]
      rfl
  | pendantFluorine i =>
      rw [show roleIndex (.pendantFluorine i : TraversalRole parities) =
          1 + (6 * (i : ℕ) + 4) by simp only [roleIndex]; omega]
      rw [familyRaw_atomAt?_internal parities i 4 (by omega)]
      rfl
  | pendantBromine i =>
      rw [show roleIndex (.pendantBromine i : TraversalRole parities) =
          1 + (6 * (i : ℕ) + 5) by simp only [roleIndex]; omega]
      rw [familyRaw_atomAt?_internal parities i 5 (by omega)]
      rfl

theorem roleIndex_internalRole (parities : List TetrahedralInputParity)
    (i : Fin parities.length) (offset : ℕ) (bound : offset < 6) :
    roleIndex (internalRole parities i offset) = 1 + (6 * (i : ℕ) + offset) := by
  interval_cases offset <;> simp only [internalRole, roleIndex] <;> omega

theorem roleSpec_internalRole (parities : List TetrahedralInputParity)
    (i : Fin parities.length) (offset : ℕ) (bound : offset < 6) :
    roleSpec (internalRole parities i offset) = blockAtomSpec (parities.get i) offset := by
  interval_cases offset <;> simp [internalRole, roleSpec, blockAtomSpec]

/-! ### Independent role bounds -/

theorem roleIndex_lt_atomCount (parities : List TetrahedralInputParity)
    (role : TraversalRole parities) : roleIndex role < (familyRaw parities).atomCount := by
  rw [familyRaw_atom_count]
  cases role with
  | leftHydrogen => simp only [roleIndex]; omega
  | rightHydrogen => simp only [roleIndex]; omega
  | backbone i => have h := i.isLt; simp only [roleIndex]; omega
  | backboneHydrogen i => have h := i.isLt; simp only [roleIndex]; omega
  | taggedCarbon i => have h := i.isLt; simp only [roleIndex]; omega
  | pendantHydrogen i => have h := i.isLt; simp only [roleIndex]; omega
  | pendantFluorine i => have h := i.isLt; simp only [roleIndex]; omega
  | pendantBromine i => have h := i.isLt; simp only [roleIndex]; omega

theorem tagged_index_injective (parities : List TetrahedralInputParity)
    (i j : Fin parities.length)
    (equal : 3 + 6 * (i : ℕ) = 3 + 6 * (j : ℕ)) : i = j := by
  apply Fin.ext
  omega

/-! ### Independent inverse: every actual lookup is a role -/

/-- Any internal offset of the flat role atoms is a bounded block position. -/
theorem listGet?_roleAtoms_lt (parities : List TetrahedralInputParity) (m : ℕ)
    (bound : m < 6 * parities.length) :
    ∃ (i : Fin parities.length) (offset : ℕ), offset < 6 ∧ m = 6 * (i : ℕ) + offset ∧
      listGet? (roleAtoms parities) m = some (blockAtomSpec (parities.get i) offset) := by
  revert m
  induction parities with
  | nil =>
      intro m bound
      simp only [List.length_nil, Nat.mul_zero] at bound
      omega
  | cons parity rest ih =>
      intro m bound
      have hbound : m < 6 + 6 * rest.length := by
        simp only [List.length_cons] at bound
        omega
      by_cases hsmall : m < 6
      · refine ⟨⟨0, by simp⟩, m, hsmall, by simp, ?_⟩
        simp only [roleAtoms]
        rw [listGet?_append_left (blockAtoms parity) (roleAtoms rest) m
          (by simp only [blockAtoms, List.length_cons, List.length_nil]; omega)]
        rw [listGet?_blockAtoms parity m hsmall]
        simp
      · have hge : 6 ≤ m := by omega
        have hrest : m - 6 < 6 * rest.length := by omega
        obtain ⟨i, offset, hoff, hm, hget⟩ := ih (m - 6) hrest
        refine ⟨⟨i.val + 1,
          by have hi := i.isLt; simp only [List.length_cons]; omega⟩, offset, hoff, ?_, ?_⟩
        · change m = 6 * (i.val + 1) + offset
          omega
        · simp only [roleAtoms]
          rw [show m = 6 + (m - 6) by omega]
          rw [listGet?_cons_block parity (roleAtoms rest) (m - 6)]
          rw [hget]
          simp

/-- Every in-range written index of the family raw molecule is exactly one traversal role. -/
theorem familyRaw_atomAt?_eq_roleSpec_of_lt (parities : List TetrahedralInputParity)
    (index : ℕ) (bound : index < (familyRaw parities).atomCount) :
    ∃ role : TraversalRole parities, roleIndex role = index ∧
      (familyRaw parities).atomAt? index = some (roleSpec role) := by
  rw [familyRaw_atom_count] at bound
  by_cases hzero : index = 0
  · subst index
    exact ⟨.leftHydrogen, rfl, familyRaw_atomAt?_left parities⟩
  by_cases hlast : index = 6 * parities.length + 1
  · subst index
    exact ⟨.rightHydrogen, rfl, familyRaw_atomAt?_right parities⟩
  · have hm : index - 1 < 6 * parities.length := by omega
    have hsplit : index = 1 + (index - 1) := by omega
    obtain ⟨i, offset, hoff, hdec, _⟩ := listGet?_roleAtoms_lt parities (index - 1) hm
    refine ⟨internalRole parities i offset, ?_, ?_⟩
    · rw [roleIndex_internalRole parities i offset hoff]
      omega
    · rw [hsplit, hdec]
      rw [familyRaw_atomAt?_internal parities i offset hoff, roleSpec_internalRole parities i offset hoff]

/-- Independent inverse: any actual observed lookup yields a role with exactly its index/spec. -/
theorem familyRaw_atomAt?_role_of_lookup (parities : List TetrahedralInputParity) (index : ℕ)
    (spec : AtomSpec) (lookup : (familyRaw parities).atomAt? index = some spec) :
    ∃ role : TraversalRole parities, roleIndex role = index ∧ roleSpec role = spec := by
  have bound : index < (familyRaw parities).atomCount :=
    listGet?_eq_some_implies_lt (familyRaw parities).atoms index spec
      (by simpa [RawMolecule.atomAt?] using lookup)
  obtain ⟨role, hindex, hlookup⟩ := familyRaw_atomAt?_eq_roleSpec_of_lt parities index bound
  refine ⟨role, hindex, ?_⟩
  rw [hlookup] at lookup
  exact Option.some.inj lookup

/-! ### Actual tagged-annotation inverse and parity provenance -/

/-- Every actual tetrahedral annotation is exactly a unique tag role carrying `parities.get i`. -/
theorem familyRaw_tagged_inverse (parities : List TetrahedralInputParity) (index : ℕ)
    (spec : AtomSpec) (lookup : (familyRaw parities).atomAt? index = some spec)
    (parity : TetrahedralInputParity) (tag : spec.tetrahedral? = some parity) :
    ∃ i : Fin parities.length,
      index = 3 + 6 * (i : ℕ) ∧
      spec = atomSpec (.taggedCarbon (parities.get i)) ∧
      parity = parities.get i := by
  obtain ⟨role, hindex, hspec⟩ := familyRaw_atomAt?_role_of_lookup parities index spec lookup
  cases role with
  | taggedCarbon i =>
      refine ⟨i, ?_, ?_, ?_⟩
      · rw [← hindex]; rfl
      · rw [← hspec]; rfl
      · have annotated : spec.tetrahedral? = some (parities.get i) := by rw [← hspec]; rfl
        exact Option.some.inj (tag.symm.trans annotated)
  | leftHydrogen =>
      rw [← hspec] at tag
      simp [roleSpec, atomSpec] at tag
  | rightHydrogen =>
      rw [← hspec] at tag
      simp [roleSpec, atomSpec] at tag
  | backbone i =>
      rw [← hspec] at tag
      simp [roleSpec, atomSpec] at tag
  | backboneHydrogen i =>
      rw [← hspec] at tag
      simp [roleSpec, atomSpec] at tag
  | pendantHydrogen i =>
      rw [← hspec] at tag
      simp [roleSpec, atomSpec] at tag
  | pendantFluorine i =>
      rw [← hspec] at tag
      simp [roleSpec, atomSpec] at tag
  | pendantBromine i =>
      rw [← hspec] at tag
      simp [roleSpec, atomSpec] at tag

/-- Every non-tag role indeed carries no tetrahedral annotation (converse direction). -/
theorem familyRaw_atomAt?_role_parity (parities : List TetrahedralInputParity)
    (role : TraversalRole parities) :
    ((familyRaw parities).atomAt? (roleIndex role)).bind AtomSpec.tetrahedral? = roleParity? role := by
  rw [familyRaw_atomAt?_role parities role]
  exact roleSpec_parity role

/-- Nat behavioural equality is `false` for distinct indices.  Avoids depending on a
Mathlib-specific `BEq` lemma name. -/
theorem nat_beq_eq_false {a b : ℕ} (h : a ≠ b) : (a == b) = false := by
  cases hb : a == b
  · rfl
  · exact absurd (beq_iff_eq.mp hb) h

/-- Nat behavioural equality is reflexive, derived from `beq_iff_eq` directly. -/
theorem nat_beq_self (a : ℕ) : (a == a) = true := beq_iff_eq.mpr rfl

/-- A record projection is `none` exactly when both endpoints avoid the center. -/
theorem recordNeighbor?_eq_none_of_ne {center : ℕ} {bond : RawBond}
    (source_ne : bond.source ≠ center) (target_ne : bond.target ≠ center) :
    recordNeighbor? center bond = none := by
  simp [recordNeighbor?, nat_beq_eq_false source_ne, nat_beq_eq_false target_ne]



theorem filterMap_recordNeighbor?_eq_nil {center : ℕ} {bonds : List RawBond}
    (avoid : ∀ bond ∈ bonds, bond.source ≠ center ∧ bond.target ≠ center) :
    bonds.filterMap (recordNeighbor? center) = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro bond member
  exact recordNeighbor?_eq_none_of_ne (avoid bond member).1 (avoid bond member).2

/-! ## The actual six-edge block record -/

/-- The six actual single bonds appended by one chronological backbone block, stated with typed
horizontal `RawBond` literals at the real raw indices. -/
def blockBonds (parent m : ℕ) : List RawBond :=
  [ { source := parent, target := m, kind := ParsedBondKind.single },
    { source := m, target := m + 1, kind := ParsedBondKind.single },
    { source := m, target := m + 2, kind := ParsedBondKind.single },
    { source := m + 2, target := m + 3, kind := ParsedBondKind.single },
    { source := m + 2, target := m + 4, kind := ParsedBondKind.single },
    { source := m + 2, target := m + 5, kind := ParsedBondKind.single } ]

/-- Obligation `actual_six_edge_append`: the raw bond record of `blockResult` is exactly the old
record followed by the six actual single bonds based at `state.atoms.length`.  No surrogate
generator or parser hop occurs. -/
theorem blockResult_bonds_eq (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) :
    (blockResult state parent parity).bonds =
      state.bonds ++ blockBonds parent state.atoms.length := by
  simp only [blockResult, pendantBranchResult, singleBranchResult, attachSingle, blockBonds,
    List.length_append, List.length_cons, List.length_nil, List.cons_append, List.nil_append,
    List.append_assoc]

/-! ## Local new-record computation over one block -/

/-- The actual tag record of one block, read at the real index `m + 2`. -/
theorem blockBonds_tag_records (parent m : ℕ) (parent_lt : parent < m) :
    (blockBonds parent m).filterMap (recordNeighbor? (m + 2)) = [m, m + 3, m + 4, m + 5] := by
  have parentNe : parent ≠ m + 2 := by omega
  simp (disch := omega) [blockBonds, List.filterMap_cons, recordNeighbor?]
  simp_all


/-- The actual first pendant terminal (H) record of one block, read at the real index `m + 3`. -/
theorem blockBonds_h_records (parent m : ℕ) (parent_lt : parent < m) :
    (blockBonds parent m).filterMap (recordNeighbor? (m + 3)) = [m + 2] := by
  have parentNe : parent ≠ m + 3 := by omega
  simp (disch := omega) [blockBonds, List.filterMap_cons, recordNeighbor?]
  simp_all


/-- The actual second pendant terminal (F) record of one block, read at the real index `m + 4`. -/
theorem blockBonds_f_records (parent m : ℕ) (parent_lt : parent < m) :
    (blockBonds parent m).filterMap (recordNeighbor? (m + 4)) = [m + 2] := by
  have parentNe : parent ≠ m + 4 := by omega
  simp (disch := omega) [blockBonds, List.filterMap_cons, recordNeighbor?]
  simp_all


/-- The actual third pendant terminal (Br) record of one block, read at the real index `m + 5`. -/
theorem blockBonds_br_records (parent m : ℕ) (parent_lt : parent < m) :
    (blockBonds parent m).filterMap (recordNeighbor? (m + 5)) = [m + 2] := by
  have parentNe : parent ≠ m + 5 := by omega
  simp (disch := omega) [blockBonds, List.filterMap_cons, recordNeighbor?]
  simp_all


/-! ## Exclusion invariant: blocks never touch an older center -/

/-- Every bond of one block avoids any center strictly below its base; the only exception is the
block parent, which must be distinct from the center.  This single exclusion invariant replaces
28 pairwise disjointness cases. -/
theorem blockBonds_fresh {parent m center : ℕ} (center_lt : center < m)
    (parent_ne : parent ≠ center) :
    ∀ bond ∈ blockBonds parent m, bond.source ≠ center ∧ bond.target ≠ center := by
  intro bond member
  simp only [blockBonds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h
  · subst h; change parent ≠ center ∧ m ≠ center; exact ⟨parent_ne, by omega⟩
  · subst h; change m ≠ center ∧ m + 1 ≠ center; exact ⟨by omega, by omega⟩
  · subst h; change m ≠ center ∧ m + 2 ≠ center; exact ⟨by omega, by omega⟩
  · subst h; change m + 2 ≠ center ∧ m + 3 ≠ center; exact ⟨by omega, by omega⟩
  · subst h; change m + 2 ≠ center ∧ m + 4 ≠ center; exact ⟨by omega, by omega⟩
  · subst h; change m + 2 ≠ center ∧ m + 5 ≠ center; exact ⟨by omega, by omega⟩

/-! ## Chronological suffix records -/

/-- The raw bond record of an arbitrary `blocksResult` suffix, with the exact running base index. -/
def blocksBonds : List TetrahedralInputParity → ℕ → ℕ → List RawBond
  | [], _, _ => []
  | _ :: rest, parent, m => blockBonds parent m ++ blocksBonds rest m (m + 6)

theorem blocksResult_bonds_eq (parities : List TetrahedralInputParity) (state : ParseState)
    (parent : ℕ) :
    (blocksResult parities state parent).bonds =
      state.bonds ++ blocksBonds parities parent state.atoms.length := by
  induction parities generalizing state parent with
  | nil => exact (List.append_nil state.bonds).symm
  | cons parity rest inductionHypothesis =>
      show (blocksResult rest (blockResult state parent parity) state.atoms.length).bonds =
        state.bonds ++ blocksBonds (parity :: rest) parent state.atoms.length
      rw [inductionHypothesis, blockResult_bonds_eq, blockResult_atom_count]
      simp only [blocksBonds, List.append_assoc]

/-- Suffix exhaustion of the exclusion invariant: a suffix whose base lies above a center, and
whose entering parent differs from it, never touches that center. -/
theorem blocksBonds_fresh (parities : List TetrahedralInputParity) {parent m center : ℕ}
    (center_lt : center < m) (parent_ne : parent ≠ center) :
    ∀ bond ∈ blocksBonds parities parent m, bond.source ≠ center ∧ bond.target ≠ center := by
  induction parities generalizing parent m with
  | nil => intro bond member; cases member
  | cons parity rest inductionHypothesis =>
      intro bond member
      rw [show blocksBonds (parity :: rest) parent m =
        blockBonds parent m ++ blocksBonds rest m (m + 6) from rfl, List.mem_append] at member
      rcases member with initial | later
      · exact blockBonds_fresh center_lt parent_ne bond initial
      · exact inductionHypothesis (parent := m) (m := m + 6) (by omega) (by omega) bond later

/-- Obligation `arbitrary_suffix_preserved`: any old center strictly inside the initial state and
distinct from the entering parent keeps its actual `recordNeighbors` projection through an
arbitrary chronological suffix of blocks.  No row-table exactness, canonical transport,
no-extra-incident-edge or callback hypothesis is used. -/
theorem blocksResult_recordNeighbors_preserved (parities : List TetrahedralInputParity)
    (state : ParseState) (parent center : ℕ)
    (center_lt : center < state.atoms.length) (parent_ne : parent ≠ center) :
    recordNeighbors (blocksResult parities state parent).molecule center =
      recordNeighbors state.molecule center := by
  have fresh := blocksBonds_fresh parities (m := state.atoms.length) center_lt parent_ne
  simp only [recordNeighbors, ParseState.molecule]
  rw [blocksResult_bonds_eq, List.filterMap_append,
    filterMap_recordNeighbor?_eq_nil fresh, List.append_nil]

/-! ## Final hydrogen append -/

/-- The actual `attachSingle` final-hydrogen append preserves any center distinct from the append
parent and from the fresh index.  This discharges the final-H case of obligation
`arbitrary_suffix_preserved`. -/
theorem attachSingle_recordNeighbors_preserved (state : ParseState) (parent center : ℕ)
    (atom : AtomSpec) (parent_ne : parent ≠ center)
    (fresh_ne : state.atoms.length ≠ center) :
    recordNeighbors (attachSingle state parent atom).molecule center =
      recordNeighbors state.molecule center := by
  have single : ([{ source := parent, target := state.atoms.length, kind := ParsedBondKind.single }] : List RawBond).filterMap (recordNeighbor? center) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro bond member
    simp only [List.mem_singleton] at member
    subst member
    exact recordNeighbor?_eq_none_of_ne parent_ne fresh_ne
  simp only [recordNeighbors, ParseState.molecule]
  rw [attachSingle_bonds, List.filterMap_append, single, List.append_nil]

/-! ## First-block instance of the family statement for an arbitrary suffix -/

/-- Obligation `new_tag_and_terminal_records`, first block: for an arbitrary prefix state and an
arbitrary nonempty suffix, the actual tag record at the real index `state.atoms.length + 2` is the
four recovered endpoints.  The later blocks are excluded by the suffix exclusion invariant. -/
theorem blocksResult_tag_recordNeighbors_cons (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) (rest : List TetrahedralInputParity)
    (physical : Chronological state) (parentBound : parent < state.atoms.length) :
    recordNeighbors (blocksResult (parity :: rest) state parent).molecule
        (state.atoms.length + 2) =
      [state.atoms.length, state.atoms.length + 3, state.atoms.length + 4,
        state.atoms.length + 5] := by
  have oldAvoid : ∀ bond ∈ state.bonds,
      bond.source ≠ state.atoms.length + 2 ∧ bond.target ≠ state.atoms.length + 2 := by
    intro bond member
    have forward := physical.forward bond member
    have bounded := physical.bounded bond member
    exact ⟨by omega, by omega⟩
  have restAvoid : ∀ bond ∈ blocksBonds rest state.atoms.length (state.atoms.length + 6),
      bond.source ≠ state.atoms.length + 2 ∧ bond.target ≠ state.atoms.length + 2 :=
    blocksBonds_fresh rest (parent := state.atoms.length) (m := state.atoms.length + 6)
      (by omega) (by omega)
  simp only [recordNeighbors, ParseState.molecule]
  rw [blocksResult_bonds_eq]
  rw [show blocksBonds (parity :: rest) parent state.atoms.length =
    blockBonds parent state.atoms.length ++
      blocksBonds rest state.atoms.length (state.atoms.length + 6) from rfl]
  simp only [List.filterMap_append, filterMap_recordNeighbor?_eq_nil oldAvoid,
    filterMap_recordNeighbor?_eq_nil restAvoid, List.nil_append, List.append_nil]
  exact blockBonds_tag_records parent state.atoms.length parentBound

/-- First-block pendant terminal records (H, F, Br) for an arbitrary prefix state and suffix. -/
theorem blocksResult_terminal_recordNeighbors_cons (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) (rest : List TetrahedralInputParity)
    (physical : Chronological state) (parentBound : parent < state.atoms.length) :
    recordNeighbors (blocksResult (parity :: rest) state parent).molecule
        (state.atoms.length + 3) = [state.atoms.length + 2] ∧
      recordNeighbors (blocksResult (parity :: rest) state parent).molecule
        (state.atoms.length + 4) = [state.atoms.length + 2] ∧
      recordNeighbors (blocksResult (parity :: rest) state parent).molecule
        (state.atoms.length + 5) = [state.atoms.length + 2] := by
  have restAvoid : ∀ bond ∈ blocksBonds rest state.atoms.length (state.atoms.length + 6),
      bond.source ≠ state.atoms.length + 3 ∧ bond.target ≠ state.atoms.length + 3 :=
    blocksBonds_fresh rest (parent := state.atoms.length) (m := state.atoms.length + 6)
      (by omega) (by omega)
  have restAvoid4 : ∀ bond ∈ blocksBonds rest state.atoms.length (state.atoms.length + 6),
      bond.source ≠ state.atoms.length + 4 ∧ bond.target ≠ state.atoms.length + 4 :=
    blocksBonds_fresh rest (parent := state.atoms.length) (m := state.atoms.length + 6)
      (by omega) (by omega)
  have restAvoid5 : ∀ bond ∈ blocksBonds rest state.atoms.length (state.atoms.length + 6),
      bond.source ≠ state.atoms.length + 5 ∧ bond.target ≠ state.atoms.length + 5 :=
    blocksBonds_fresh rest (parent := state.atoms.length) (m := state.atoms.length + 6)
      (by omega) (by omega)
  have oldAvoid3 : ∀ bond ∈ state.bonds,
      bond.source ≠ state.atoms.length + 3 ∧ bond.target ≠ state.atoms.length + 3 := by
    intro bond member
    have forward := physical.forward bond member
    have bounded := physical.bounded bond member
    exact ⟨by omega, by omega⟩
  have oldAvoid4 : ∀ bond ∈ state.bonds,
      bond.source ≠ state.atoms.length + 4 ∧ bond.target ≠ state.atoms.length + 4 := by
    intro bond member
    have forward := physical.forward bond member
    have bounded := physical.bounded bond member
    exact ⟨by omega, by omega⟩
  have oldAvoid5 : ∀ bond ∈ state.bonds,
      bond.source ≠ state.atoms.length + 5 ∧ bond.target ≠ state.atoms.length + 5 := by
    intro bond member
    have forward := physical.forward bond member
    have bounded := physical.bounded bond member
    exact ⟨by omega, by omega⟩
  have projection : ∀ center, (∀ bond ∈ state.bonds,
        bond.source ≠ center ∧ bond.target ≠ center) →
      (∀ bond ∈ blocksBonds rest state.atoms.length (state.atoms.length + 6),
        bond.source ≠ center ∧ bond.target ≠ center) →
      recordNeighbors (blocksResult (parity :: rest) state parent).molecule center =
        (blockBonds parent state.atoms.length).filterMap (recordNeighbor? center) := by
    intro center oldAvoid restAvoid'
    simp only [recordNeighbors, ParseState.molecule]
    rw [blocksResult_bonds_eq]
    rw [show blocksBonds (parity :: rest) parent state.atoms.length =
      blockBonds parent state.atoms.length ++
        blocksBonds rest state.atoms.length (state.atoms.length + 6) from rfl]
    simp only [List.filterMap_append, filterMap_recordNeighbor?_eq_nil oldAvoid,
      filterMap_recordNeighbor?_eq_nil restAvoid', List.nil_append, List.append_nil]
  refine ⟨?_, ?_, ?_⟩
  · rw [projection (state.atoms.length + 3) oldAvoid3 restAvoid]
    exact blockBonds_h_records parent state.atoms.length parentBound
  · rw [projection (state.atoms.length + 4) oldAvoid4 restAvoid4]
    exact blockBonds_f_records parent state.atoms.length parentBound
  · rw [projection (state.atoms.length + 5) oldAvoid5 restAvoid5]
    exact blockBonds_br_records parent state.atoms.length parentBound

/-! ## Family first-block instance -/

/-- The actual last/current backbone index of a family-shaped construction is either `0` or a
running base `1 + 6 * k`.  This is the shape invariant that excludes the tag and terminal indices. -/
theorem blocksParent_shape (parities : List TetrahedralInputParity) (state : ParseState)
    (parent : ℕ) (hparent : parent = 0 ∨ ∃ b, parent = 1 + 6 * b)
    (hstate : ∃ a, state.atoms.length = 1 + 6 * a) :
    blocksParent parities state parent = 0 ∨
      ∃ k, blocksParent parities state parent = 1 + 6 * k := by
  induction parities generalizing state parent with
  | nil => exact hparent
  | cons parity rest inductionHypothesis =>
      apply inductionHypothesis
      · exact hstate.elim fun a ha => Or.inr ⟨a, ha⟩
      · obtain ⟨a, ha⟩ := hstate
        exact ⟨a + 1, by rw [blockResult_atom_count, ha]; omega⟩



/-! ### All ordinal records, from prefix induction rather than supplied rows -/

theorem initial_chronological : Chronological initialHydrogenState := by
  constructor
  · intro bond member; cases member
  · intro bond member; cases member
  · exact List.nodup_nil

theorem blocksResult_pendant_records (ps : List TetrahedralInputParity)
    (state : ParseState) (parent : ℕ) (physical : Chronological state)
    (parentBound : parent < state.atoms.length) (i : ℕ) (bound : i < ps.length) :
    recordNeighbors (blocksResult ps state parent).molecule (state.atoms.length + 6 * i + 2) =
      [state.atoms.length + 6 * i, state.atoms.length + 6 * i + 3,
        state.atoms.length + 6 * i + 4, state.atoms.length + 6 * i + 5] ∧
    recordNeighbors (blocksResult ps state parent).molecule (state.atoms.length + 6 * i + 3) =
      [state.atoms.length + 6 * i + 2] ∧
    recordNeighbors (blocksResult ps state parent).molecule (state.atoms.length + 6 * i + 4) =
      [state.atoms.length + 6 * i + 2] ∧
    recordNeighbors (blocksResult ps state parent).molecule (state.atoms.length + 6 * i + 5) =
      [state.atoms.length + 6 * i + 2] := by
  induction ps generalizing state parent i with
  | nil => simp at bound
  | cons parity rest ih =>
      cases i with
      | zero =>
          simp only [Nat.mul_zero, Nat.add_zero]
          exact ⟨blocksResult_tag_recordNeighbors_cons state parent parity rest physical parentBound,
            blocksResult_terminal_recordNeighbors_cons state parent parity rest physical parentBound⟩
      | succ i =>
          have next := blockResult_chronological state parent parity physical parentBound
          have nextBound : state.atoms.length < (blockResult state parent parity).atoms.length := by
            rw [blockResult_atom_count]; omega
          have ordinal : i < rest.length := by simpa using bound
          have result := ih (blockResult state parent parity) state.atoms.length next nextBound i ordinal
          have shift : (blockResult state parent parity).atoms.length + 6 * i =
              state.atoms.length + 6 * (i + 1) := by rw [blockResult_atom_count]; omega
          rw [shift] at result
          exact result

theorem family_final_preserves (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : ℕ) (range : 2 ≤ offset ∧ offset ≤ 5) :
    recordNeighbors (familyRaw ps) (1 + 6 * i.val + offset) =
      recordNeighbors (blocksResult ps initialHydrogenState 0).molecule
        (1 + 6 * i.val + offset) := by
  have fresh : (blocksResult ps initialHydrogenState 0).atoms.length ≠
      1 + 6 * i.val + offset := by
    rw [blocksResult_atom_count]
    have hi := i.isLt
    change 1 + 6 * ps.length ≠ _
    omega
  have parent : blocksParent ps initialHydrogenState 0 ≠ 1 + 6 * i.val + offset := by
    rcases blocksParent_shape ps initialHydrogenState 0 (Or.inl rfl) ⟨0, rfl⟩ with h | ⟨k, h⟩
    · omega
    · omega
  rw [← familyState_molecule]
  exact attachSingle_recordNeighbors_preserved _ _ _ _ parent fresh

theorem familyRaw_pendant_records (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    recordNeighbors (familyRaw ps) (3 + 6 * i.val) =
      [1 + 6 * i.val, 4 + 6 * i.val, 5 + 6 * i.val, 6 + 6 * i.val] ∧
    recordNeighbors (familyRaw ps) (4 + 6 * i.val) = [3 + 6 * i.val] ∧
    recordNeighbors (familyRaw ps) (5 + 6 * i.val) = [3 + 6 * i.val] ∧
    recordNeighbors (familyRaw ps) (6 + 6 * i.val) = [3 + 6 * i.val] := by
  have result := blocksResult_pendant_records ps initialHydrogenState 0 initial_chronological
    (by decide) i.val i.isLt
  have move (offset : ℕ) (range : 2 ≤ offset ∧ offset ≤ 5) := family_final_preserves ps i offset range
  have r2 := move 2 (by omega)
  have r3 := move 3 (by omega)
  have r4 := move 4 (by omega)
  have r5 := move 5 (by omega)
  have initialSize : initialHydrogenState.atoms.length = 1 := rfl
  rw [initialSize] at result
  have e2 : 1 + 6 * i.val + 2 = 3 + 6 * i.val := by omega
  have e3 : 1 + 6 * i.val + 3 = 4 + 6 * i.val := by omega
  have e4 : 1 + 6 * i.val + 4 = 5 + 6 * i.val := by omega
  have e5 : 1 + 6 * i.val + 5 = 6 + 6 * i.val := by omega
  rw [e2, e3, e4, e5] at result
  rw [e2] at r2
  rw [e3] at r3
  rw [e4] at r4
  rw [e5] at r5
  rw [r2, r3, r4, r5]
  exact result

/-! ### Actual single-record graph orders -/

private theorem single_fold_le_one (bonds : List RawBond) (u v : ℕ) :
    ∀ acc, acc ≤ 1 → (∀ bond ∈ bonds, bond.kind = .single) →
    bonds.foldl (fun order bond =>
      if bond.directedConnects u v then max order bond.kind.order else order) acc ≤ 1 := by
  induction bonds with
  | nil => intro acc bound single; exact bound
  | cons bond bonds ih =>
      intro acc bound single
      simp only [List.foldl_cons]
      apply ih
      · have kind := single bond List.mem_cons_self
        rw [kind]
        split <;> simp_all [ParsedBondKind.order]
      · intro selected member
        exact single selected (List.mem_cons_of_mem bond member)

-- all_single_bond_order_le_one is re-exported from NativeSingleBondRawSupport.


-- all_single_incident_order is re-exported from NativeSingleBondRawSupport.


theorem familyRaw_pendant_site (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    Nonempty (TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery.PendantSite
      (familyRaw ps) (3 + 6 * i.val)) := by
  obtain ⟨tagRow, hRow, fRow, brRow⟩ := familyRaw_pendant_records ps i
  have z (role : TraversalRole ps) :
      (familyRaw ps).atomZAt (roleIndex role) = (roleSpec role).element.atomicNumber := by
    unfold RawMolecule.atomZAt
    rw [familyRaw_atomAt?_role]
  have single : ∀ other ∈ recordNeighbors (familyRaw ps) (3 + 6 * i.val),
      (familyRaw ps).bondOrder (3 + 6 * i.val) other = 1 := by
    intro other member
    exact all_single_incident_order _ (familyRaw_admissible ps).1
      (familyRaw_all_single ps) _ other member
  exact ⟨{ backbone := 1 + 6 * i.val, hydrogen := 4 + 6 * i.val, fluorine := 5 + 6 * i.val, bromine := 6 + 6 * i.val, bound := roleIndex_lt_atomCount ps (.taggedCarbon i), carbon := z (.taggedCarbon i), neighbors := by rw [tagRow], single := single, backboneCarbon := z (.backbone i), hydrogenZ := z (.pendantHydrogen i), fluorineZ := z (.pendantFluorine i), bromineZ := z (.pendantBromine i), hydrogenRow := hRow, fluorineRow := fRow, bromineRow := brRow }⟩

/-- Every actually observed tag has its physical four-neighbor site. No site is an input. -/
theorem familyRaw_all_tag_pendant_sites (ps : List TetrahedralInputParity) :
    ∀ index spec parity, (familyRaw ps).atomAt? index = some spec →
      spec.tetrahedral? = some parity →
      Nonempty (TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery.PendantSite
        (familyRaw ps) index) ∧ spec.element = .C := by
  intro index spec parity lookup tag
  obtain ⟨i, indexEq, specEq, _⟩ := familyRaw_tagged_inverse ps index spec lookup parity tag
  subst index
  subst spec
  exact ⟨familyRaw_pendant_site ps i, rfl⟩

/-! ### Backbone records and terminal records -/

theorem blockBonds_parent_records (parent m : ℕ) (parent_lt : parent < m) :
    (blockBonds parent m).filterMap (recordNeighbor? parent) = [m] := by
  have endpoint0 : m ≠ parent := by omega
  have endpoint1 : m + 1 ≠ parent := by omega
  have endpoint2 : m + 2 ≠ parent := by omega
  have endpoint3 : m + 3 ≠ parent := by omega
  have endpoint4 : m + 4 ≠ parent := by omega
  have endpoint5 : m + 5 ≠ parent := by omega
  simp (disch := omega) [blockBonds, List.filterMap_cons, recordNeighbor?]
  simp_all

theorem blockBonds_backbone_records (parent m : ℕ) (parent_lt : parent < m) :
    (blockBonds parent m).filterMap (recordNeighbor? m) = [parent, m + 1, m + 2] := by
  have parentNe : parent ≠ m := by omega
  simp (disch := omega) [blockBonds, List.filterMap_cons, recordNeighbor?]
  simp_all

theorem blockBonds_backbone_h_records (parent m : ℕ) (parent_lt : parent < m) :
    (blockBonds parent m).filterMap (recordNeighbor? (m + 1)) = [m] := by
  have parentNe : parent ≠ m + 1 := by omega
  simp (disch := omega) [blockBonds, List.filterMap_cons, recordNeighbor?]
  simp_all

theorem blockResult_parent_records (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) (bound : parent < state.atoms.length) :
    recordNeighbors (blockResult state parent parity).molecule parent =
      recordNeighbors state.molecule parent ++ [state.atoms.length] := by
  simp only [recordNeighbors, ParseState.molecule]
  rw [blockResult_bonds_eq, List.filterMap_append, blockBonds_parent_records parent _ bound]

theorem blockResult_new_records (state : ParseState) (parent center : ℕ)
    (parity : TetrahedralInputParity) (physical : Chronological state)
    (fresh : state.atoms.length ≤ center) :
    recordNeighbors (blockResult state parent parity).molecule center =
      (blockBonds parent state.atoms.length).filterMap (recordNeighbor? center) := by
  have avoid : ∀ bond ∈ state.bonds, bond.source ≠ center ∧ bond.target ≠ center := by
    intro bond retained
    have forward := physical.forward bond retained
    have bounded := physical.bounded bond retained
    exact ⟨by omega, by omega⟩
  simp only [recordNeighbors, ParseState.molecule]
  rw [blockResult_bonds_eq, List.filterMap_append,
    filterMap_recordNeighbor?_eq_nil avoid, List.nil_append]

theorem blocksResult_parent_records (ps : List TetrahedralInputParity)
    (state : ParseState) (parent : ℕ) (bound : parent < state.atoms.length) :
    recordNeighbors (blocksResult ps state parent).molecule parent =
      recordNeighbors state.molecule parent ++ (if ps = [] then [] else [state.atoms.length]) := by
  cases ps with
  | nil => simp only [blocksResult, if_true, List.append_nil]
  | cons parity rest =>
      change recordNeighbors (blocksResult rest (blockResult state parent parity)
        state.atoms.length).molecule parent = _
      rw [blocksResult_recordNeighbors_preserved rest (blockResult state parent parity)
        state.atoms.length parent (by rw [blockResult_atom_count]; omega) (by omega)]
      rw [blockResult_parent_records state parent parity bound]
      simp

def entryParent (m parent : ℕ) : ℕ → ℕ
  | 0 => parent
  | i + 1 => m + 6 * i

theorem entryParent_shift (m parent i : ℕ) :
    entryParent (m + 6) m i = entryParent m parent (i + 1) := by
  cases i with
  | zero => rfl
  | succ i => simp only [entryParent]; omega

theorem blocksResult_backbone_records (ps : List TetrahedralInputParity)
    (state : ParseState) (parent : ℕ) (physical : Chronological state)
    (parentBound : parent < state.atoms.length) (i : ℕ) (bound : i < ps.length) :
    recordNeighbors (blocksResult ps state parent).molecule (state.atoms.length + 6 * i) =
      [entryParent state.atoms.length parent i, state.atoms.length + 6 * i + 1,
        state.atoms.length + 6 * i + 2] ++
      (if i + 1 < ps.length then [state.atoms.length + 6 * i + 6] else []) := by
  induction ps generalizing state parent i with
  | nil => simp at bound
  | cons parity rest ih =>
      cases i with
      | zero =>
          simp only [Nat.mul_zero, Nat.add_zero, blocksResult, entryParent]
          rw [blocksResult_parent_records rest (blockResult state parent parity) state.atoms.length
            (by rw [blockResult_atom_count]; omega)]
          rw [blockResult_new_records state parent state.atoms.length parity physical (by omega),
            blockBonds_backbone_records parent _ parentBound, blockResult_atom_count]
          cases rest with
          | nil => simp
          | cons head tail => simp
      | succ i =>
          have next := blockResult_chronological state parent parity physical parentBound
          have nextBound : state.atoms.length < (blockResult state parent parity).atoms.length := by
            rw [blockResult_atom_count]; omega
          have ordinal : i < rest.length := by simpa using bound
          have result := ih (blockResult state parent parity) state.atoms.length next nextBound i ordinal
          have shift : (blockResult state parent parity).atoms.length + 6 * i =
              state.atoms.length + 6 * (i + 1) := by rw [blockResult_atom_count]; omega
          have parentShift : entryParent (blockResult state parent parity).atoms.length
              state.atoms.length i = entryParent state.atoms.length parent (i + 1) := by
            rw [blockResult_atom_count]
            exact entryParent_shift _ _ _
          rw [shift, parentShift] at result
          have condition : (i + 1 < rest.length) = (i + 1 + 1 < (parity :: rest).length) := by
            apply propext
            simp only [List.length_cons]
            omega
          simpa only [condition] using result

theorem blocksResult_backbone_h_records (ps : List TetrahedralInputParity)
    (state : ParseState) (parent : ℕ) (physical : Chronological state)
    (parentBound : parent < state.atoms.length) (i : ℕ) (bound : i < ps.length) :
    recordNeighbors (blocksResult ps state parent).molecule (state.atoms.length + 6 * i + 1) =
      [state.atoms.length + 6 * i] := by
  induction ps generalizing state parent i with
  | nil => simp at bound
  | cons parity rest ih =>
      cases i with
      | zero =>
          simp only [Nat.mul_zero, Nat.add_zero, blocksResult]
          rw [blocksResult_recordNeighbors_preserved rest (blockResult state parent parity)
            state.atoms.length (state.atoms.length + 1)
            (by rw [blockResult_atom_count]; omega) (by omega)]
          rw [blockResult_new_records state parent (state.atoms.length + 1) parity physical (by omega)]
          exact blockBonds_backbone_h_records _ _ parentBound
      | succ i =>
          have next := blockResult_chronological state parent parity physical parentBound
          have nextBound : state.atoms.length < (blockResult state parent parity).atoms.length := by
            rw [blockResult_atom_count]; omega
          have ordinal : i < rest.length := by simpa using bound
          have result := ih (blockResult state parent parity) state.atoms.length next nextBound i ordinal
          have shift : (blockResult state parent parity).atoms.length + 6 * i =
              state.atoms.length + 6 * (i + 1) := by rw [blockResult_atom_count]; omega
          rw [shift] at result
          exact result

/-- A final fresh append changes exactly the parent among the old centers. -/
theorem attachSingle_old_records (state : ParseState) (parent center : ℕ) (atom : AtomSpec)
    (bound : center < state.atoms.length) :
    recordNeighbors (attachSingle state parent atom).molecule center =
      recordNeighbors state.molecule center ++
      (if center = parent then [state.atoms.length] else []) := by
  simp only [recordNeighbors, ParseState.molecule]
  rw [attachSingle_bonds, List.filterMap_append]
  congr 1
  by_cases equal : center = parent
  · subst center
    simp (disch := omega) [List.filterMap_cons, recordNeighbor?]
  · have reverse : parent ≠ center := Ne.symm equal
    have fresh : state.atoms.length ≠ center := by omega
    simp only [List.filterMap_cons, List.filterMap_nil, recordNeighbor?]
    simp_all

theorem attachSingle_fresh_records (state : ParseState) (parent : ℕ) (atom : AtomSpec)
    (physical : Chronological state) (parentBound : parent < state.atoms.length) :
    recordNeighbors (attachSingle state parent atom).molecule state.atoms.length = [parent] := by
  have avoid : ∀ bond ∈ state.bonds,
      bond.source ≠ state.atoms.length ∧ bond.target ≠ state.atoms.length := by
    intro bond retained
    have forward := physical.forward bond retained
    have bounded := physical.bounded bond retained
    exact ⟨by omega, by omega⟩
  simp only [recordNeighbors, ParseState.molecule]
  rw [attachSingle_bonds, List.filterMap_append, filterMap_recordNeighbor?_eq_nil avoid]
  have parentNe : parent ≠ state.atoms.length := by omega
  simp (disch := omega) [List.filterMap_cons, recordNeighbor?]
  simp_all

theorem family_last_parent (ps : List TetrahedralInputParity) :
    blocksParent ps initialHydrogenState 0 = if ps = [] then 0 else 6 * ps.length - 5 := by
  rw [TetraStereo.UniversalProof.ChronologicalFamilyRuntimeSourceBridge.blocksParent_closed]
  cases ps with
  | nil => rfl
  | cons parity rest =>
      simp only [List.cons_ne_nil, if_false, initialHydrogenState, List.length_cons, List.length_nil]
      omega

theorem familyRaw_backbone_degree (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (recordNeighbors (familyRaw ps) (1 + 6 * i.val)).length = 4 := by
  have records := blocksResult_backbone_records ps initialHydrogenState 0 initial_chronological
    (by decide) i.val i.isLt
  have bound : 1 + 6 * i.val < (blocksResult ps initialHydrogenState 0).atoms.length := by
    rw [blocksResult_atom_count]
    have hi := i.isLt
    change _ < 1 + 6 * ps.length
    omega
  have hi := i.isLt
  have nonempty : ps ≠ [] := by intro empty; simp [empty] at hi
  have last := family_last_parent ps
  have initialSize : initialHydrogenState.atoms.length = 1 := rfl
  rw [initialSize] at records
  rw [← familyState_molecule]
  change (recordNeighbors (attachSingle (blocksResult ps initialHydrogenState 0)
    (blocksParent ps initialHydrogenState 0) (atomSpec .hydrogen)).molecule (1 + 6 * i.val)).length = 4
  rw [attachSingle_old_records _ _ _ _ bound, records, List.length_append]
  rw [last, if_neg nonempty]
  by_cases more : i.val + 1 < ps.length
  · have different : 1 + 6 * i.val ≠ 6 * ps.length - 5 := by omega
    simp only [if_pos more, if_neg different, List.length_append, List.length_cons, List.length_nil]
  · have equal : 1 + 6 * i.val = 6 * ps.length - 5 := by omega
    simp only [if_neg more, if_pos equal, List.length_append, List.length_cons, List.length_nil]

theorem familyRaw_backbone_h_degree (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (recordNeighbors (familyRaw ps) (2 + 6 * i.val)).length = 1 := by
  have records := blocksResult_backbone_h_records ps initialHydrogenState 0 initial_chronological
    (by decide) i.val i.isLt
  have initialSize : initialHydrogenState.atoms.length = 1 := rfl
  rw [initialSize] at records
  have indexEq : 1 + 6 * i.val + 1 = 2 + 6 * i.val := by omega
  rw [indexEq] at records
  have parent : blocksParent ps initialHydrogenState 0 ≠ 2 + 6 * i.val := by
    rcases blocksParent_shape ps initialHydrogenState 0 (Or.inl rfl) ⟨0, rfl⟩ with h | ⟨k, h⟩
    · omega
    · omega
  have fresh : (blocksResult ps initialHydrogenState 0).atoms.length ≠ 2 + 6 * i.val := by
    rw [blocksResult_atom_count]
    have hi := i.isLt
    change 1 + 6 * ps.length ≠ _
    omega
  rw [← familyState_molecule]
  change (recordNeighbors (attachSingle _ _ _).molecule _).length = 1
  rw [attachSingle_recordNeighbors_preserved _ _ _ _ parent fresh, records]
  rfl

theorem familyRaw_left_degree (ps : List TetrahedralInputParity) :
    (recordNeighbors (familyRaw ps) 0).length = 1 := by
  have records := blocksResult_parent_records ps initialHydrogenState 0 (by decide)
  have bound : 0 < (blocksResult ps initialHydrogenState 0).atoms.length :=
    lt_of_le_of_lt (Nat.zero_le _) (blocksParent_bounded ps initialHydrogenState 0 (by decide))
  rw [← familyState_molecule]
  change (recordNeighbors (attachSingle _ _ _).molecule 0).length = 1
  rw [attachSingle_old_records _ _ _ _ bound, records]
  have initialRow : recordNeighbors initialHydrogenState.molecule 0 = [] := rfl
  rw [initialRow, List.nil_append]
  cases ps with
  | nil => rfl
  | cons parity rest =>
      have last := family_last_parent (parity :: rest)
      rw [last]
      have positive : 0 ≠ 6 * (rest.length + 1) - 5 := by omega
      simp only [List.cons_ne_nil, if_false, List.length_cons]
      rw [if_neg positive, List.append_nil]
      rfl

theorem familyRaw_right_degree (ps : List TetrahedralInputParity) :
    (recordNeighbors (familyRaw ps) (6 * ps.length + 1)).length = 1 := by
  have physical := blocksResult_chronological ps initialHydrogenState 0 initial_chronological (by decide)
  have bound := blocksParent_bounded ps initialHydrogenState 0 (by decide)
  have records := attachSingle_fresh_records (blocksResult ps initialHydrogenState 0)
    (blocksParent ps initialHydrogenState 0) (atomSpec .hydrogen) physical bound
  have count : (blocksResult ps initialHydrogenState 0).atoms.length = 6 * ps.length + 1 := by
    rw [blocksResult_atom_count]
    change 1 + 6 * ps.length = _
    omega
  rw [count] at records
  rw [← familyState_molecule]
  change (recordNeighbors (attachSingle _ _ _).molecule _).length = 1
  rw [records]
  rfl

/-! ### General all-single incidence fold and encoded valence -/


-- all_single_incident_fold is re-exported from NativeSingleBondRawSupport.


-- all_single_incident_sum is re-exported from NativeSingleBondRawSupport.


def roleDegree {ps : List TetrahedralInputParity} : TraversalRole ps → ℕ
  | .backbone _ => 4
  | .taggedCarbon _ => 4
  | _ => 1

/-- Exact physical saturation, stronger than the encoded upper-bound valence contract. -/
theorem familyRaw_role_degree (ps : List TetrahedralInputParity) (role : TraversalRole ps) :
    (recordNeighbors (familyRaw ps) (roleIndex role)).length = roleDegree role := by
  cases role with
  | leftHydrogen => exact familyRaw_left_degree ps
  | rightHydrogen => exact familyRaw_right_degree ps
  | backbone i => exact familyRaw_backbone_degree ps i
  | backboneHydrogen i => exact familyRaw_backbone_h_degree ps i
  | taggedCarbon i =>
      simpa only [roleIndex, roleDegree, List.length_cons, List.length_nil] using
        congrArg List.length (familyRaw_pendant_records ps i).1
  | pendantHydrogen i =>
      simpa only [roleIndex, roleDegree, List.length_cons, List.length_nil] using
        congrArg List.length (familyRaw_pendant_records ps i).2.1
  | pendantFluorine i =>
      simpa only [roleIndex, roleDegree, List.length_cons, List.length_nil] using
        congrArg List.length (familyRaw_pendant_records ps i).2.2.1
  | pendantBromine i =>
      simpa only [roleIndex, roleDegree, List.length_cons, List.length_nil] using
        congrArg List.length (familyRaw_pendant_records ps i).2.2.2

theorem roleSpec_zero_explicit {ps : List TetrahedralInputParity} (role : TraversalRole ps) :
    (roleSpec role).explicitHydrogens = 0 := by
  cases role <;> rfl

theorem roleDegree_allowed {ps : List TetrahedralInputParity} (role : TraversalRole ps) :
    roleDegree role ∈ (roleSpec role).allowedValences := by
  cases role <;> simp [roleDegree, roleSpec, atomSpec, AtomSpec.allowedValences,
    Element.allowedValences]

theorem familyRaw_used_valence_role (ps : List TetrahedralInputParity) (role : TraversalRole ps) :
    (familyRaw ps).usedValenceAt (roleIndex role) = roleDegree role := by
  unfold RawMolecule.usedValenceAt
  rw [familyRaw_atomAt?_role]
  change (roleSpec role).explicitHydrogens + (familyRaw ps).incidentBondOrderSum (roleIndex role) = _
  rw [roleSpec_zero_explicit, all_single_incident_sum _ (familyRaw_all_single ps),
    familyRaw_role_degree, Nat.zero_add]

/-- Unconditional encoded valence for every arbitrary-parity actual STRING family, including
its zero-tag HH member. No valence or desired intake success is a premise. -/
theorem familyRaw_valenceOK (ps : List TetrahedralInputParity) : (familyRaw ps).ValenceOK := by
  intro index spec lookup
  obtain ⟨role, indexEq, specEq⟩ := familyRaw_atomAt?_role_of_lookup ps index spec lookup
  rw [← indexEq, ← specEq]
  exact ⟨roleDegree role, roleDegree_allowed role,
    le_of_eq (familyRaw_used_valence_role ps role)⟩

end TetraStereo.UniversalProof.ChronologicalFamilyPhysicalBridge
