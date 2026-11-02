import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import TetraStereo.UniversalProof.GeneralWrittenNeighborBridge
import TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.GeneralParserStateBridge
open TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery




















/-! ## Frozen role table (shared contract) -/

/-- The twelve independent roles of one second-sphere parity block, in written append order. -/
inductive FamilyRole where
  | backboneCarbon
  | backboneHydrogen
  | bridgeCarbon
  | bridgeHydrogenA
  | bridgeHydrogenB
  | tagCarbon
  | tagHydrogen
  | fluorine
  | methylCarbon
  | methylHydrogenA
  | methylHydrogenB
  | methylHydrogenC
  deriving DecidableEq, Repr

/-- Frozen append order of the twelve roles; the constructor consumes exactly this list. -/
def blockRoles : List FamilyRole :=
  [.backboneCarbon, .backboneHydrogen, .bridgeCarbon, .bridgeHydrogenA,
   .bridgeHydrogenB, .tagCarbon, .tagHydrogen, .fluorine,
   .methylCarbon, .methylHydrogenA, .methylHydrogenB, .methylHydrogenC]

theorem blockRoles_length : blockRoles.length = 12 := rfl

/-- Local block offset of each role (0..11). -/
def roleOffset : FamilyRole → ℕ
  | .backboneCarbon => 0
  | .backboneHydrogen => 1
  | .bridgeCarbon => 2
  | .bridgeHydrogenA => 3
  | .bridgeHydrogenB => 4
  | .tagCarbon => 5
  | .tagHydrogen => 6
  | .fluorine => 7
  | .methylCarbon => 8
  | .methylHydrogenA => 9
  | .methylHydrogenB => 10
  | .methylHydrogenC => 11

/-- Inverse lookup: the role written at a fixed local block offset. -/
def roleOfOffset : ℕ → FamilyRole
  | 0 => .backboneCarbon
  | 1 => .backboneHydrogen
  | 2 => .bridgeCarbon
  | 3 => .bridgeHydrogenA
  | 4 => .bridgeHydrogenB
  | 5 => .tagCarbon
  | 6 => .tagHydrogen
  | 7 => .fluorine
  | 8 => .methylCarbon
  | 9 => .methylHydrogenA
  | 10 => .methylHydrogenB
  | _ => .methylHydrogenC

theorem roleOffset_roleOfOffset (k : ℕ) (hk : k < 12) : roleOffset (roleOfOffset k) = k := by
  interval_cases k <;> rfl

theorem roleOfOffset_tag_iff (k : ℕ) (hk : k < 12) :
    roleOfOffset k = .tagCarbon ↔ k = 5 := by
  interval_cases k <;> simp [roleOfOffset]

/-- Frozen parent offset of each role relative to the block base; `none` is the continuation
parent handed to the block from the previous block (or the initial `[H]` cap). -/
def roleParentOffset : FamilyRole → Option ℕ
  | .backboneCarbon => none
  | .backboneHydrogen => some 0
  | .bridgeCarbon => some 0
  | .bridgeHydrogenA => some 2
  | .bridgeHydrogenB => some 2
  | .tagCarbon => some 2
  | .tagHydrogen => some 5
  | .fluorine => some 5
  | .methylCarbon => some 5
  | .methylHydrogenA => some 8
  | .methylHydrogenB => some 8
  | .methylHydrogenC => some 8

def carbonSpec : AtomSpec := atomSpec .carbon
def hydrogenSpec : AtomSpec := atomSpec .hydrogen
def fluorineSpec : AtomSpec := atomSpec .fluorine

/-- Atom spelling of each role at one block; only `tagCarbon` is parity-annotated. -/
def roleAtom (parity : TetrahedralInputParity) : FamilyRole → AtomSpec
  | .backboneCarbon => carbonSpec
  | .backboneHydrogen => hydrogenSpec
  | .bridgeCarbon => carbonSpec
  | .bridgeHydrogenA => hydrogenSpec
  | .bridgeHydrogenB => hydrogenSpec
  | .tagCarbon => atomSpec (.taggedCarbon parity)
  | .tagHydrogen => hydrogenSpec
  | .fluorine => fluorineSpec
  | .methylCarbon => carbonSpec
  | .methylHydrogenA => hydrogenSpec
  | .methylHydrogenB => hydrogenSpec
  | .methylHydrogenC => hydrogenSpec

/-- The twelve block atoms in written append order. -/
def blockAtoms (parity : TetrahedralInputParity) : List AtomSpec :=
  blockRoles.map (roleAtom parity)

theorem blockAtoms_length (parity : TetrahedralInputParity) : (blockAtoms parity).length = 12 := by
  simp [blockAtoms, blockRoles]

theorem roleAtom_tetrahedral (parity : TetrahedralInputParity) (role : FamilyRole) :
    (roleAtom parity role).tetrahedral? =
      if role = .tagCarbon then some parity else none := by
  cases role <;> rfl

theorem hydrogenSpec_tetrahedral : hydrogenSpec.tetrahedral? = none := rfl

/-- Global index of the tag carbon of block `i` (0-based, initial `[H]` cap at index 0). -/
def tagIndex (i : ℕ) : ℕ := 12 * i + 6

/-! ## Elementary local list lookups -/

theorem listGet?_map {α β : Type*} (f : α → β) (l : List α) (k : ℕ) :
    listGet? (l.map f) k = (listGet? l k).map f := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
      cases k with
      | zero => rfl
      | succ k => simpa [listGet?, List.map_cons] using ih k

theorem listGet?_append_right {α : Type*} (xs ys : List α) (k : ℕ) :
    listGet? (xs ++ ys) (xs.length + k) = listGet? ys k := by
  induction xs generalizing k with
  | nil => simp
  | cons a xs ih =>
      have hlen : (a :: xs).length + k = xs.length + k + 1 := by
        simp [List.length_cons]; omega
      rw [hlen, List.cons_append]
      simp only [listGet?]
      exact ih k

theorem listGet?_append_right_twelve {α : Type*} (xs ys : List α) (k : ℕ)
    (hlen : xs.length = 12) :
    listGet? (xs ++ ys) (12 + k) = listGet? ys k := by
  rw [← hlen]
  exact listGet?_append_right xs ys k

theorem listGet?_append_left {α : Type*} (xs ys : List α) (k : ℕ) (hk : k < xs.length) :
    listGet? (xs ++ ys) k = listGet? xs k := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons a xs ih =>
      cases k with
      | zero => rfl
      | succ k =>
          have hk' : k < xs.length := by simpa using hk
          rw [List.cons_append]
          simp only [listGet?]
          exact ih k hk'

theorem listGet?_singleton {α : Type*} (a : α) (m : ℕ) :
    listGet? [a] m = if m = 0 then some a else none := by
  cases m <;> simp [listGet?]

theorem listGet?_blockRoles (k : ℕ) (hk : k < 12) :
    listGet? blockRoles k = some (roleOfOffset k) := by
  interval_cases k <;> rfl

theorem blockAtoms_get (parity : TetrahedralInputParity) (k : ℕ) (hk : k < 12) :
    listGet? (blockAtoms parity) k = some (roleAtom parity (roleOfOffset k)) := by
  rw [blockAtoms, listGet?_map, listGet?_blockRoles k hk]
  rfl

theorem flatMap_blockAtoms_length (ps : List TetrahedralInputParity) :
    (ps.flatMap blockAtoms).length = 12 * ps.length := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
      rw [List.flatMap_cons, List.length_append, blockAtoms_length, ih, List.length_cons]
      ring

theorem listGet?_flatMap_blocks (ps : List TetrahedralInputParity) (j : ℕ)
    (hj : j < 12 * ps.length) :
    listGet? (ps.flatMap blockAtoms) j =
      (listGet? ps (j / 12)).bind (fun p => listGet? (blockAtoms p) (j % 12)) := by
  induction ps generalizing j with
  | nil => simp at hj
  | cons parity rest ih =>
      rw [List.flatMap_cons]
      rcases Nat.lt_or_ge j 12 with hsmall | hbig
      · rw [listGet?_append_left _ _ j (by rw [blockAtoms_length]; exact hsmall)]
        rw [Nat.div_eq_of_lt hsmall, Nat.mod_eq_of_lt hsmall]
        rfl
      · obtain ⟨j', rfl⟩ : ∃ j', j = 12 + j' := ⟨j - 12, by omega⟩
        have hj' : j' < 12 * rest.length := by
          have : 12 + j' < 12 * (rest.length + 1) := by simpa [List.length_cons] using hj
          rw [Nat.mul_succ] at this
          omega
        rw [listGet?_append_right_twelve _ _ _ (blockAtoms_length parity)]
        rw [ih j' hj']
        rw [show (12 + j') / 12 = j' / 12 + 1 by omega,
            show (12 + j') % 12 = j' % 12 by omega]
        rfl

theorem listGet?_flatMap_blocks_high (ps : List TetrahedralInputParity) (j : ℕ)
    (hj : 12 * ps.length ≤ j) :
    listGet? (ps.flatMap blockAtoms ++ [hydrogenSpec]) j =
      if j = 12 * ps.length then some hydrogenSpec else none := by
  have hlen : (ps.flatMap blockAtoms).length = 12 * ps.length := flatMap_blockAtoms_length ps
  conv_lhs =>
    rw [show j = (ps.flatMap blockAtoms).length + (j - 12 * ps.length) by omega]
  rw [listGet?_append_right, listGet?_singleton]
  by_cases h : j = 12 * ps.length
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem Option.bind_assoc' {α β γ : Type*} (o : Option α) (f : α → Option β)
    (g : β → Option γ) :
    (o.bind f).bind g = o.bind (fun x => (f x).bind g) := by
  cases o <;> rfl

theorem Option.bind_tag {α : Type*} (a : Option α) (c : Prop) [Decidable c] :
    (a.bind (fun q => if c then some q else none)) = if c then a else none := by
  by_cases h : c <;> simp [h]

/-! ## The bundled physical invariant and the base molecule -/

/-- One independent invariant carrying raw well-formedness, stored written exactness, the actual
forward/unique-child chronological record and unordered-edge uniqueness together. -/
def BlockGood (mol : RawMolecule) : Prop :=
  mol.WellFormed ∧
    StoredRowExact mol ∧
      ChronologicalRecords mol.atoms mol.bonds ∧
        mol.BondRecordsUnique

def family543Base : RawMolecule :=
  { atoms := [hydrogenSpec], bonds := [], neighborOrder := [[]],
    introductionPredecessors := [none] }

def baseFin : Fin family543Base.atomCount :=
  ⟨0, by simp [family543Base, RawMolecule.atomCount]⟩

theorem family543Base_blockGood : BlockGood family543Base := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro bond hmem; simp [family543Base] at hmem
  · refine ⟨by simp [family543Base, RawMolecule.atomCount], ?_⟩
    intro i
    have hzero : i.val = 0 := by
      have hbound : i.val < 1 := i.isLt
      omega
    unfold WrittenRowExactAt
    rw [hzero]
    simp [family543Base, RawMolecule.writtenNeighbors, RawMolecule.bondOrder,
      RawMolecule.directedBondOrder]
  · refine ⟨?_, ?_, ?_⟩
    · intro bond hmem; simp [family543Base] at hmem
    · intro bond hmem; simp [family543Base] at hmem
    · simp [family543Base]
  · unfold RawMolecule.BondRecordsUnique; simp [family543Base]



theorem appendFreshChild_wellFormed (mol : RawMolecule) (parent : Fin mol.atomCount)
    (child : AtomSpec) (hwf : mol.WellFormed) :
    (appendFreshChild mol parent child).WellFormed := by
  intro bond hmem
  rw [appendFreshChild_bonds] at hmem
  rcases List.mem_append.mp hmem with hold | hfresh
  · obtain ⟨h1, h2, h3⟩ := hwf bond hold
    refine ⟨?_, ?_, h3⟩
    · rw [appendFreshChild_atomCount]; omega
    · rw [appendFreshChild_atomCount]; omega
  · have hb := List.mem_singleton.mp hfresh
    subst hb
    refine ⟨?_, ?_, ?_⟩
    · rw [appendFreshChild_atomCount]; dsimp only [freshBond]; omega
    · rw [appendFreshChild_atomCount]; dsimp only [freshBond]; omega
    · unfold freshBond; exact Nat.ne_of_lt parent.isLt

theorem appendFreshChild_bondCount (mol : RawMolecule) (parent : Fin mol.atomCount)
    (child : AtomSpec) :
    (appendFreshChild mol parent child).bonds.length = mol.bonds.length + 1 := by
  rw [appendFreshChild_bonds, List.length_append, List.length_singleton]

theorem appendFreshChild_chronological (mol : RawMolecule) (parent : Fin mol.atomCount)
    (child : AtomSpec) (h : ChronologicalRecords mol.atoms mol.bonds) :
    ChronologicalRecords (appendFreshChild mol parent child).atoms
      (appendFreshChild mol parent child).bonds := by
  rw [appendFreshChild_atoms, appendFreshChild_bonds]
  refine ⟨?_, ?_, ?_⟩
  · intro bond hmem
    rcases List.mem_append.mp hmem with hold | hfresh
    · exact h.forward bond hold
    · have hb := List.mem_singleton.mp hfresh
      subst hb
      simpa only [freshBond] using parent.isLt
  · intro bond hmem
    rcases List.mem_append.mp hmem with hold | hfresh
    · have b := h.bounded bond hold
      simp only [List.length_append, List.length_singleton]
      omega
    · have hb := List.mem_singleton.mp hfresh
      subst hb
      change mol.atomCount < (mol.atoms ++ [child]).length
      rw [List.length_append, List.length_singleton]
      change mol.atomCount < mol.atomCount + 1
      omega
  · rw [List.map_append]
    refine List.nodup_append.mpr ⟨h.targets, by simp, ?_⟩
    intro a ha b hb
    rcases List.mem_map.mp ha with ⟨bond, hmem, rfl⟩
    have hb' := List.mem_singleton.mp hb
    have b := h.bounded bond hmem
    rw [hb']
    change bond.target ≠ mol.atomCount
    change bond.target < mol.atomCount at b
    omega

theorem appendFreshChild_blockGood (mol : RawMolecule) (parent : Fin mol.atomCount)
    (child : AtomSpec) (h : BlockGood mol) :
    BlockGood (appendFreshChild mol parent child) :=
  ⟨appendFreshChild_wellFormed mol parent child h.1,
   appendFreshChild_storedRowExact mol parent child h.1 h.2.1,
   appendFreshChild_chronological mol parent child h.2.2.1,
   appendFreshChild_bondRecordsUnique mol parent child h.1 h.2.2.2⟩

/-! ## The twelve-append block constructor -/

/-- One block: twelve ordinary raw appends whose parent offsets are the frozen role table.
The first append attaches the backbone carbon to the continuation parent; the remaining eleven
attach to earlier atoms of the same block, so no supplied output is consulted. -/
def blockAppend (mol : RawMolecule) (base : ℕ) (hbase : mol.atomCount = base)
    (externalParent : Fin mol.atomCount) (parity : TetrahedralInputParity) : RawMolecule := by
  let s1 := appendFreshChild mol externalParent (roleAtom parity .backboneCarbon)
  have h1 : s1.atomCount = base + 1 := by rw [appendFreshChild_atomCount, hbase]
  let s2 := appendFreshChild s1 ⟨base, by omega⟩ (roleAtom parity .backboneHydrogen)
  have h2 : s2.atomCount = base + 2 := by rw [appendFreshChild_atomCount, h1]
  let s3 := appendFreshChild s2 ⟨base, by omega⟩ (roleAtom parity .bridgeCarbon)
  have h3 : s3.atomCount = base + 3 := by rw [appendFreshChild_atomCount, h2]
  let s4 := appendFreshChild s3 ⟨base + 2, by omega⟩ (roleAtom parity .bridgeHydrogenA)
  have h4 : s4.atomCount = base + 4 := by rw [appendFreshChild_atomCount, h3]
  let s5 := appendFreshChild s4 ⟨base + 2, by omega⟩ (roleAtom parity .bridgeHydrogenB)
  have h5 : s5.atomCount = base + 5 := by rw [appendFreshChild_atomCount, h4]
  let s6 := appendFreshChild s5 ⟨base + 2, by omega⟩ (roleAtom parity .tagCarbon)
  have h6 : s6.atomCount = base + 6 := by rw [appendFreshChild_atomCount, h5]
  let s7 := appendFreshChild s6 ⟨base + 5, by omega⟩ (roleAtom parity .tagHydrogen)
  have h7 : s7.atomCount = base + 7 := by rw [appendFreshChild_atomCount, h6]
  let s8 := appendFreshChild s7 ⟨base + 5, by omega⟩ (roleAtom parity .fluorine)
  have h8 : s8.atomCount = base + 8 := by rw [appendFreshChild_atomCount, h7]
  let s9 := appendFreshChild s8 ⟨base + 5, by omega⟩ (roleAtom parity .methylCarbon)
  have h9 : s9.atomCount = base + 9 := by rw [appendFreshChild_atomCount, h8]
  let s10 := appendFreshChild s9 ⟨base + 8, by omega⟩ (roleAtom parity .methylHydrogenA)
  have h10 : s10.atomCount = base + 10 := by rw [appendFreshChild_atomCount, h9]
  let s11 := appendFreshChild s10 ⟨base + 8, by omega⟩ (roleAtom parity .methylHydrogenB)
  have h11 : s11.atomCount = base + 11 := by rw [appendFreshChild_atomCount, h10]
  let s12 := appendFreshChild s11 ⟨base + 8, by omega⟩ (roleAtom parity .methylHydrogenC)
  exact s12

theorem blockAppend_blockGood (mol : RawMolecule) (base : ℕ) (hbase : mol.atomCount = base)
    (externalParent : Fin mol.atomCount) (parity : TetrahedralInputParity) (h : BlockGood mol) :
    BlockGood (blockAppend mol base hbase externalParent parity) := by
  unfold blockAppend
  dsimp only
  repeat (first | apply appendFreshChild_blockGood)
  exact h

theorem blockAppend_atomCount (mol : RawMolecule) (base : ℕ) (hbase : mol.atomCount = base)
    (externalParent : Fin mol.atomCount) (parity : TetrahedralInputParity) :
    (blockAppend mol base hbase externalParent parity).atomCount = base + 12 := by
  unfold blockAppend
  dsimp only
  simp only [appendFreshChild_atomCount]
  rw [hbase]

theorem blockAppend_bondCount (mol : RawMolecule) (base : ℕ) (hbase : mol.atomCount = base)
    (externalParent : Fin mol.atomCount) (parity : TetrahedralInputParity) :
    (blockAppend mol base hbase externalParent parity).bonds.length = mol.bonds.length + 12 := by
  unfold blockAppend
  dsimp only
  simp only [appendFreshChild_bondCount]

theorem blockAppend_atoms (mol : RawMolecule) (base : ℕ) (hbase : mol.atomCount = base)
    (externalParent : Fin mol.atomCount) (parity : TetrahedralInputParity) :
    (blockAppend mol base hbase externalParent parity).atoms = mol.atoms ++ blockAtoms parity := by
  unfold blockAppend
  dsimp only
  simp only [appendFreshChild_atoms, List.append_assoc,
    blockAtoms, blockRoles, List.map_cons, List.map_nil, List.cons_append, List.nil_append]

/-! ## The whole family: fold the block constructor over the parity list -/

def blocksResult543 :
    List TetrahedralInputParity → (mol : RawMolecule) → Fin mol.atomCount → RawMolecule
  | [], mol, _ => mol
  | parity :: rest, mol, parent =>
      blocksResult543 rest
        (blockAppend mol mol.atomCount rfl parent parity)
        ⟨mol.atomCount, by rw [blockAppend_atomCount]; omega⟩

def blocksParent543 :
    List TetrahedralInputParity → (mol : RawMolecule) → Fin mol.atomCount → ℕ
  | [], _, parent => parent.val
  | parity :: rest, mol, parent =>
      blocksParent543 rest
        (blockAppend mol mol.atomCount rfl parent parity)
        ⟨mol.atomCount, by rw [blockAppend_atomCount]; omega⟩

theorem blocksResult543_atomCount (ps : List TetrahedralInputParity) (mol : RawMolecule)
    (parent : Fin mol.atomCount) :
    (blocksResult543 ps mol parent).atomCount = mol.atomCount + 12 * ps.length := by
  induction ps generalizing mol parent with
  | nil => simp [blocksResult543]
  | cons parity rest ih =>
      simp only [blocksResult543]
      rw [ih, blockAppend_atomCount, List.length_cons]
      ring

theorem blocksResult543_bondCount (ps : List TetrahedralInputParity) (mol : RawMolecule)
    (parent : Fin mol.atomCount) :
    (blocksResult543 ps mol parent).bonds.length = mol.bonds.length + 12 * ps.length := by
  induction ps generalizing mol parent with
  | nil => simp [blocksResult543]
  | cons parity rest ih =>
      simp only [blocksResult543]
      rw [ih, blockAppend_bondCount, List.length_cons]
      ring

theorem blocksResult543_blockGood (ps : List TetrahedralInputParity) (mol : RawMolecule)
    (parent : Fin mol.atomCount) (h : BlockGood mol) :
    BlockGood (blocksResult543 ps mol parent) := by
  induction ps generalizing mol parent with
  | nil => exact h
  | cons parity rest ih =>
      simp only [blocksResult543]
      exact ih (blockAppend mol mol.atomCount rfl parent parity)
        ⟨mol.atomCount, by rw [blockAppend_atomCount]; omega⟩
        (blockAppend_blockGood mol mol.atomCount rfl parent parity h)

theorem blocksResult543_atoms (ps : List TetrahedralInputParity) (mol : RawMolecule)
    (parent : Fin mol.atomCount) :
    (blocksResult543 ps mol parent).atoms = mol.atoms ++ ps.flatMap blockAtoms := by
  induction ps generalizing mol parent with
  | nil => simp [blocksResult543]
  | cons parity rest ih =>
      simp only [blocksResult543, ih, blockAppend_atoms, List.flatMap_cons, List.append_assoc]

theorem blocksParent543_bounded (ps : List TetrahedralInputParity) (mol : RawMolecule)
    (parent : Fin mol.atomCount) :
    blocksParent543 ps mol parent < (blocksResult543 ps mol parent).atomCount := by
  induction ps generalizing mol parent with
  | nil => exact parent.isLt
  | cons parity rest ih =>
      simp only [blocksParent543, blocksResult543]
      exact ih (blockAppend mol mol.atomCount rfl parent parity)
        ⟨mol.atomCount, by rw [blockAppend_atomCount]; omega⟩

/-- The independent second-sphere family: initial `[H]` cap, `n` twelve-append blocks, final `[H]`
cap.  Built entirely from raw appends; the parser is never invoked. -/
def familyRaw (parities : List TetrahedralInputParity) : RawMolecule :=
  let constructed := blocksResult543 parities family543Base baseFin
  let parent := blocksParent543 parities family543Base baseFin
  appendFreshChild constructed
    ⟨parent, blocksParent543_bounded parities family543Base baseFin⟩ hydrogenSpec

theorem familyRaw_atoms (ps : List TetrahedralInputParity) :
    (familyRaw ps).atoms =
      [hydrogenSpec] ++ (ps.flatMap blockAtoms ++ [hydrogenSpec]) := by
  unfold familyRaw
  dsimp only
  rw [appendFreshChild_atoms, blocksResult543_atoms]
  simp only [family543Base, List.append_assoc]

/-! ## The six owned declarations -/

theorem familyRaw_atomCount (ps : List TetrahedralInputParity) :
    (familyRaw ps).atomCount = 12 * ps.length + 2 := by
  unfold familyRaw
  dsimp only
  rw [appendFreshChild_atomCount, blocksResult543_atomCount]
  simp only [family543Base, RawMolecule.atomCount, List.length_singleton]
  ring

theorem familyRaw_bondCount (ps : List TetrahedralInputParity) :
    (familyRaw ps).bonds.length = 12 * ps.length + 1 := by
  unfold familyRaw
  dsimp only
  rw [appendFreshChild_bondCount, blocksResult543_bondCount]
  simp only [family543Base, List.length_nil]
  ring

theorem familyRaw_blockGood (ps : List TetrahedralInputParity) : BlockGood (familyRaw ps) := by
  unfold familyRaw
  dsimp only
  apply appendFreshChild_blockGood
  exact blocksResult543_blockGood ps family543Base baseFin family543Base_blockGood

theorem familyRaw_wellFormed (ps : List TetrahedralInputParity) :
    (familyRaw ps).WellFormed :=
  (familyRaw_blockGood ps).1

theorem familyRaw_bondRecordsUnique (ps : List TetrahedralInputParity) :
    (familyRaw ps).BondRecordsUnique :=
  (familyRaw_blockGood ps).2.2.2

theorem familyRaw_chronological (ps : List TetrahedralInputParity) :
    ChronologicalRecords (familyRaw ps).atoms (familyRaw ps).bonds :=
  (familyRaw_blockGood ps).2.2.1

/-- Actual chronological forward invariant: every stored bond points strictly forward. -/
theorem familyRaw_forward (ps : List TetrahedralInputParity) :
    ∀ bond, bond ∈ (familyRaw ps).bonds → bond.source < bond.target :=
  (familyRaw_chronological ps).forward

/-- Actual unique-child invariant: no two stored bonds share a target index. -/
theorem familyRaw_uniqueChild (ps : List TetrahedralInputParity) :
    ((familyRaw ps).bonds.map RawBond.target).Nodup :=
  (familyRaw_chronological ps).targets

theorem storedRowExact_writtenNeighborExact (mol : RawMolecule) (h : StoredRowExact mol) :
    mol.WrittenNeighborExact := by
  apply WrittenNeighborExact.of_at
  intro center
  have row := h.2 center
  exact ⟨row.1, row.2.1, fun ligand => row.2.2 ligand.val ligand.isLt⟩

theorem familyRaw_writtenNeighborExact (ps : List TetrahedralInputParity) :
    (familyRaw ps).WrittenNeighborExact :=
  storedRowExact_writtenNeighborExact (familyRaw ps)
    (familyRaw_blockGood ps).2.1

/-! ## Actual tags and the tag/parity inverse -/

/-- The observed tetrahedral annotation of the constructed molecule at an absolute index. -/
def observedTag (mol : RawMolecule) (k : ℕ) : Option TetrahedralInputParity :=
  (mol.atomAt? k).bind AtomSpec.tetrahedral?

/-- Every annotated index of the constructed family is exactly a block tag index, and the value
observed there is exactly the corresponding input parity.  This is the actual tag/parity inverse
over the constructed atom table. -/
theorem familyRaw_observedTag_iff (ps : List TetrahedralInputParity) (k : ℕ)
    (p : TetrahedralInputParity) :
    observedTag (familyRaw ps) k = some p ↔
      ∃ i : Fin ps.length, k = tagIndex i.val ∧ ps[i.val] = p := by
  have hatoms : (familyRaw ps).atoms =
      [hydrogenSpec] ++ (ps.flatMap blockAtoms ++ [hydrogenSpec]) := familyRaw_atoms ps
  rw [observedTag, RawMolecule.atomAt?, hatoms]
  cases k with
  | zero =>
      simp only [List.singleton_append, listGet?]
      rw [show (some hydrogenSpec).bind AtomSpec.tetrahedral? =
          (none : Option TetrahedralInputParity) by
        simp [hydrogenSpec, atomSpec]]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨i, hk, -⟩
        rw [tagIndex] at hk
        exact absurd hk (by omega)
  | succ k' =>
      rw [show k' + 1 = [hydrogenSpec].length + k' by
        simp only [List.length_singleton]; omega]
      rw [listGet?_append_right]
      by_cases hlow : k' < 12 * ps.length
      · rw [listGet?_append_left _ _ k' (by rw [flatMap_blockAtoms_length]; exact hlow)]
        rw [listGet?_flatMap_blocks ps k' hlow]
        rw [Option.bind_assoc']
        have hinner : (fun q => (listGet? (blockAtoms q) (k' % 12)).bind
              AtomSpec.tetrahedral?) =
            (fun q => if roleOfOffset (k' % 12) = .tagCarbon then some q else none) := by
          funext q
          rw [blockAtoms_get q (k' % 12) (Nat.mod_lt _ (by decide))]
          change (roleAtom q (roleOfOffset (k' % 12))).tetrahedral? = _
          exact roleAtom_tetrahedral q (roleOfOffset (k' % 12))
        rw [hinner, Option.bind_tag]
        by_cases hc : roleOfOffset (k' % 12) = .tagCarbon
        · rw [if_pos hc]
          have hmod : k' % 12 = 5 :=
            (roleOfOffset_tag_iff (k' % 12) (Nat.mod_lt _ (by decide))).mp hc
          constructor
          · intro h
            have hlt : k' / 12 < ps.length := listGet?_eq_some_implies_lt ps (k' / 12) p h
            refine ⟨⟨k' / 12, hlt⟩, ?_, ?_⟩
            · change 1 + k' = 12 * (k' / 12) + 6
              have := Nat.div_add_mod k' 12
              omega
            · have hget := listGet?_eq_some_get ps ⟨k' / 12, hlt⟩
              rw [h] at hget
              exact (Option.some.inj hget).symm
          · rintro ⟨i, hk, hp⟩
            simp only [tagIndex, List.length_singleton] at hk
            have hidx : k' / 12 = i.val := by omega
            rw [hidx, ← hp]
            simpa using listGet?_eq_some_get ps i
        · rw [if_neg hc]
          constructor
          · intro h; exact absurd h (by simp)
          · rintro ⟨i, hk, -⟩
            exfalso
            apply hc
            simp only [tagIndex, List.length_singleton] at hk
            have hmod : k' % 12 = 5 := by omega
            rw [hmod]
            exact (roleOfOffset_tag_iff 5 (by decide)).mpr rfl
      · rw [listGet?_flatMap_blocks_high ps k' (by omega)]
        have hnone : (if k' = 12 * ps.length then some hydrogenSpec else none).bind
            AtomSpec.tetrahedral? = (none : Option TetrahedralInputParity) := by
          by_cases h : k' = 12 * ps.length <;> simp [h, hydrogenSpec, atomSpec]
        rw [hnone]
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨i, hk, -⟩
          simp only [tagIndex, List.length_singleton] at hk
          have hlt : i.val < ps.length := i.isLt
          have hk' : k' = 12 * i.val + 5 := by omega
          exact absurd (by omega : False) False.elim

end TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
