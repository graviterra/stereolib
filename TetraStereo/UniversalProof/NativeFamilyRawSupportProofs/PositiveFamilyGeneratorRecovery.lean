import TetraStereo.UniversalProof.NativeFamilyRawSupport
import TetraStereo.OneCenter.ExplicitHydrogens
import TetraStereo.OneCenter.BranchSphereKey
import TetraStereo.UniversalProof.ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity
import TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
import TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery
import TetraStereo.UniversalProof.ActualFamilyReportBridgeProofs.ActualFamilyReportBridge

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeFamilyRawSupportProofs.PositiveFamilyGeneratorRecovery

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity











/-! ## Atom constructors -/

def backboneCarbon : AtomSpec :=
  { AtomSpec.aliphatic .C with explicitHydrogens? := some 0 }

def pendantCarbon (parity : TetrahedralInputParity) : AtomSpec :=
  { AtomSpec.aliphatic .C with explicitHydrogens? := some 0, tetrahedral? := some parity }

def terminalHydrogen : AtomSpec :=
  { AtomSpec.aliphatic .H with explicitHydrogens? := some 0 }

def terminalFluorine : AtomSpec :=
  { AtomSpec.aliphatic .F with explicitHydrogens? := some 0 }

def terminalBromine : AtomSpec :=
  { AtomSpec.aliphatic .Br with explicitHydrogens? := some 0 }

/-- Decode an atom index into its role; the trailing `n + 2` indices are backbone hydrogens. -/
def atomAtIndex (n : ℕ) (parity : ℕ → TetrahedralInputParity) (idx : ℕ) : AtomSpec :=
  if idx < 5 * n then
    match idx % 5 with
    | 0 => backboneCarbon
    | 1 => pendantCarbon (parity (idx / 5))
    | 2 => terminalHydrogen
    | 3 => terminalFluorine
    | _ => terminalBromine
  else
    terminalHydrogen

def familyAtoms (n : ℕ) (parity : ℕ → TetrahedralInputParity) : List AtomSpec :=
  (List.range (6 * n + 2)).map (atomAtIndex n parity)

/-! ## Bond constructors -/

def chainBonds (n : ℕ) : List RawBond :=
  (List.range (n - 1)).map (fun j => (⟨5 * j, 5 * j + 5, ParsedBondKind.single⟩ : RawBond))

def pendantBonds (n : ℕ) : List RawBond :=
  (List.range n).map (fun i => (⟨5 * i, 5 * i + 1, ParsedBondKind.single⟩ : RawBond))

def terminalHBonds (n : ℕ) : List RawBond :=
  (List.range n).map (fun i => (⟨5 * i + 1, 5 * i + 2, ParsedBondKind.single⟩ : RawBond))

def terminalFBonds (n : ℕ) : List RawBond :=
  (List.range n).map (fun i => (⟨5 * i + 1, 5 * i + 3, ParsedBondKind.single⟩ : RawBond))

def terminalBrBonds (n : ℕ) : List RawBond :=
  (List.range n).map (fun i => (⟨5 * i + 1, 5 * i + 4, ParsedBondKind.single⟩ : RawBond))

def linkBonds (n : ℕ) : List RawBond :=
  (List.range n).map (fun i => (⟨5 * i, 5 * n + i, ParsedBondKind.single⟩ : RawBond))

def capLeftBonds (n : ℕ) : List RawBond := [⟨0, 6 * n, ParsedBondKind.single⟩]

def capRightBonds (n : ℕ) : List RawBond := [⟨5 * n - 5, 6 * n + 1, ParsedBondKind.single⟩]

/-- The complete generated bond list: `6*n + 1` records for `n ≥ 1`. -/
def familyBonds (n : ℕ) : List RawBond :=
  chainBonds n ++ pendantBonds n ++ terminalHBonds n ++ terminalFBonds n
    ++ terminalBrBonds n ++ linkBonds n ++ capLeftBonds n ++ capRightBonds n

def rawFamily (n : ℕ) (parity : ℕ → TetrahedralInputParity) : RawMolecule :=
  { atoms := familyAtoms n parity, bonds := familyBonds n, neighborOrder := [] }

/-- The canonicalized family consumed by stereochemical perception: the written-neighbour table is
replaced by the exact bonded-neighbour canonicalization of the same atoms and bonds. -/
def family (n : ℕ) (parity : ℕ → TetrahedralInputParity) : RawMolecule :=
  (rawFamily n parity).withExactWrittenNeighbors

/-! ## List bridge and atom-level facts -/

theorem listGet?_eq_getElem? {α : Type*} (l : List α) (i : ℕ) : listGet? l i = l[i]? := by
  induction l generalizing i with
  | nil => simp [listGet?]
  | cons head tail ih =>
      cases i with
      | zero => rfl
      | succ i => simpa [listGet?] using ih i

@[simp] theorem family_atoms (n : ℕ) (parity : ℕ → TetrahedralInputParity) :
    (family n parity).atoms = familyAtoms n parity := rfl

@[simp] theorem family_bonds (n : ℕ) (parity : ℕ → TetrahedralInputParity) :
    (family n parity).bonds = familyBonds n := rfl

@[simp] theorem rawFamily_atoms (n : ℕ) (parity : ℕ → TetrahedralInputParity) :
    (rawFamily n parity).atoms = familyAtoms n parity := rfl

@[simp] theorem rawFamily_bonds (n : ℕ) (parity : ℕ → TetrahedralInputParity) :
    (rawFamily n parity).bonds = familyBonds n := rfl

theorem familyAtoms_length (n : ℕ) (parity : ℕ → TetrahedralInputParity) :
    (familyAtoms n parity).length = 6 * n + 2 := by
  simp [familyAtoms]

theorem family_atomCount (n : ℕ) (parity : ℕ → TetrahedralInputParity) :
    (family n parity).atomCount = 6 * n + 2 := by
  show (familyAtoms n parity).length = 6 * n + 2
  simp [familyAtoms]

theorem rawFamily_atomCount (n : ℕ) (parity : ℕ → TetrahedralInputParity) :
    (rawFamily n parity).atomCount = 6 * n + 2 := by
  show (familyAtoms n parity).length = 6 * n + 2
  simp [familyAtoms]

theorem familyAtoms_getElem? (n : ℕ) (parity : ℕ → TetrahedralInputParity) (idx : ℕ)
    (h : idx < 6 * n + 2) :
    listGet? (familyAtoms n parity) idx = some (atomAtIndex n parity idx) := by
  unfold familyAtoms
  rw [listGet?_eq_getElem?]
  exact getElem?_map_range (atomAtIndex n parity) (6 * n + 2) idx h

theorem atomAtIndex_backbone (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ) (hi : i < n) :
    atomAtIndex n parity (5 * i) = backboneCarbon := by
  have hlt : 5 * i < 5 * n := by omega
  have hmod : (5 * i) % 5 = 0 := by omega
  simp only [atomAtIndex, if_pos hlt, hmod]

theorem atomAtIndex_tag (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ) (hi : i < n) :
    atomAtIndex n parity (5 * i + 1) = pendantCarbon (parity i) := by
  have hlt : 5 * i + 1 < 5 * n := by omega
  have hmod : (5 * i + 1) % 5 = 1 := by omega
  have hdiv : (5 * i + 1) / 5 = i := by omega
  simp only [atomAtIndex, if_pos hlt, hmod, hdiv]

theorem atomAtIndex_terminalH (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ) (hi : i < n) :
    atomAtIndex n parity (5 * i + 2) = terminalHydrogen := by
  have hlt : 5 * i + 2 < 5 * n := by omega
  have hmod : (5 * i + 2) % 5 = 2 := by omega
  simp only [atomAtIndex, if_pos hlt, hmod]

theorem atomAtIndex_terminalF (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ) (hi : i < n) :
    atomAtIndex n parity (5 * i + 3) = terminalFluorine := by
  have hlt : 5 * i + 3 < 5 * n := by omega
  have hmod : (5 * i + 3) % 5 = 3 := by omega
  simp only [atomAtIndex, if_pos hlt, hmod]

theorem atomAtIndex_terminalBr (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ) (hi : i < n) :
    atomAtIndex n parity (5 * i + 4) = terminalBromine := by
  have hlt : 5 * i + 4 < 5 * n := by omega
  have hmod : (5 * i + 4) % 5 = 4 := by omega
  simp only [atomAtIndex, if_pos hlt, hmod]

theorem atomAtIndex_hydrogen (n : ℕ) (parity : ℕ → TetrahedralInputParity) (j : ℕ)
    (hj : j < n + 2) :
    atomAtIndex n parity (5 * n + j) = terminalHydrogen := by
  have _ := hj
  have hge : ¬ 5 * n + j < 5 * n := by omega
  simp only [atomAtIndex, if_neg hge]

theorem familyAtoms_inlineCounts (n : ℕ) (parity : ℕ → TetrahedralInputParity) :
    ∀ a ∈ familyAtoms n parity, a.explicitHydrogens? = some 0 := by
  intro a ha
  rcases List.mem_map.mp ha with ⟨idx, _hidx, rfl⟩
  unfold atomAtIndex
  split
  · split <;> rfl
  · rfl

/-! ## Atom lookup on the generated family -/

theorem family_atomAt? (n : ℕ) (parity : ℕ → TetrahedralInputParity) (idx : ℕ)
    (hidx : idx < (family n parity).atomCount) :
    (family n parity).atomAt? idx = some (atomAtIndex n parity idx) := by
  unfold RawMolecule.atomAt?
  rw [family_atoms]
  exact familyAtoms_getElem? n parity idx (by rw [family_atomCount] at hidx; exact hidx)

theorem rawFamily_atomAt? (n : ℕ) (parity : ℕ → TetrahedralInputParity) (idx : ℕ)
    (hidx : idx < (rawFamily n parity).atomCount) :
    (rawFamily n parity).atomAt? idx = some (atomAtIndex n parity idx) := by
  unfold RawMolecule.atomAt?
  rw [rawFamily_atoms]
  exact familyAtoms_getElem? n parity idx (by rw [rawFamily_atomCount] at hidx; exact hidx)

theorem family_tag_atomAt? (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ) (hi : i < n) :
    (family n parity).atomAt? (5 * i + 1) = some (pendantCarbon (parity i)) := by
  have h : 5 * i + 1 < (family n parity).atomCount := by rw [family_atomCount]; omega
  rw [family_atomAt? n parity (5 * i + 1) h, atomAtIndex_tag n parity i hi]

theorem family_terminalH_atomAt? (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hi : i < n) : (family n parity).atomAt? (5 * i + 2) = some terminalHydrogen := by
  have h : 5 * i + 2 < (family n parity).atomCount := by rw [family_atomCount]; omega
  rw [family_atomAt? n parity (5 * i + 2) h, atomAtIndex_terminalH n parity i hi]

theorem family_terminalF_atomAt? (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hi : i < n) : (family n parity).atomAt? (5 * i + 3) = some terminalFluorine := by
  have h : 5 * i + 3 < (family n parity).atomCount := by rw [family_atomCount]; omega
  rw [family_atomAt? n parity (5 * i + 3) h, atomAtIndex_terminalF n parity i hi]

theorem family_terminalBr_atomAt? (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hi : i < n) : (family n parity).atomAt? (5 * i + 4) = some terminalBromine := by
  have h : 5 * i + 4 < (family n parity).atomCount := by rw [family_atomCount]; omega
  rw [family_atomAt? n parity (5 * i + 4) h, atomAtIndex_terminalBr n parity i hi]

theorem family_tag_parity (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ) (hi : i < n) :
    ((family n parity).atomAt? (5 * i + 1)).map AtomSpec.tetrahedral? = some (some (parity i)) := by
  rw [family_tag_atomAt? n parity i hi]
  rfl

theorem family_atomZAt_backbone (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hi : i < n) : (family n parity).atomZAt (5 * i) = 6 := by
  unfold RawMolecule.atomZAt
  have h : 5 * i < (family n parity).atomCount := by rw [family_atomCount]; omega
  rw [family_atomAt? n parity (5 * i) h, atomAtIndex_backbone n parity i hi]
  rfl

theorem family_atomZAt_terminalH (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hi : i < n) : (family n parity).atomZAt (5 * i + 2) = 1 := by
  unfold RawMolecule.atomZAt
  have h : 5 * i + 2 < (family n parity).atomCount := by rw [family_atomCount]; omega
  rw [family_atomAt? n parity (5 * i + 2) h, atomAtIndex_terminalH n parity i hi]
  rfl

theorem family_atomZAt_terminalF (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hi : i < n) : (family n parity).atomZAt (5 * i + 3) = 9 := by
  unfold RawMolecule.atomZAt
  have h : 5 * i + 3 < (family n parity).atomCount := by rw [family_atomCount]; omega
  rw [family_atomAt? n parity (5 * i + 3) h, atomAtIndex_terminalF n parity i hi]
  rfl

theorem family_atomZAt_terminalBr (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hi : i < n) : (family n parity).atomZAt (5 * i + 4) = 35 := by
  unfold RawMolecule.atomZAt
  have h : 5 * i + 4 < (family n parity).atomCount := by rw [family_atomCount]; omega
  rw [family_atomAt? n parity (5 * i + 4) h, atomAtIndex_terminalBr n parity i hi]
  rfl

/-- **Every observed tag is precisely one pendant index.** A stored tetrahedral annotation occurs
exactly at some block index `5*i+1`, and that block index is unique. -/
theorem atomAtIndex_tetrahedral (n : ℕ) (parity : ℕ → TetrahedralInputParity) (idx : ℕ)
    (a : TetrahedralInputParity)
    (h : (atomAtIndex n parity idx).tetrahedral? = some a) :
    ∃ i, i < n ∧ idx = 5 * i + 1 ∧ parity i = a := by
  by_cases hlt : idx < 5 * n
  · have hr : idx % 5 = 0 ∨ idx % 5 = 1 ∨ idx % 5 = 2 ∨ idx % 5 = 3 ∨ idx % 5 = 4 := by omega
    rcases hr with h0 | h1 | h2 | h3 | h4
    · simp [atomAtIndex, backboneCarbon, AtomSpec.aliphatic, hlt, h0] at h
    · refine ⟨idx / 5, ?_, ?_, ?_⟩
      · have d := Nat.div_add_mod idx 5; omega
      · have d := Nat.div_add_mod idx 5; omega
      · simpa [atomAtIndex, pendantCarbon, AtomSpec.aliphatic, hlt, h1] using h
    · simp [atomAtIndex, terminalHydrogen, AtomSpec.aliphatic, hlt, h2] at h
    · simp [atomAtIndex, terminalFluorine, AtomSpec.aliphatic, hlt, h3] at h
    · simp [atomAtIndex, terminalBromine, AtomSpec.aliphatic, hlt, h4] at h
  · simp [atomAtIndex, terminalHydrogen, AtomSpec.aliphatic, hlt] at h

theorem family_tagged_iff (n : ℕ) (parity : ℕ → TetrahedralInputParity) (idx : ℕ)
    (hidx : idx < (family n parity).atomCount) (a : TetrahedralInputParity) :
    ((family n parity).atomAt? idx).map AtomSpec.tetrahedral? = some (some a) ↔
      ∃ i, i < n ∧ idx = 5 * i + 1 ∧ parity i = a := by
  rw [family_atomAt? n parity idx hidx]
  constructor
  · intro h
    have h' : (atomAtIndex n parity idx).tetrahedral? = some a := by simpa using h
    obtain ⟨i, hi, hidx', hpar⟩ := atomAtIndex_tetrahedral n parity idx a h'
    exact ⟨i, hi, hidx', hpar⟩
  · rintro ⟨i, hi, rfl, rfl⟩
    rw [atomAtIndex_tag n parity i hi]
    rfl

/-! ## Bond membership -/

theorem mem_chainBonds {n : ℕ} {b : RawBond} :
    b ∈ chainBonds n ↔ ∃ j, j < n - 1 ∧
      (⟨5 * j, 5 * j + 5, ParsedBondKind.single⟩ : RawBond) = b := by
  simp only [chainBonds, List.mem_map, List.mem_range]

theorem mem_pendantBonds {n : ℕ} {b : RawBond} :
    b ∈ pendantBonds n ↔ ∃ i, i < n ∧
      (⟨5 * i, 5 * i + 1, ParsedBondKind.single⟩ : RawBond) = b := by
  simp only [pendantBonds, List.mem_map, List.mem_range]

theorem mem_terminalHBonds {n : ℕ} {b : RawBond} :
    b ∈ terminalHBonds n ↔ ∃ i, i < n ∧
      (⟨5 * i + 1, 5 * i + 2, ParsedBondKind.single⟩ : RawBond) = b := by
  simp only [terminalHBonds, List.mem_map, List.mem_range]

theorem mem_terminalFBonds {n : ℕ} {b : RawBond} :
    b ∈ terminalFBonds n ↔ ∃ i, i < n ∧
      (⟨5 * i + 1, 5 * i + 3, ParsedBondKind.single⟩ : RawBond) = b := by
  simp only [terminalFBonds, List.mem_map, List.mem_range]

theorem mem_terminalBrBonds {n : ℕ} {b : RawBond} :
    b ∈ terminalBrBonds n ↔ ∃ i, i < n ∧
      (⟨5 * i + 1, 5 * i + 4, ParsedBondKind.single⟩ : RawBond) = b := by
  simp only [terminalBrBonds, List.mem_map, List.mem_range]

theorem mem_linkBonds {n : ℕ} {b : RawBond} :
    b ∈ linkBonds n ↔ ∃ i, i < n ∧
      (⟨5 * i, 5 * n + i, ParsedBondKind.single⟩ : RawBond) = b := by
  simp only [linkBonds, List.mem_map, List.mem_range]

theorem mem_capLeftBonds {n : ℕ} {b : RawBond} :
    b ∈ capLeftBonds n ↔ (⟨0, 6 * n, ParsedBondKind.single⟩ : RawBond) = b := by
  simp [capLeftBonds, eq_comm]

theorem mem_capRightBonds {n : ℕ} {b : RawBond} :
    b ∈ capRightBonds n ↔ (⟨5 * n - 5, 6 * n + 1, ParsedBondKind.single⟩ : RawBond) = b := by
  simp [capRightBonds, eq_comm]

theorem mem_familyBonds {n : ℕ} {b : RawBond} :
    b ∈ familyBonds n ↔
      (∃ j, j < n - 1 ∧ (⟨5 * j, 5 * j + 5, ParsedBondKind.single⟩ : RawBond) = b) ∨
      (∃ i, i < n ∧ (⟨5 * i, 5 * i + 1, ParsedBondKind.single⟩ : RawBond) = b) ∨
      (∃ i, i < n ∧ (⟨5 * i + 1, 5 * i + 2, ParsedBondKind.single⟩ : RawBond) = b) ∨
      (∃ i, i < n ∧ (⟨5 * i + 1, 5 * i + 3, ParsedBondKind.single⟩ : RawBond) = b) ∨
      (∃ i, i < n ∧ (⟨5 * i + 1, 5 * i + 4, ParsedBondKind.single⟩ : RawBond) = b) ∨
      (∃ i, i < n ∧ (⟨5 * i, 5 * n + i, ParsedBondKind.single⟩ : RawBond) = b) ∨
      ((⟨0, 6 * n, ParsedBondKind.single⟩ : RawBond) = b) ∨
      ((⟨5 * n - 5, 6 * n + 1, ParsedBondKind.single⟩ : RawBond) = b) := by
  simp only [familyBonds, List.mem_append, mem_chainBonds, mem_pendantBonds, mem_terminalHBonds,
    mem_terminalFBonds, mem_terminalBrBonds, mem_linkBonds, mem_capLeftBonds, mem_capRightBonds,
    or_assoc]

/-! ## Counts, kinds, bounds, well-formedness -/

theorem familyBonds_length (n : ℕ) (hn : 1 ≤ n) : (familyBonds n).length = 6 * n + 1 := by
  simp only [familyBonds, List.length_append, chainBonds, pendantBonds, terminalHBonds,
    terminalFBonds, terminalBrBonds, linkBonds, capLeftBonds, capRightBonds,
    List.length_map, List.length_range, List.length_cons, List.length_nil]
  omega

theorem familyBonds_kind_single (n : ℕ) :
    ∀ b ∈ familyBonds n, b.kind = ParsedBondKind.single := by
  intro b hb
  rw [mem_familyBonds] at hb
  rcases hb with ⟨j, hj, hb⟩ | ⟨i, hi, hb⟩ | ⟨i, hi, hb⟩ | ⟨i, hi, hb⟩ | ⟨i, hi, hb⟩
    | ⟨i, hi, hb⟩ | hb | hb
  all_goals rw [← hb]

theorem familyBonds_bounds (n : ℕ) :
    ∀ b ∈ familyBonds n, b.source < 6 * n + 2 ∧ b.target < 6 * n + 2 := by
  intro b hb
  rw [mem_familyBonds] at hb
  rcases hb with ⟨j, hj, hb⟩ | ⟨i, hi, hb⟩ | ⟨i, hi, hb⟩ | ⟨i, hi, hb⟩ | ⟨i, hi, hb⟩
    | ⟨i, hi, hb⟩ | hb | hb
  all_goals (rw [← hb]; dsimp only; omega)

theorem familyBonds_source_lt_target (n : ℕ) (hn : 1 ≤ n) :
    ∀ b ∈ familyBonds n, b.source < b.target := by
  intro b hb
  rw [mem_familyBonds] at hb
  rcases hb with ⟨j, hj, hb⟩ | ⟨i, hi, hb⟩ | ⟨i, hi, hb⟩ | ⟨i, hi, hb⟩ | ⟨i, hi, hb⟩
    | ⟨i, hi, hb⟩ | hb | hb
  all_goals (rw [← hb]; dsimp only; omega)

theorem familyBonds_wellFormed (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    (hn : 1 ≤ n) : (rawFamily n parity).WellFormed := by
  intro b hb
  have retained : b ∈ familyBonds n := hb
  obtain ⟨h1, h2⟩ := familyBonds_bounds n b retained
  unfold RawMolecule.BondEndpointsOK
  rw [rawFamily_atomCount]
  exact ⟨h1, h2, Nat.ne_of_lt (familyBonds_source_lt_target n hn b retained)⟩

/-! ## Unordered-bond uniqueness -/

theorem range_map_nodup {α : Type*} {f : ℕ → α} {k : ℕ}
    (hinj : ∀ a b, a < k → b < k → f a = f b → a = b) :
    ((List.range k).map f).Nodup :=
  (List.nodup_map_iff_inj_on List.nodup_range).mpr
    (fun a ha b hb h => hinj a b (List.mem_range.mp ha) (List.mem_range.mp hb) h)

theorem disjoint_append_left {α : Type*} {l₁ l₂ l₃ : List α}
    (h₁ : l₁.Disjoint l₃) (h₂ : l₂.Disjoint l₃) : (l₁ ++ l₂).Disjoint l₃ := by
  rw [List.disjoint_left] at h₁ h₂ ⊢
  intro a ha hc
  rw [List.mem_append] at ha
  rcases ha with ha | ha
  · exact h₁ ha hc
  · exact h₂ ha hc

theorem chainBonds_nodup (n : ℕ) : (chainBonds n).Nodup := by
  rw [chainBonds]
  exact range_map_nodup (fun a b _ _ h => by injection h with h1 h2 h3; omega)

theorem pendantBonds_nodup (n : ℕ) : (pendantBonds n).Nodup := by
  rw [pendantBonds]
  exact range_map_nodup (fun a b _ _ h => by injection h with h1 h2 h3; omega)

theorem terminalHBonds_nodup (n : ℕ) : (terminalHBonds n).Nodup := by
  rw [terminalHBonds]
  exact range_map_nodup (fun a b _ _ h => by injection h with h1 h2 h3; omega)

theorem terminalFBonds_nodup (n : ℕ) : (terminalFBonds n).Nodup := by
  rw [terminalFBonds]
  exact range_map_nodup (fun a b _ _ h => by injection h with h1 h2 h3; omega)

theorem terminalBrBonds_nodup (n : ℕ) : (terminalBrBonds n).Nodup := by
  rw [terminalBrBonds]
  exact range_map_nodup (fun a b _ _ h => by injection h with h1 h2 h3; omega)

theorem linkBonds_nodup (n : ℕ) : (linkBonds n).Nodup := by
  rw [linkBonds]
  exact range_map_nodup (fun a b _ _ h => by injection h with h1 h2 h3; omega)

theorem capLeftBonds_nodup (n : ℕ) : (capLeftBonds n).Nodup := by
  rw [capLeftBonds]; exact List.nodup_singleton _

theorem capRightBonds_nodup (n : ℕ) : (capRightBonds n).Nodup := by
  rw [capRightBonds]; exact List.nodup_singleton _

theorem disjoint_chain_pendant (n : ℕ) : (chainBonds n).Disjoint (pendantBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_chainBonds.mp leftMember with ⟨i, hi, rfl⟩
  rcases mem_pendantBonds.mp rightMember with ⟨j, hj, equality⟩
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_chain_termH (n : ℕ) : (chainBonds n).Disjoint (terminalHBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_chainBonds.mp leftMember with ⟨i, hi, rfl⟩
  rcases mem_terminalHBonds.mp rightMember with ⟨j, hj, equality⟩
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_chain_termF (n : ℕ) : (chainBonds n).Disjoint (terminalFBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_chainBonds.mp leftMember with ⟨i, hi, rfl⟩
  rcases mem_terminalFBonds.mp rightMember with ⟨j, hj, equality⟩
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_chain_termBr (n : ℕ) : (chainBonds n).Disjoint (terminalBrBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_chainBonds.mp leftMember with ⟨i, hi, rfl⟩
  rcases mem_terminalBrBonds.mp rightMember with ⟨j, hj, equality⟩
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_chain_link (n : ℕ) : (chainBonds n).Disjoint (linkBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_chainBonds.mp leftMember with ⟨i, hi, rfl⟩
  rcases mem_linkBonds.mp rightMember with ⟨j, hj, equality⟩
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_chain_capLeft (n : ℕ) : (chainBonds n).Disjoint (capLeftBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_chainBonds.mp leftMember with ⟨i, hi, rfl⟩
  have equality := mem_capLeftBonds.mp rightMember
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_chain_capRight (n : ℕ) : (chainBonds n).Disjoint (capRightBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_chainBonds.mp leftMember with ⟨i, hi, rfl⟩
  have equality := mem_capRightBonds.mp rightMember
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_pendant_termH (n : ℕ) : (pendantBonds n).Disjoint (terminalHBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_pendantBonds.mp leftMember with ⟨i, hi, rfl⟩
  rcases mem_terminalHBonds.mp rightMember with ⟨j, hj, equality⟩
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_pendant_termF (n : ℕ) : (pendantBonds n).Disjoint (terminalFBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_pendantBonds.mp leftMember with ⟨i, hi, rfl⟩
  rcases mem_terminalFBonds.mp rightMember with ⟨j, hj, equality⟩
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_pendant_termBr (n : ℕ) : (pendantBonds n).Disjoint (terminalBrBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_pendantBonds.mp leftMember with ⟨i, hi, rfl⟩
  rcases mem_terminalBrBonds.mp rightMember with ⟨j, hj, equality⟩
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_pendant_link (n : ℕ) : (pendantBonds n).Disjoint (linkBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_pendantBonds.mp leftMember with ⟨i, hi, rfl⟩
  rcases mem_linkBonds.mp rightMember with ⟨j, hj, equality⟩
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_pendant_capLeft (n : ℕ) : (pendantBonds n).Disjoint (capLeftBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_pendantBonds.mp leftMember with ⟨i, hi, rfl⟩
  have equality := mem_capLeftBonds.mp rightMember
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_pendant_capRight (n : ℕ) : (pendantBonds n).Disjoint (capRightBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_pendantBonds.mp leftMember with ⟨i, hi, rfl⟩
  have equality := mem_capRightBonds.mp rightMember
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_termH_termF (n : ℕ) : (terminalHBonds n).Disjoint (terminalFBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_terminalHBonds.mp leftMember with ⟨i, hi, rfl⟩
  rcases mem_terminalFBonds.mp rightMember with ⟨j, hj, equality⟩
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_termH_termBr (n : ℕ) : (terminalHBonds n).Disjoint (terminalBrBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_terminalHBonds.mp leftMember with ⟨i, hi, rfl⟩
  rcases mem_terminalBrBonds.mp rightMember with ⟨j, hj, equality⟩
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_termH_link (n : ℕ) : (terminalHBonds n).Disjoint (linkBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_terminalHBonds.mp leftMember with ⟨i, hi, rfl⟩
  rcases mem_linkBonds.mp rightMember with ⟨j, hj, equality⟩
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_termH_capLeft (n : ℕ) : (terminalHBonds n).Disjoint (capLeftBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_terminalHBonds.mp leftMember with ⟨i, hi, rfl⟩
  have equality := mem_capLeftBonds.mp rightMember
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_termH_capRight (n : ℕ) : (terminalHBonds n).Disjoint (capRightBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_terminalHBonds.mp leftMember with ⟨i, hi, rfl⟩
  have equality := mem_capRightBonds.mp rightMember
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_termF_termBr (n : ℕ) : (terminalFBonds n).Disjoint (terminalBrBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_terminalFBonds.mp leftMember with ⟨i, hi, rfl⟩
  rcases mem_terminalBrBonds.mp rightMember with ⟨j, hj, equality⟩
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_termF_link (n : ℕ) : (terminalFBonds n).Disjoint (linkBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_terminalFBonds.mp leftMember with ⟨i, hi, rfl⟩
  rcases mem_linkBonds.mp rightMember with ⟨j, hj, equality⟩
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_termF_capLeft (n : ℕ) : (terminalFBonds n).Disjoint (capLeftBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_terminalFBonds.mp leftMember with ⟨i, hi, rfl⟩
  have equality := mem_capLeftBonds.mp rightMember
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_termF_capRight (n : ℕ) : (terminalFBonds n).Disjoint (capRightBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_terminalFBonds.mp leftMember with ⟨i, hi, rfl⟩
  have equality := mem_capRightBonds.mp rightMember
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_termBr_link (n : ℕ) : (terminalBrBonds n).Disjoint (linkBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_terminalBrBonds.mp leftMember with ⟨i, hi, rfl⟩
  rcases mem_linkBonds.mp rightMember with ⟨j, hj, equality⟩
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_termBr_capLeft (n : ℕ) : (terminalBrBonds n).Disjoint (capLeftBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_terminalBrBonds.mp leftMember with ⟨i, hi, rfl⟩
  have equality := mem_capLeftBonds.mp rightMember
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_termBr_capRight (n : ℕ) : (terminalBrBonds n).Disjoint (capRightBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_terminalBrBonds.mp leftMember with ⟨i, hi, rfl⟩
  have equality := mem_capRightBonds.mp rightMember
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_link_capLeft (n : ℕ) : (linkBonds n).Disjoint (capLeftBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_linkBonds.mp leftMember with ⟨i, hi, rfl⟩
  have equality := mem_capLeftBonds.mp rightMember
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_link_capRight (n : ℕ) : (linkBonds n).Disjoint (capRightBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_linkBonds.mp leftMember with ⟨i, hi, rfl⟩
  have equality := mem_capRightBonds.mp rightMember
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem disjoint_capLeft_capRight (n : ℕ) : (capLeftBonds n).Disjoint (capRightBonds n) := by
  apply List.disjoint_left.mpr
  intro bond leftMember rightMember
  rcases mem_capLeftBonds.mp leftMember with rfl
  have equality := mem_capRightBonds.mp rightMember
  have sourceEquality := congrArg RawBond.source equality
  have targetEquality := congrArg RawBond.target equality
  simp only [] at sourceEquality targetEquality
  omega

theorem familyBonds_nodup (n : ℕ) : (familyBonds n).Nodup := by
  have h0 : (chainBonds n).Nodup := chainBonds_nodup n
  have h1 : (chainBonds n ++ pendantBonds n).Nodup :=
    List.nodup_append'.mpr ⟨h0, pendantBonds_nodup n, disjoint_chain_pendant n⟩
  have h2 : ((chainBonds n ++ pendantBonds n) ++ terminalHBonds n).Nodup :=
    List.nodup_append'.mpr ⟨h1, terminalHBonds_nodup n, disjoint_append_left (disjoint_chain_termH n) (disjoint_pendant_termH n)⟩
  have h3 : (((chainBonds n ++ pendantBonds n) ++ terminalHBonds n) ++ terminalFBonds n).Nodup :=
    List.nodup_append'.mpr ⟨h2, terminalFBonds_nodup n, disjoint_append_left (disjoint_append_left (disjoint_chain_termF n) (disjoint_pendant_termF n)) (disjoint_termH_termF n)⟩
  have h4 : ((((chainBonds n ++ pendantBonds n) ++ terminalHBonds n) ++ terminalFBonds n) ++ terminalBrBonds n).Nodup :=
    List.nodup_append'.mpr ⟨h3, terminalBrBonds_nodup n, disjoint_append_left (disjoint_append_left (disjoint_append_left (disjoint_chain_termBr n) (disjoint_pendant_termBr n)) (disjoint_termH_termBr n)) (disjoint_termF_termBr n)⟩
  have h5 : (((((chainBonds n ++ pendantBonds n) ++ terminalHBonds n) ++ terminalFBonds n) ++ terminalBrBonds n) ++ linkBonds n).Nodup :=
    List.nodup_append'.mpr ⟨h4, linkBonds_nodup n, disjoint_append_left (disjoint_append_left (disjoint_append_left (disjoint_append_left (disjoint_chain_link n) (disjoint_pendant_link n)) (disjoint_termH_link n)) (disjoint_termF_link n)) (disjoint_termBr_link n)⟩
  have h6 : ((((((chainBonds n ++ pendantBonds n) ++ terminalHBonds n) ++ terminalFBonds n) ++ terminalBrBonds n) ++ linkBonds n) ++ capLeftBonds n).Nodup :=
    List.nodup_append'.mpr ⟨h5, capLeftBonds_nodup n, disjoint_append_left (disjoint_append_left (disjoint_append_left (disjoint_append_left (disjoint_append_left (disjoint_chain_capLeft n) (disjoint_pendant_capLeft n)) (disjoint_termH_capLeft n)) (disjoint_termF_capLeft n)) (disjoint_termBr_capLeft n)) (disjoint_link_capLeft n)⟩
  have h7 : (((((((chainBonds n ++ pendantBonds n) ++ terminalHBonds n) ++ terminalFBonds n) ++ terminalBrBonds n) ++ linkBonds n) ++ capLeftBonds n) ++ capRightBonds n).Nodup :=
    List.nodup_append'.mpr ⟨h6, capRightBonds_nodup n, disjoint_append_left (disjoint_append_left (disjoint_append_left (disjoint_append_left (disjoint_append_left (disjoint_append_left (disjoint_chain_capRight n) (disjoint_pendant_capRight n)) (disjoint_termH_capRight n)) (disjoint_termF_capRight n)) (disjoint_termBr_capRight n)) (disjoint_link_capRight n)) (disjoint_capLeft_capRight n)⟩
  simpa only [familyBonds, List.append_assoc] using h7

theorem edgeKey_eq_of_lt {b : RawBond} (h : b.source < b.target) :
    b.edgeKey = (b.source, b.target) := by
  unfold RawBond.edgeKey
  rw [Nat.min_eq_left (Nat.le_of_lt h), Nat.max_eq_right (Nat.le_of_lt h)]

theorem eq_of_edgeKey_eq_of_lt {b₁ b₂ : RawBond}
    (h₁ : b₁.source < b₁.target) (h₂ : b₂.source < b₂.target)
    (k₁ : b₁.kind = ParsedBondKind.single) (k₂ : b₂.kind = ParsedBondKind.single)
    (hk : b₁.edgeKey = b₂.edgeKey) : b₁ = b₂ := by
  rw [edgeKey_eq_of_lt h₁, edgeKey_eq_of_lt h₂] at hk
  injection hk with hs ht
  cases b₁; cases b₂
  simp_all

theorem familyBonds_bondRecordsUnique (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    (hn : 1 ≤ n) : (rawFamily n parity).BondRecordsUnique := by
  change ((familyBonds n).map RawBond.edgeKey).Nodup
  apply (List.nodup_map_iff_inj_on (familyBonds_nodup n)).mpr
  intro a ha b hb hk
  exact eq_of_edgeKey_eq_of_lt (familyBonds_source_lt_target n hn a ha)
    (familyBonds_source_lt_target n hn b hb)
    (familyBonds_kind_single n a ha) (familyBonds_kind_single n b hb) hk

theorem rawFamily_admissible (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    (rawFamily n parity).Admissible :=
  ⟨familyBonds_wellFormed n parity hn, familyBonds_bondRecordsUnique n parity hn⟩

/-! ## Canonicalized-molecule admission -/

theorem family_admissible (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    (family n parity).Admissible :=
  (withExactWrittenNeighbors_admissible_iff _).mpr (rawFamily_admissible n parity hn)

theorem family_writtenNeighborExact (n : ℕ) (parity : ℕ → TetrahedralInputParity) :
    (family n parity).WrittenNeighborExact :=
  withExactWrittenNeighbors_writtenNeighborExact _

theorem family_stereochemicalAdmissible (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    (hn : 1 ≤ n) : (family n parity).StereochemicalAdmissible :=
  ⟨family_admissible n parity hn, family_writtenNeighborExact n parity⟩

/-! ## Zero further hydrogen demand and the expansion identity -/

theorem family_totalWrittenTable (n : ℕ) (parity : ℕ → TetrahedralInputParity) :
    (family n parity).neighborOrder.length = (family n parity).atomCount := by
  simp [family, withExactWrittenNeighbors, RawMolecule.atomCount]

theorem family_zeroHydrogenDemand (n : ℕ) (parity : ℕ → TetrahedralInputParity) :
    ZeroHydrogenDemand (family n parity) := by
  intro idx hidx
  have hlookup : (family n parity).atomAt? idx = some (atomAtIndex n parity idx) :=
    family_atomAt? n parity idx hidx
  have hcount : (atomAtIndex n parity idx).explicitHydrogens? = some 0 := by
    unfold atomAtIndex
    split
    · split <;> rfl
    · rfl
  simp only [RawMolecule.hydrogenCountAt, hlookup, hcount]

theorem family_expansion_identity (n : ℕ) (parity : ℕ → TetrahedralInputParity) :
    (family n parity).withExplicitHydrogens = family n parity :=
  structurally_fixed_expansion_identity _
    ⟨familyAtoms_inlineCounts n parity, family_writtenNeighborExact n parity,
      family_totalWrittenTable n parity⟩

/-! ## Actual Rule-2 mass availability -/

-- rule2Mass_carbon is re-exported from NativeFamilyRawSupport.


-- rule2Mass_hydrogen is re-exported from NativeFamilyRawSupport.


-- rule2Mass_fluorine is re-exported from NativeFamilyRawSupport.


-- rule2Mass_bromine is re-exported from NativeFamilyRawSupport.


theorem rule2Mass_atomAtIndex (n : ℕ) (parity : ℕ → TetrahedralInputParity) (idx : ℕ) :
    ∃ mass, RawMolecule.rule2MassPico? (atomAtIndex n parity idx).element
      (atomAtIndex n parity idx).isotope? = some mass := by
  unfold atomAtIndex
  split
  · split
    · simpa [backboneCarbon, AtomSpec.aliphatic] using rule2Mass_carbon
    · simpa [pendantCarbon, AtomSpec.aliphatic] using rule2Mass_carbon
    · simpa [terminalHydrogen, AtomSpec.aliphatic] using rule2Mass_hydrogen
    · simpa [terminalFluorine, AtomSpec.aliphatic] using rule2Mass_fluorine
    · simpa [terminalBromine, AtomSpec.aliphatic] using rule2Mass_bromine
  · simpa [terminalHydrogen, AtomSpec.aliphatic] using rule2Mass_hydrogen

theorem family_rule2MassesKnown (n : ℕ) (parity : ℕ → TetrahedralInputParity) :
    (family n parity).Rule2MassesKnown := by
  intro atom hmem
  rw [family_atoms] at hmem
  rcases List.mem_map.mp hmem with ⟨idx, _hidx, rfl⟩
  exact rule2Mass_atomAtIndex n parity idx

/-! ## Generic bond-order / written-neighbour infrastructure -/

-- order_pos is re-exported from NativeFamilyRawSupport.


-- directedConnects_true_iff is re-exported from NativeFamilyRawSupport.


theorem foldl_mono (bonds : List RawBond) (u v : ℕ) {a b : ℕ} (h : a ≤ b) :
    bonds.foldl (fun acc bond => if bond.directedConnects u v then max acc bond.kind.order else acc) a
      ≤ bonds.foldl (fun acc bond => if bond.directedConnects u v then max acc bond.kind.order else acc) b := by
  induction bonds generalizing a b with
  | nil => exact h
  | cons bond rest ih =>
      simp only [List.foldl_cons]
      apply ih
      by_cases hc : bond.directedConnects u v = true
      · simp only [if_pos hc]; exact max_le_max h le_rfl
      · simp only [if_neg hc]; exact h

-- le_foldl is re-exported from NativeFamilyRawSupport.


-- foldl_pos_of_mem is re-exported from NativeFamilyRawSupport.


-- exists_of_fold_pos is re-exported from NativeFamilyRawSupport.


-- directedBondOrder_pos_of_connect is re-exported from NativeFamilyRawSupport.


-- exists_connecting_of_directedBondOrder_pos is re-exported from NativeFamilyRawSupport.


/-- Written-neighbour fallback table (the actual `writtenNeighbors` projection when no order is
stored, which is the case for `rawFamily`). -/
def wnFilter (c : ℕ) : RawBond → Option ℕ :=
  fun b => if b.source = c then some b.target else if b.target = c then some b.source else none

theorem rawFamily_writtenNeighbors_fallback (n : ℕ) (parity : ℕ → TetrahedralInputParity) (c : ℕ) :
    (rawFamily n parity).writtenNeighbors c = (familyBonds n).filterMap (wnFilter c) := by
  unfold RawMolecule.writtenNeighbors wnFilter
  simp [rawFamily]

theorem mem_writtenNeighbors_iff (n : ℕ) (parity : ℕ → TetrahedralInputParity) {c l : ℕ} :
    l ∈ (rawFamily n parity).writtenNeighbors c ↔
      ∃ b ∈ familyBonds n, (b.source = c ∧ b.target = l) ∨ (b.source = l ∧ b.target = c) := by
  rw [rawFamily_writtenNeighbors_fallback, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, hobs⟩
    refine ⟨b, hb, ?_⟩
    unfold wnFilter at hobs
    by_cases h1 : b.source = c
    · left; exact ⟨h1, Option.some.inj (by simpa [h1] using hobs)⟩
    · by_cases h2 : b.target = c
      · right; exact ⟨Option.some.inj (by simpa [h1, h2] using hobs), h2⟩
      · simp [h1, h2] at hobs
  · rintro ⟨b, hb, h1 | h2⟩
    · refine ⟨b, hb, ?_⟩
      unfold wnFilter
      rw [if_pos h1.1]; exact congrArg some h1.2
    · refine ⟨b, hb, ?_⟩
      unfold wnFilter
      by_cases hc : b.source = c
      · rw [if_pos hc]
        exact congrArg some (h2.2.trans (h2.1.symm.trans hc).symm)
      · rw [if_neg hc, if_pos h2.2]; exact congrArg some h2.1

theorem mem_writtenNeighbors_of_bondOrder_pos (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    {c l : ℕ} (h : 0 < (rawFamily n parity).bondOrder c l) :
    l ∈ (rawFamily n parity).writtenNeighbors c := by
  rw [mem_writtenNeighbors_iff]
  unfold RawMolecule.bondOrder at h
  by_cases heq : c = l
  · rw [if_pos heq] at h; exact absurd h (lt_irrefl 0)
  · rw [if_neg heq] at h
    rcases (lt_max_iff.mp h) with hc | hc
    · obtain ⟨b, hb, hs, ht⟩ := exists_connecting_of_directedBondOrder_pos (rawFamily n parity) hc
      exact ⟨b, hb, Or.inl ⟨hs, ht⟩⟩
    · obtain ⟨b, hb, hs, ht⟩ := exists_connecting_of_directedBondOrder_pos (rawFamily n parity) hc
      exact ⟨b, hb, Or.inr ⟨hs, ht⟩⟩

theorem bondOrder_pos_of_mem_writtenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    (hn : 1 ≤ n) {c l : ℕ} (h : l ∈ (rawFamily n parity).writtenNeighbors c) :
    0 < (rawFamily n parity).bondOrder c l := by
  rw [mem_writtenNeighbors_iff] at h
  obtain ⟨b, hb, hconn⟩ := h
  have hwell : (rawFamily n parity).WellFormed := familyBonds_wellFormed n parity hn
  have hne : c ≠ l := by
    rcases hconn with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := (hwell b hb).2.2; omega
    · have := (hwell b hb).2.2; omega
  unfold RawMolecule.bondOrder
  rw [if_neg hne]
  rcases hconn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact lt_of_lt_of_le
      (directedBondOrder_pos_of_connect (rawFamily n parity) b hb h1 h2) (le_max_left _ _)
  · exact lt_of_lt_of_le
      (directedBondOrder_pos_of_connect (rawFamily n parity) b hb h1 h2) (le_max_right _ _)

/-- If a stored written row is duplicate-free, contains only real atoms, and is exactly the bonded
set, then the exact-written-neighbour canonicalization returns that same row. -/
theorem exactWrittenNeighbors_eq_of_writtenRow (mol : RawMolecule) (c : ℕ) (row : List ℕ)
    (hw : mol.writtenNeighbors c = row) (hnodup : row.Nodup)
    (hvalid : ∀ l ∈ row, l < mol.atomCount ∧ 0 < mol.bondOrder c l)
    (hcomplete : ∀ l, 0 < mol.bondOrder c l → l ∈ row) :
    mol.exactWrittenNeighbors c = row := by
  unfold RawMolecule.exactWrittenNeighbors
  rw [hw]
  have hfilter : row.filter (fun l => decide (l < mol.atomCount ∧ 0 < mol.bondOrder c l)) = row :=
    List.filter_eq_self.mpr (fun l hl => decide_eq_true (hvalid l hl))
  rw [hfilter, List.dedup_eq_self.mpr hnodup]
  have hmissing :
      ((List.range mol.atomCount).filter (fun l => decide (0 < mol.bondOrder c l))).filter
        (fun l => decide (l ∉ row)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro l hl
    have hpos : 0 < mol.bondOrder c l := of_decide_eq_true (List.mem_filter.mp hl).2
    have hmem : l ∈ row := hcomplete l hpos
    simp [hmem]
  change row ++ ((List.range mol.atomCount).filter
    (fun l => decide (0 < mol.bondOrder c l))).filter (fun l => decide (l ∉ row)) = row
  rw [hmissing, List.append_nil]

/-! ## Segment filterMaps of the written-neighbour projection -/

theorem filterMap_range_singleton (k i v : ℕ) :
    (List.range k).filterMap (fun j => if j = i then (some v : Option ℕ) else none) =
      if i < k then [v] else [] := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.filterMap_append, ih]
      by_cases hik : i < k
      · have different : k ≠ i := by omega
        have next : i < k + 1 := by omega
        simp [hik, different, next]
      · by_cases same : k = i
        · subst i
          simp
        · have next : ¬ i < k + 1 := by omega
          simp [hik, same, next]

theorem segment_none {k c : ℕ} (g : ℕ → RawBond)
    (h : ∀ j < k, (g j).source ≠ c ∧ (g j).target ≠ c) :
    ((List.range k).map g).filterMap (wnFilter c) = [] := by
  rw [List.filterMap_map]
  change (List.range k).filterMap (fun j => wnFilter c (g j)) = []
  exact List.filterMap_eq_nil_iff.mpr (fun j hj => by
    have hj' := List.mem_range.mp hj
    have := h j hj'
    unfold wnFilter
    rw [if_neg this.1, if_neg this.2])

theorem filterMap_congr_local {α β : Type*} {l : List α} {f g : α → Option β}
    (h : ∀ a ∈ l, f a = g a) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.filterMap_cons, List.filterMap_cons, h a (List.mem_cons_self),
        ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem wn_target_single {k i u v : ℕ} (hu : u ≤ 4) (hv : v ≤ 4) (huv : u ≠ v) (hi : i < k) :
    ((List.range k).map (fun j => (⟨5 * j + u, 5 * j + v, ParsedBondKind.single⟩ : RawBond))).filterMap
      (wnFilter (5 * i + v)) = [5 * i + u] := by
  rw [List.filterMap_map]
  change (List.range k).filterMap (fun j => wnFilter (5 * i + v)
    (⟨5 * j + u, 5 * j + v, ParsedBondKind.single⟩ : RawBond)) = [5 * i + u]
  rw [show (fun j => wnFilter (5 * i + v) (⟨5 * j + u, 5 * j + v, ParsedBondKind.single⟩ : RawBond))
      = (fun j => if j = i then (some (5 * i + u) : Option ℕ) else none) from by
        funext j
        unfold wnFilter
        dsimp only
        by_cases hj : j = i
        · subst j
          have unequal : 5 * i + u ≠ 5 * i + v := by omega
          simp only [if_neg unequal]
        · have source : 5 * j + u ≠ 5 * i + v := by omega
          have target : 5 * j + v ≠ 5 * i + v := by omega
          simp only [if_neg source, if_neg target, if_neg hj]]
  rw [filterMap_range_singleton, if_pos hi]

theorem wn_source_single {k i u v : ℕ} (hu : u ≤ 4) (hv : v ≤ 4) (huv : u ≠ v) (hi : i < k) :
    ((List.range k).map (fun j => (⟨5 * j + u, 5 * j + v, ParsedBondKind.single⟩ : RawBond))).filterMap
      (wnFilter (5 * i + u)) = [5 * i + v] := by
  have _ := huv
  rw [List.filterMap_map]
  change (List.range k).filterMap (fun j => wnFilter (5 * i + u)
    (⟨5 * j + u, 5 * j + v, ParsedBondKind.single⟩ : RawBond)) = [5 * i + v]
  rw [show (fun j => wnFilter (5 * i + u) (⟨5 * j + u, 5 * j + v, ParsedBondKind.single⟩ : RawBond))
      = (fun j => if j = i then (some (5 * i + v) : Option ℕ) else none) from by
        funext j
        unfold wnFilter
        dsimp only
        by_cases hj : j = i
        · subst j
          simp only [if_true]
        · have source : 5 * j + u ≠ 5 * i + u := by omega
          have target : 5 * j + v ≠ 5 * i + u := by omega
          simp only [if_neg source, if_neg target, if_neg hj]]
  rw [filterMap_range_singleton, if_pos hi]

private theorem wn_pendant_target {n i : ℕ} (hi : i < n) :
    ((List.range n).map (fun j => (⟨5 * j, 5 * j + 1, ParsedBondKind.single⟩ : RawBond))).filterMap
      (wnFilter (5 * i + 1)) = [5 * i] := by
  simpa only [Nat.add_zero] using
    (wn_target_single (k := n) (i := i) (u := 0) (v := 1)
      (by omega) (by omega) (by omega) hi)

theorem wn_link_single {n j0 : ℕ} (hj0 : j0 < n) :
    ((List.range n).map (fun j => (⟨5 * j, 5 * n + j, ParsedBondKind.single⟩ : RawBond))).filterMap
      (wnFilter (5 * n + j0)) = [5 * j0] := by
  rw [List.filterMap_map]
  change (List.range n).filterMap (fun j => wnFilter (5 * n + j0)
    (⟨5 * j, 5 * n + j, ParsedBondKind.single⟩ : RawBond)) = [5 * j0]
  rw [filterMap_congr_local (l := List.range n)
      (g := fun j => if j = j0 then (some (5 * j0) : Option ℕ) else none) ?_]
  · rw [filterMap_range_singleton, if_pos hj0]
  · intro j hj
    have hjn : j < n := List.mem_range.mp hj
    unfold wnFilter
    dsimp only
    by_cases hje : j = j0
    · subst j
      have source : 5 * j0 ≠ 5 * n + j0 := by omega
      simp only [if_neg source]
    · have source : 5 * j ≠ 5 * n + j0 := by omega
      have target : 5 * n + j ≠ 5 * n + j0 := by omega
      simp only [if_neg source, if_neg target, if_neg hje]

theorem capLeft_none (n c : ℕ) (h1 : (0 : ℕ) ≠ c) (h2 : 6 * n ≠ c) :
    (capLeftBonds n).filterMap (wnFilter c) = [] := by
  rw [capLeftBonds, List.filterMap_cons, List.filterMap_nil]
  unfold wnFilter
  rw [if_neg h1, if_neg h2]

theorem capRight_none (n c : ℕ) (h1 : 5 * n - 5 ≠ c) (h2 : 6 * n + 1 ≠ c) :
    (capRightBonds n).filterMap (wnFilter c) = [] := by
  rw [capRightBonds, List.filterMap_cons, List.filterMap_nil]
  unfold wnFilter
  rw [if_neg h1, if_neg h2]

theorem capLeft_single (n : ℕ) (hn : 1 ≤ n) :
    (capLeftBonds n).filterMap (wnFilter (6 * n)) = [0] := by
  rw [capLeftBonds, List.filterMap_cons, List.filterMap_nil]
  unfold wnFilter
  rw [if_neg (by omega : ¬ ((0 : ℕ) = 6 * n)), if_pos rfl]

theorem capRight_single (n : ℕ) (hn : 1 ≤ n) :
    (capRightBonds n).filterMap (wnFilter (6 * n + 1)) = [5 * n - 5] := by
  rw [capRightBonds, List.filterMap_cons, List.filterMap_nil]
  unfold wnFilter
  rw [if_neg (by omega : ¬ (5 * n - 5 = 6 * n + 1)), if_pos rfl]

/-! ## Exact written-neighbour rows for the distinguished roles -/

theorem tag_writtenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hn : 1 ≤ n) (hi : i < n) :
    (rawFamily n parity).writtenNeighbors (5 * i + 1) = [5 * i, 5 * i + 2, 5 * i + 3, 5 * i + 4] := by
  rw [rawFamily_writtenNeighbors_fallback]
  simp only [familyBonds, chainBonds, pendantBonds, terminalHBonds, terminalFBonds,
    terminalBrBonds, linkBonds, List.filterMap_append]
  rw [segment_none (fun j => (⟨5 * j, 5 * j + 5, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      wn_pendant_target hi,
      wn_source_single (k := n) (i := i) (u := 1) (v := 2) (by omega) (by omega) (by omega) hi,
      wn_source_single (k := n) (i := i) (u := 1) (v := 3) (by omega) (by omega) (by omega) hi,
      wn_source_single (k := n) (i := i) (u := 1) (v := 4) (by omega) (by omega) (by omega) hi,
      segment_none (fun j => (⟨5 * j, 5 * n + j, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      capLeft_none n (5 * i + 1) (by omega) (by omega),
      capRight_none n (5 * i + 1) (by omega) (by omega)]
  simp

theorem terminalH_writtenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hn : 1 ≤ n) (hi : i < n) :
    (rawFamily n parity).writtenNeighbors (5 * i + 2) = [5 * i + 1] := by
  rw [rawFamily_writtenNeighbors_fallback]
  simp only [familyBonds, chainBonds, pendantBonds, terminalHBonds, terminalFBonds,
    terminalBrBonds, linkBonds, List.filterMap_append]
  rw [segment_none (fun j => (⟨5 * j, 5 * j + 5, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j, 5 * j + 1, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      wn_target_single (k := n) (i := i) (u := 1) (v := 2) (by omega) (by omega) (by omega) hi,
      segment_none (fun j => (⟨5 * j + 1, 5 * j + 3, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j + 1, 5 * j + 4, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j, 5 * n + j, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      capLeft_none n (5 * i + 2) (by omega) (by omega),
      capRight_none n (5 * i + 2) (by omega) (by omega)]
  simp

theorem terminalF_writtenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hn : 1 ≤ n) (hi : i < n) :
    (rawFamily n parity).writtenNeighbors (5 * i + 3) = [5 * i + 1] := by
  rw [rawFamily_writtenNeighbors_fallback]
  simp only [familyBonds, chainBonds, pendantBonds, terminalHBonds, terminalFBonds,
    terminalBrBonds, linkBonds, List.filterMap_append]
  rw [segment_none (fun j => (⟨5 * j, 5 * j + 5, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j, 5 * j + 1, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j + 1, 5 * j + 2, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      wn_target_single (k := n) (i := i) (u := 1) (v := 3) (by omega) (by omega) (by omega) hi,
      segment_none (fun j => (⟨5 * j + 1, 5 * j + 4, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j, 5 * n + j, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      capLeft_none n (5 * i + 3) (by omega) (by omega),
      capRight_none n (5 * i + 3) (by omega) (by omega)]
  simp

theorem terminalBr_writtenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hn : 1 ≤ n) (hi : i < n) :
    (rawFamily n parity).writtenNeighbors (5 * i + 4) = [5 * i + 1] := by
  rw [rawFamily_writtenNeighbors_fallback]
  simp only [familyBonds, chainBonds, pendantBonds, terminalHBonds, terminalFBonds,
    terminalBrBonds, linkBonds, List.filterMap_append]
  rw [segment_none (fun j => (⟨5 * j, 5 * j + 5, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j, 5 * j + 1, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j + 1, 5 * j + 2, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j + 1, 5 * j + 3, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      wn_target_single (k := n) (i := i) (u := 1) (v := 4) (by omega) (by omega) (by omega) hi,
      segment_none (fun j => (⟨5 * j, 5 * n + j, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      capLeft_none n (5 * i + 4) (by omega) (by omega),
      capRight_none n (5 * i + 4) (by omega) (by omega)]
  simp

theorem linkH_writtenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (j : ℕ)
    (hn : 1 ≤ n) (hj : j < n) :
    (rawFamily n parity).writtenNeighbors (5 * n + j) = [5 * j] := by
  rw [rawFamily_writtenNeighbors_fallback]
  simp only [familyBonds, chainBonds, pendantBonds, terminalHBonds, terminalFBonds,
    terminalBrBonds, linkBonds, List.filterMap_append]
  rw [segment_none (fun j0 => (⟨5 * j0, 5 * j0 + 5, ParsedBondKind.single⟩ : RawBond))
        (by intro j0 hj0; constructor <;> dsimp only <;> omega),
      segment_none (fun j0 => (⟨5 * j0, 5 * j0 + 1, ParsedBondKind.single⟩ : RawBond))
        (by intro j0 hj0; constructor <;> dsimp only <;> omega),
      segment_none (fun j0 => (⟨5 * j0 + 1, 5 * j0 + 2, ParsedBondKind.single⟩ : RawBond))
        (by intro j0 hj0; constructor <;> dsimp only <;> omega),
      segment_none (fun j0 => (⟨5 * j0 + 1, 5 * j0 + 3, ParsedBondKind.single⟩ : RawBond))
        (by intro j0 hj0; constructor <;> dsimp only <;> omega),
      segment_none (fun j0 => (⟨5 * j0 + 1, 5 * j0 + 4, ParsedBondKind.single⟩ : RawBond))
        (by intro j0 hj0; constructor <;> dsimp only <;> omega),
      wn_link_single (n := n) (j0 := j) hj,
      capLeft_none n (5 * n + j) (by omega) (by omega),
      capRight_none n (5 * n + j) (by omega) (by omega)]
  simp

theorem capLeftH_writtenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    (rawFamily n parity).writtenNeighbors (6 * n) = [0] := by
  rw [rawFamily_writtenNeighbors_fallback]
  simp only [familyBonds, chainBonds, pendantBonds, terminalHBonds, terminalFBonds,
    terminalBrBonds, linkBonds, List.filterMap_append]
  rw [segment_none (fun j => (⟨5 * j, 5 * j + 5, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j, 5 * j + 1, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j + 1, 5 * j + 2, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j + 1, 5 * j + 3, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j + 1, 5 * j + 4, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j, 5 * n + j, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      capLeft_single n hn,
      capRight_none n (6 * n) (by omega) (by omega)]
  simp

theorem capRightH_writtenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    (rawFamily n parity).writtenNeighbors (6 * n + 1) = [5 * n - 5] := by
  rw [rawFamily_writtenNeighbors_fallback]
  simp only [familyBonds, chainBonds, pendantBonds, terminalHBonds, terminalFBonds,
    terminalBrBonds, linkBonds, List.filterMap_append]
  rw [segment_none (fun j => (⟨5 * j, 5 * j + 5, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j, 5 * j + 1, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j + 1, 5 * j + 2, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j + 1, 5 * j + 3, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j + 1, 5 * j + 4, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      segment_none (fun j => (⟨5 * j, 5 * n + j, ParsedBondKind.single⟩ : RawBond))
        (by intro j hj; constructor <;> dsimp only <;> omega),
      capLeft_none n (6 * n + 1) (by omega) (by omega),
      capRight_single n hn]
  simp

/-! ## Exact canonical rows for the distinguished roles -/

theorem tag_nodup (i : ℕ) : ([5 * i, 5 * i + 2, 5 * i + 3, 5 * i + 4] : List ℕ).Nodup := by
  have h : ([5 * i, 5 * i + 2, 5 * i + 3, 5 * i + 4] : List ℕ) =
      ([0, 2, 3, 4].map (fun o => 5 * i + o)) := by simp
  rw [h]
  exact List.Nodup.map (fun a b hab => Nat.add_left_cancel hab) (by decide)

theorem exactWrittenNeighbors_of_row (n : ℕ) (parity : ℕ → TetrahedralInputParity) (c : ℕ)
    (row : List ℕ) (hn : 1 ≤ n) (hw : (rawFamily n parity).writtenNeighbors c = row)
    (hnodup : row.Nodup) (hbound : ∀ l ∈ row, l < 6 * n + 2) :
    (rawFamily n parity).exactWrittenNeighbors c = row := by
  refine exactWrittenNeighbors_eq_of_writtenRow (rawFamily n parity) c row hw hnodup ?_ ?_
  · intro l hl
    refine ⟨?_, bondOrder_pos_of_mem_writtenNeighbors n parity hn (by rw [hw]; exact hl)⟩
    rw [rawFamily_atomCount]; exact hbound l hl
  · intro l hpos
    rw [← hw]
    exact mem_writtenNeighbors_of_bondOrder_pos n parity hpos

theorem tag_exactWrittenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hn : 1 ≤ n) (hi : i < n) :
    (rawFamily n parity).exactWrittenNeighbors (5 * i + 1) = [5 * i, 5 * i + 2, 5 * i + 3, 5 * i + 4] :=
  exactWrittenNeighbors_of_row n parity (5 * i + 1) _ hn (tag_writtenNeighbors n parity i hn hi)
    (tag_nodup i) (by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl <;> omega)

theorem terminalH_exactWrittenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hn : 1 ≤ n) (hi : i < n) :
    (rawFamily n parity).exactWrittenNeighbors (5 * i + 2) = [5 * i + 1] :=
  exactWrittenNeighbors_of_row n parity (5 * i + 2) _ hn (terminalH_writtenNeighbors n parity i hn hi)
    (List.nodup_singleton _) (by intro l hl; rw [List.mem_singleton] at hl; omega)

theorem terminalF_exactWrittenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hn : 1 ≤ n) (hi : i < n) :
    (rawFamily n parity).exactWrittenNeighbors (5 * i + 3) = [5 * i + 1] :=
  exactWrittenNeighbors_of_row n parity (5 * i + 3) _ hn (terminalF_writtenNeighbors n parity i hn hi)
    (List.nodup_singleton _) (by intro l hl; rw [List.mem_singleton] at hl; omega)

theorem terminalBr_exactWrittenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hn : 1 ≤ n) (hi : i < n) :
    (rawFamily n parity).exactWrittenNeighbors (5 * i + 4) = [5 * i + 1] :=
  exactWrittenNeighbors_of_row n parity (5 * i + 4) _ hn
    (terminalBr_writtenNeighbors n parity i hn hi)
    (List.nodup_singleton _) (by intro l hl; rw [List.mem_singleton] at hl; omega)

theorem linkH_exactWrittenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (j : ℕ)
    (hn : 1 ≤ n) (hj : j < n) :
    (rawFamily n parity).exactWrittenNeighbors (5 * n + j) = [5 * j] :=
  exactWrittenNeighbors_of_row n parity (5 * n + j) _ hn (linkH_writtenNeighbors n parity j hn hj)
    (List.nodup_singleton _) (by intro l hl; rw [List.mem_singleton] at hl; omega)

theorem capLeftH_exactWrittenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    (rawFamily n parity).exactWrittenNeighbors (6 * n) = [0] :=
  exactWrittenNeighbors_of_row n parity (6 * n) _ hn (capLeftH_writtenNeighbors n parity hn)
    (List.nodup_singleton _) (by intro l hl; rw [List.mem_singleton] at hl; omega)

theorem capRightH_exactWrittenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    (rawFamily n parity).exactWrittenNeighbors (6 * n + 1) = [5 * n - 5] :=
  exactWrittenNeighbors_of_row n parity (6 * n + 1) _ hn (capRightH_writtenNeighbors n parity hn)
    (List.nodup_singleton _) (by intro l hl; rw [List.mem_singleton] at hl; omega)

/-! ## The same rows on the canonicalized family -/

theorem family_tag_writtenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hn : 1 ≤ n) (hi : i < n) :
    (family n parity).writtenNeighbors (5 * i + 1) = [5 * i, 5 * i + 2, 5 * i + 3, 5 * i + 4] := by
  have hlt : 5 * i + 1 < (family n parity).atomCount := by rw [family_atomCount]; omega
  unfold family
  rw [withExactWrittenNeighbors_writtenNeighbors (rawFamily n parity) ⟨5 * i + 1, hlt⟩]
  exact tag_exactWrittenNeighbors n parity i hn hi

theorem family_terminalH_writtenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hn : 1 ≤ n) (hi : i < n) :
    (family n parity).writtenNeighbors (5 * i + 2) = [5 * i + 1] := by
  have hlt : 5 * i + 2 < (family n parity).atomCount := by rw [family_atomCount]; omega
  unfold family
  rw [withExactWrittenNeighbors_writtenNeighbors (rawFamily n parity) ⟨5 * i + 2, hlt⟩]
  exact terminalH_exactWrittenNeighbors n parity i hn hi

theorem family_terminalF_writtenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hn : 1 ≤ n) (hi : i < n) :
    (family n parity).writtenNeighbors (5 * i + 3) = [5 * i + 1] := by
  have hlt : 5 * i + 3 < (family n parity).atomCount := by rw [family_atomCount]; omega
  unfold family
  rw [withExactWrittenNeighbors_writtenNeighbors (rawFamily n parity) ⟨5 * i + 3, hlt⟩]
  exact terminalF_exactWrittenNeighbors n parity i hn hi

theorem family_terminalBr_writtenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hn : 1 ≤ n) (hi : i < n) :
    (family n parity).writtenNeighbors (5 * i + 4) = [5 * i + 1] := by
  have hlt : 5 * i + 4 < (family n parity).atomCount := by rw [family_atomCount]; omega
  unfold family
  rw [withExactWrittenNeighbors_writtenNeighbors (rawFamily n parity) ⟨5 * i + 4, hlt⟩]
  exact terminalBr_exactWrittenNeighbors n parity i hn hi

theorem family_linkH_writtenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (j : ℕ)
    (hn : 1 ≤ n) (hj : j < n) :
    (family n parity).writtenNeighbors (5 * n + j) = [5 * j] := by
  have hlt : 5 * n + j < (family n parity).atomCount := by rw [family_atomCount]; omega
  unfold family
  rw [withExactWrittenNeighbors_writtenNeighbors (rawFamily n parity) ⟨5 * n + j, hlt⟩]
  exact linkH_exactWrittenNeighbors n parity j hn hj

theorem family_capLeftH_writtenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    (family n parity).writtenNeighbors (6 * n) = [0] := by
  have hlt : 6 * n < (family n parity).atomCount := by rw [family_atomCount]; omega
  unfold family
  rw [withExactWrittenNeighbors_writtenNeighbors (rawFamily n parity) ⟨6 * n, hlt⟩]
  exact capLeftH_exactWrittenNeighbors n parity hn

theorem family_capRightH_writtenNeighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    (hn : 1 ≤ n) :
    (family n parity).writtenNeighbors (6 * n + 1) = [5 * n - 5] := by
  have hlt : 6 * n + 1 < (family n parity).atomCount := by rw [family_atomCount]; omega
  unfold family
  rw [withExactWrittenNeighbors_writtenNeighbors (rawFamily n parity) ⟨6 * n + 1, hlt⟩]
  exact capRightH_exactWrittenNeighbors n parity hn

/-! ## Pendant degree and first-Z ranks -/

theorem family_tag_degree (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hn : 1 ≤ n) (hi : i < n) :
    ((family n parity).writtenNeighbors (5 * i + 1)).length = 4 := by
  exact congrArg List.length (family_tag_writtenNeighbors n parity i hn hi)

theorem family_tag_ranks (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hn : 1 ≤ n) (hi : i < n) :
    ((family n parity).writtenNeighbors (5 * i + 1)).map (family n parity).atomZAt = [6, 1, 9, 35] := by
  rw [family_tag_writtenNeighbors n parity i hn hi]
  simp only [List.map_cons, List.map_nil]
  rw [family_atomZAt_backbone n parity i hi, family_atomZAt_terminalH n parity i hi,
    family_atomZAt_terminalF n parity i hi, family_atomZAt_terminalBr n parity i hi]

theorem family_tag_ranks_nodup (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ)
    (hn : 1 ≤ n) (hi : i < n) :
    (((family n parity).writtenNeighbors (5 * i + 1)).map (family n parity).atomZAt).Nodup := by
  rw [family_tag_ranks n parity i hn hi]; decide

/-- The positive-size restriction excludes a genuine raw self-bond at size zero. -/
theorem family_zero_not_well_formed (parity : ℕ → TetrahedralInputParity) :
    ¬ (family 0 parity).WellFormed := by
  intro well
  have member : (⟨0, 0, ParsedBondKind.single⟩ : RawBond) ∈ (family 0 parity).bonds := by
    simp [family_bonds, familyBonds, capLeftBonds]
  exact (well _ member).2.2 rfl

/-- The generated pendant indices are distinct for every family size. -/
theorem family_tag_indices_nodup (n : ℕ) :
    ((List.range n).map (fun i => 5 * i + 1)).Nodup :=
  range_map_nodup (fun a b _ _ equality => by omega)

/-! ## Independent physical intake, derived from the actual generated records -/

open TetraStereo.UniversalProof.NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery
open TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery
open TetraStereo.UniversalProof.FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
open TetraStereo.UniversalProof.ActualFamilyReportBridgeProofs.ActualFamilyReportBridge

/-- Stored written-table canonicalization leaves the incident record projection unchanged. -/
theorem family_record_neighbors (n : ℕ) (parity : ℕ → TetrahedralInputParity) (center : ℕ) :
    recordNeighbors (family n parity) center = (rawFamily n parity).writtenNeighbors center := by
  unfold recordNeighbors
  change (familyBonds n).filterMap (recordNeighbor? center) = _
  rw [rawFamily_writtenNeighbors_fallback]
  apply filterMap_congr_local
  intro bond retained
  simp [recordNeighbor?, wnFilter]

private theorem single_fold_le_one (bonds : List RawBond) (u v : ℕ) :
    ∀ (acc : ℕ), acc ≤ 1 → (∀ bond ∈ bonds, bond.kind = .single) →
    bonds.foldl (fun order bond =>
      if bond.directedConnects u v then max order bond.kind.order else order) acc ≤ 1 := by
  induction bonds with
  | nil => intro acc bound single; exact bound
  | cons bond bonds inductionHypothesis =>
      intro acc bound single
      simp only [List.foldl_cons]
      apply inductionHypothesis
      · have kind := single bond (List.mem_cons_self)
        rw [kind]
        split <;> simp_all [ParsedBondKind.order]
      · intro selected member
        exact single selected (List.mem_cons_of_mem bond member)

theorem family_bond_order_le_one (n : ℕ) (parity : ℕ → TetrahedralInputParity) (u v : ℕ) :
    (family n parity).bondOrder u v ≤ 1 := by
  by_cases same : u = v
  · simpa only [RawMolecule.bondOrder, if_pos same] using (Nat.zero_le (1 : ℕ))
  · simp only [RawMolecule.bondOrder, if_neg same]
    apply max_le
    · exact single_fold_le_one (familyBonds n) u v 0 (by omega) (familyBonds_kind_single n)
    · exact single_fold_le_one (familyBonds n) v u 0 (by omega) (familyBonds_kind_single n)

theorem family_incident_single (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n)
    (center other : ℕ) (member : other ∈ recordNeighbors (family n parity) center) :
    (family n parity).bondOrder center other = 1 := by
  rw [family_record_neighbors] at member
  have positive := bondOrder_pos_of_mem_writtenNeighbors n parity hn member
  have bound := family_bond_order_le_one n parity center other
  have same : (family n parity).bondOrder center other =
      (rawFamily n parity).bondOrder center other := rfl
  rw [← same] at positive
  exact Nat.le_antisymm bound (Nat.succ_le_of_lt positive)

theorem family_tag_carbon (n : ℕ) (parity : ℕ → TetrahedralInputParity) (i : ℕ) (hi : i < n) :
    (family n parity).atomZAt (5 * i + 1) = 6 := by
  unfold RawMolecule.atomZAt
  rw [family_tag_atomAt? n parity i hi]
  rfl

/-- Physical C(backbone)(H)(F)(Br) witness for each generated tag, from actual record rows. -/
def family_pendant_site (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n)
    (i : ℕ) (hi : i < n) : PendantSite (family n parity) (5 * i + 1) where
  backbone := 5 * i
  hydrogen := 5 * i + 2
  fluorine := 5 * i + 3
  bromine := 5 * i + 4
  bound := by rw [family_atomCount]; omega
  carbon := family_tag_carbon n parity i hi
  neighbors := by rw [family_record_neighbors, tag_writtenNeighbors n parity i hn hi]
  single := family_incident_single n parity hn (5 * i + 1)
  backboneCarbon := family_atomZAt_backbone n parity i hi
  hydrogenZ := family_atomZAt_terminalH n parity i hi
  fluorineZ := family_atomZAt_terminalF n parity i hi
  bromineZ := family_atomZAt_terminalBr n parity i hi
  hydrogenRow := by rw [family_record_neighbors, terminalH_writtenNeighbors n parity i hn hi]
  fluorineRow := by rw [family_record_neighbors, terminalF_writtenNeighbors n parity i hn hi]
  bromineRow := by rw [family_record_neighbors, terminalBr_writtenNeighbors n parity i hn hi]

/-- Every observed annotation, including arbitrary choices of its parity, is a generated pendant. -/
theorem family_all_tag_pendant_sites (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    (hn : 1 ≤ n) (index : ℕ) (spec : AtomSpec) (inputParity : TetrahedralInputParity)
    (observed : (family n parity).atomAt? index = some spec)
    (tagged : spec.tetrahedral? = some inputParity) :
    Nonempty (PendantSite (family n parity) index) ∧ spec.element = .C := by
  have bound : index < (family n parity).atomCount :=
    listGet?_eq_some_implies_lt _ _ _ observed
  have annotation : ((family n parity).atomAt? index).map AtomSpec.tetrahedral? =
      some (some inputParity) := by rw [observed, Option.map_some, tagged]
  obtain ⟨i, hi, indexEquality, parityEquality⟩ :=
    (family_tagged_iff n parity index bound inputParity).mp annotation
  subst index
  have specEquality : spec = pendantCarbon (parity i) :=
    Option.some.inj (observed.symm.trans (family_tag_atomAt? n parity i hi))
  refine ⟨⟨family_pendant_site n parity hn i hi⟩, ?_⟩
  rw [specEquality]
  rfl

theorem family_actual_tag_nonempty (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    ∃ index spec inputParity, (family n parity).atomAt? index = some spec ∧
      spec.tetrahedral? = some inputParity := by
  refine ⟨1, pendantCarbon (parity 0), parity 0, ?_, rfl⟩
  simpa using family_tag_atomAt? n parity 0 (by omega)

/-- An inhabited independent first-Z discovery intake for every positive size. -/
theorem family_first_z_domain (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    FirstZTagDomain (family n parity) :=
  domain_of_pendant_records (family n parity) (family_admissible n parity hn).1
    (family_writtenNeighborExact n parity) (family_zeroHydrogenDemand n parity)
    (family_all_tag_pendant_sites n parity hn) (family_actual_tag_nonempty n parity hn)

theorem family_known_elements (n : ℕ) (parity : ℕ → TetrahedralInputParity) :
    ∀ spec ∈ (family n parity).atoms, spec.element ≠ .wildcard := by
  intro spec member
  rw [family_atoms] at member
  rcases List.mem_map.mp member with ⟨index, bounded, rfl⟩
  unfold atomAtIndex
  split
  · split <;> simp [backboneCarbon, pendantCarbon, terminalHydrogen,
      terminalFluorine, terminalBromine, AtomSpec.aliphatic]
  · simp [terminalHydrogen, AtomSpec.aliphatic]

theorem family_ordinary_source_input (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    OrdinarySourceInput (family n parity) :=
  ⟨(family_admissible n parity hn).1, family_writtenNeighborExact n parity,
    family_known_elements n parity, familyBonds_kind_single n⟩

/-- Actual bond normalization is the identity because all constructed records are single. -/
theorem family_actual_normalized_parsed (n : ℕ) (parity : ℕ → TetrahedralInputParity) :
    (normalizeRawMolecule (family n parity)).parsed = family n parity :=
  normalize_single_identity (family n parity) (familyBonds_kind_single n)

def family_normalized_domain (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    FirstZTagDomain (normalizeRawMolecule (family n parity)).parsed := by
  rw [family_actual_normalized_parsed]
  exact family_first_z_domain n parity hn

def family_normalized_source_input (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    OrdinarySourceInput (normalizeRawMolecule (family n parity)).parsed := by
  rw [family_actual_normalized_parsed]
  exact family_ordinary_source_input n parity hn

theorem family_normalized_admissible (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    (normalizeRawMolecule (family n parity)).parsed.StereochemicalAdmissible := by
  rw [family_actual_normalized_parsed]
  exact family_stereochemicalAdmissible n parity hn

theorem family_normalized_masses (n : ℕ) (parity : ℕ → TetrahedralInputParity) :
    (normalizeRawMolecule (family n parity)).parsed.Rule2MassesKnown := by
  rw [family_actual_normalized_parsed]
  exact family_rule2MassesKnown n parity

/-- No domain assumptions beyond positive size and arbitrary parity: every required record,
normalization, admission and rank premise of the actual report is inhabited by the constructor. -/
theorem positive_family_pipeline_intake (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    (family n parity).atomCount = 6 * n + 2 ∧
    (family n parity).bonds.length = 6 * n + 1 ∧
    FirstZTagDomain (normalizeRawMolecule (family n parity)).parsed ∧
    OrdinarySourceInput (normalizeRawMolecule (family n parity)).parsed ∧
    (normalizeRawMolecule (family n parity)).parsed.StereochemicalAdmissible ∧
    (normalizeRawMolecule (family n parity)).parsed.Rule2MassesKnown :=
  ⟨family_atomCount n parity, familyBonds_length n hn,
    family_normalized_domain n parity hn, family_normalized_source_input n parity hn,
    family_normalized_admissible n parity hn, family_normalized_masses n parity⟩

/-- All four other ACTUAL analyzer segments are empty, from the generated single-bond records. -/
theorem positive_family_other_four_segments_nil (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    (hn : 1 ≤ n) :
    let branches := normalizedStereoAnalysisBranches (normalizeRawMolecule (family n parity))
    branches.ordinaryDoubleBond = [] ∧ branches.coupledDoubleBond = [] ∧
      branches.oddCumuleneDoubleBond = [] ∧ branches.extendedAxial = [] :=
  actual_other_four_segments_nil (family n parity) (family_normalized_domain n parity hn)
    (family_normalized_source_input n parity hn)



theorem positive_family_actual_report_and_source (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    (hn : 1 ≤ n) (carrierFuel : ℕ) :
    let result := normalizeRawMolecule (family n parity)
    let domain := family_normalized_domain n parity hn
    let input := family_normalized_source_input n parity hn
    let fuel := analysisFuel (materialized result)
    analyzeNormalized result = fullRows result fuel ∧
      ((analyzeNormalized result).filter fun assignment => assignment.outcome.assigned) = tagRows result fuel ∧
      (tagRows result fuel).map StereoAssignment.unit =
        (rawAnnotatedCenters result).map StereoUnit.tetrahedral ∧
      (∀ assignment ∈ analyzeNormalized result, assignment.outcome.assigned = false →
        assignment.outcome = .refused .notSpecified ∨ assignment.outcome = .refused .rankingUnresolved) ∧
      (∀ index spec inputParity (observed : result.parsed.atomAt? index = some spec)
        (tagged : spec.tetrahedral? = some inputParity),
        FirstZSourceDiscoveryAlignmentProofs.FirstZSourceDiscoveryAlignment.ownState result domain (familySource result)
          (familyAgreement result domain input) carrierFuel
          ((familySource result).aromaticCanonicalFinalOccurrence carrierFuel
            (tagCenter result domain input index spec inputParity observed tagged)) =
          some (.chiral (seedDescriptor result fuel index inputParity))) :=
  actual_normalized_report_and_own_source (family n parity)
    (family_normalized_domain n parity hn) (family_normalized_source_input n parity hn)
    (family_normalized_admissible n parity hn) (family_normalized_masses n parity) carrierFuel

end TetraStereo.UniversalProof.NativeFamilyRawSupportProofs.PositiveFamilyGeneratorRecovery
