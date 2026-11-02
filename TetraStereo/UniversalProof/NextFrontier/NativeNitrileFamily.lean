import TetraStereo.UniversalProof.PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule






def bracket (element : Element) (hydrogens : Nat := 0) : AtomSpec :=
  { element := element, explicitHydrogens? := some hydrogens }

def centerSpec (parity : TetrahedralInputParity) : AtomSpec :=
  { bracket .C 1 with tetrahedral? := some parity }

def prefixAtoms (parity : TetrahedralInputParity) : List AtomSpec :=
  [centerSpec parity, bracket .F, bracket .C, bracket .N, bracket .C 1, bracket .N 2]

def tailAtoms (n : Nat) : List AtomSpec :=
  List.replicate n (bracket .C 2) ++ [bracket .C 3]

def tailParent (offset : Nat) : Nat := if offset = 0 then 4 else offset + 5

def prefixBonds : List RawBond :=
  [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨2, 3, .triple⟩,
    ⟨0, 4, .single⟩, ⟨4, 5, .single⟩]

def tailBonds (n : Nat) : List RawBond :=
  (List.range (n + 1)).map fun offset => ⟨tailParent offset, offset + 6, .single⟩

def tailRows (n : Nat) : List (List Nat) :=
  (List.range (n + 1)).map fun offset =>
    [tailParent offset] ++ if offset < n then [offset + 7] else []

def introductionRows (n : Nat) : List (Option Nat) :=
  [none, some 0, some 0, some 2, some 0, some 4] ++
    (List.range (n + 1)).map (fun offset => some (tailParent offset))

/-- Independently specified heavy-atom constitution and written neighbor order. -/
def raw (parity : TetrahedralInputParity) (n : Nat) : RawMolecule :=
  { atoms := prefixAtoms parity ++ tailAtoms n
    bonds := prefixBonds ++ tailBonds n
    neighborOrder := [[1, 2, 4], [0], [0, 3], [2], [0, 5, 6], [4]] ++ tailRows n
    introductionPredecessors := introductionRows n }

def prefixChars : TetrahedralInputParity → List Char
  | .anticlockwise => "[C@H]([F])([C]#[N])[CH]([NH2])".toList
  | .clockwise => "[C@@H]([F])([C]#[N])[CH]([NH2])".toList

def tailChars : Nat → List Char
  | 0 => "[CH3]".toList
  | n + 1 => "[CH2]".toList ++ tailChars n

def smiles (parity : TetrahedralInputParity) (n : Nat) : String :=
  String.ofList (prefixChars parity ++ tailChars n)

/-- The expanded input is the actual production materializer, not a separately selected graph. -/
def expanded (parity : TetrahedralInputParity) (n : Nat) : RawMolecule :=
  (raw parity n).withExplicitHydrogens

@[simp] theorem raw_atomCount (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).atomCount = n + 7 := by
  simp [raw, atomCount, prefixAtoms, tailAtoms]

@[simp] theorem raw_bondCount (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).bonds.length = n + 6 := by
  simp [raw, prefixBonds, tailBonds]

@[simp] theorem raw_rowCount (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).neighborOrder.length = n + 7 := by
  simp [raw, tailRows]

theorem raw_center (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).atomAt? 0 = some (centerSpec parity) := rfl

theorem raw_fluorine (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).atomAt? 1 = some (bracket .F) := rfl

theorem raw_nitrile_carbon (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).atomAt? 2 = some (bracket .C) := rfl

theorem raw_nitrile_nitrogen (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).atomAt? 3 = some (bracket .N) := rfl

theorem raw_amino_carbon (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).atomAt? 4 = some (bracket .C 1) := rfl

theorem raw_amino_nitrogen (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).atomAt? 5 = some (bracket .N 2) := rfl

theorem raw_center_hydrogen (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).hydrogenCountAt 0 = 1 := rfl

theorem raw_nitrile_hydrogens (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).hydrogenCountAt 2 = 0 ∧
      (raw parity n).hydrogenCountAt 3 = 0 := ⟨rfl, rfl⟩

theorem tail_parent_lt (offset : Nat) : tailParent offset < offset + 6 := by
  unfold tailParent
  split <;> omega

theorem raw_wellFormed (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).WellFormed := by
  intro bond retained
  change bond ∈ prefixBonds ++ tailBonds n at retained
  rcases List.mem_append.mp retained with inPrefix | tail
  · simp only [prefixBonds, List.mem_cons, List.not_mem_nil, or_false] at inPrefix
    rcases inPrefix with rfl | rfl | rfl | rfl | rfl
    all_goals unfold BondEndpointsOK
    all_goals rw [raw_atomCount]
    all_goals simp only
    all_goals omega
  · obtain ⟨offset, member, rfl⟩ := List.mem_map.mp tail
    have bound := List.mem_range.mp member
    have earlier := tail_parent_lt offset
    unfold BondEndpointsOK
    rw [raw_atomCount]
    simp only
    omega

theorem raw_bond_kinds (parity : TetrahedralInputParity) (n : Nat)
    (bond : RawBond) (retained : bond ∈ (raw parity n).bonds) :
    bond.kind = .single ∨ bond.kind = .triple := by
  change bond ∈ prefixBonds ++ tailBonds n at retained
  rcases List.mem_append.mp retained with inPrefix | tail
  · simp only [prefixBonds, List.mem_cons, List.not_mem_nil, or_false] at inPrefix
    rcases inPrefix with rfl | rfl | rfl | rfl | rfl <;> simp
  · obtain ⟨offset, _, rfl⟩ := List.mem_map.mp tail
    exact Or.inl rfl

theorem raw_known_elements (parity : TetrahedralInputParity) (n : Nat)
    (spec : AtomSpec) (retained : spec ∈ (raw parity n).atoms) :
    spec.element ≠ .wildcard := by
  change spec ∈ prefixAtoms parity ++ tailAtoms n at retained
  rcases List.mem_append.mp retained with inPrefix | tail
  · simp only [prefixAtoms, List.mem_cons, List.not_mem_nil, or_false] at inPrefix
    rcases inPrefix with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [centerSpec, bracket]
  · rcases List.mem_append.mp tail with repeated | terminal
    · have same : spec = bracket .C 2 := (List.mem_replicate.mp repeated).2
      subst spec
      decide
    · have same := List.mem_singleton.mp terminal
      subst spec
      decide

theorem raw_triple_present (parity : TetrahedralInputParity) (n : Nat) :
    ({ source := 2, target := 3, kind := .triple } : RawBond) ∈ (raw parity n).bonds := by
  simp [raw, prefixBonds]

theorem family_unbounded (parity : TetrahedralInputParity) (bound : Nat) :
    bound < (raw parity bound).atomCount := by
  rw [raw_atomCount]
  omega

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
