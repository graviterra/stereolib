import TetraStereo.OneCenter.ExplicitHydrogens

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingDomain

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule

def carbon (hydrogens : Nat) : AtomSpec :=
  { AtomSpec.aliphatic .C with explicitHydrogens? := some hydrogens }

def taggedCarbon (parity : TetrahedralInputParity) : AtomSpec :=
  { carbon 1 with tetrahedral? := some parity }

def chainBond (j : Nat) : RawBond :=
  ⟨if j = 0 then 2 else j + 3, j + 4, .single⟩

def chainRow (n j : Nat) : List Nat :=
  [if j = 0 then 2 else j + 3, if j < n then j + 5 else 0]

/-- The predecessor is fixed by atom introduction, never by the later ring-closing edge. -/
def ringPredecessors (n : Nat) : List (Option Nat) :=
  [none, some 0, some 0, some 2] ++
    (List.range (n + 1)).map (fun j => some (if j = 0 then 2 else j + 3))

/-- Independent physical record; no parser result is a construction premise. -/
def ringRaw (n : Nat) (parity : TetrahedralInputParity) : RawMolecule :=
  { atoms := [taggedCarbon parity,
      { AtomSpec.aliphatic .F with explicitHydrogens? := some 0 }, carbon 1,
      { AtomSpec.aliphatic .Cl with explicitHydrogens? := some 0 }] ++
      List.replicate (n + 1) (carbon 2)
    bonds := [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨2, 3, .single⟩] ++
      (List.range (n + 1)).map chainBond ++ [⟨n + 4, 0, .single⟩]
    neighborOrder := [[1, 2, n + 4], [0], [0, 3, 4], [2]] ++
      (List.range (n + 1)).map (chainRow n)
    introductionPredecessors := ringPredecessors n }

def tagToken : TetrahedralInputParity → String
  | .anticlockwise => "[C@H]"
  | .clockwise => "[C@@H]"

def chainSyntax : Nat → String
  | 0 => ""
  | n + 1 => "[CH2]" ++ chainSyntax n

def ringSyntax (n : Nat) (parity : TetrahedralInputParity) : String :=
  tagToken parity ++ "([F])([CH]([Cl])" ++ chainSyntax (n + 1) ++ "1)1"

theorem atom_count (n : Nat) (parity : TetrahedralInputParity) :
    (ringRaw n parity).atomCount = n + 5 := by
  simp [ringRaw, atomCount]

theorem bond_count (n : Nat) (parity : TetrahedralInputParity) :
    (ringRaw n parity).bonds.length = n + 5 := by
  simp [ringRaw]

theorem row_count (n : Nat) (parity : TetrahedralInputParity) :
    (ringRaw n parity).neighborOrder.length = n + 5 := by
  simp [ringRaw]

theorem chain_endpoints (n j : Nat) (bound : j < n + 1) :
    (chainBond j).source < n + 5 ∧ (chainBond j).target < n + 5 := by
  simp only [chainBond]
  split <;> omega

theorem closure_endpoints (n : Nat) : n + 4 < n + 5 ∧ 0 < n + 5 := by
  omega

theorem root_written_row (n : Nat) (parity : TetrahedralInputParity) :
    (ringRaw n parity).neighborOrder.head? = some [1, 2, n + 4] := rfl

def expectedRootHydrogenRow (n : Nat) : List Nat := [n + 5, 1, 2, n + 4]

theorem first_atom_convention (n : Nat) :
    insertHydrogenInOrder [1, 2, n + 4] false [n + 5] =
      expectedRootHydrogenRow n := rfl

theorem expected_row_distinct (n : Nat) :
    (expectedRootHydrogenRow n).Nodup := by
  simp [expectedRootHydrogenRow]

/-- Actual introduction event, before any eventual ring-closing bond. -/
theorem root_introduced_without_bond (parity : TetrahedralInputParity) :
    (ParseState.addAtom {} (taggedCarbon parity)).bonds = [] := rfl

theorem root_introduced_without_predecessor (parity : TetrahedralInputParity) :
    ({} : ParseState).current? = none ∧
      (ParseState.addAtom {} (taggedCarbon parity)).bonds = [] := ⟨rfl, rfl⟩

def hydrogenInventory (n : Nat) : List Nat := [1, 0, 1, 0] ++ List.replicate (n + 1) 2

theorem hydrogen_inventory_actual_atoms (n : Nat) (parity : TetrahedralInputParity) :
    (ringRaw n parity).atoms.map AtomSpec.explicitHydrogens = hydrogenInventory n := by
  simp [ringRaw, hydrogenInventory, taggedCarbon, carbon, AtomSpec.explicitHydrogens]

def carbonIndices (n : Nat) : List Nat :=
  [0, 2] ++ (List.range (n + 1)).map (fun j => j + 4)

theorem carbon_role_count (n : Nat) : (carbonIndices n).length = n + 3 := by
  simp [carbonIndices]

private theorem sum_twos (k : Nat) : (List.replicate k 2).sum = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]; omega

theorem hydrogen_count (n : Nat) : (hydrogenInventory n).sum = 2 * n + 4 := by
  simp [hydrogenInventory]
  omega

/-- The smallest member is a three-carbon ring. -/
theorem zero_syntax : ringSyntax 0 .anticlockwise =
    "[C@H]([F])([CH]([Cl])[CH2]1)1" := rfl

inductive EmptyBranchMarker where
  | single | double | triple
  deriving DecidableEq

def markerToken : EmptyBranchMarker → String
  | .single => "-"
  | .double => "="
  | .triple => "#"

/-- Syntax language with an explicitly empty bond-marked branch, arbitrary prefix and suffix. -/
def malformedBranch (leading following : String) (marker : EmptyBranchMarker) : String :=
  leading ++ "(" ++ markerToken marker ++ ")" ++ following

def ConcreteRejection (input : String) : Prop :=
  (parseOpenSMILES input).isOk = false

/-- The independent physical family is inhabited for every natural ring extension. -/
theorem domain_inhabited : ∃ n parity, (ringRaw n parity).atomCount = n + 5 :=
  ⟨0, .anticlockwise, atom_count 0 .anticlockwise⟩

end TetraStereo.UniversalProof.NativeRingDomain
