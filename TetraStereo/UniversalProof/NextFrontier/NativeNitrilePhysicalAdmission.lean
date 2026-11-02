import TetraStereo.UniversalProof.NextFrontier.NativeNitrileHydrogenAtoms
import TetraStereo.UniversalProof.PositiveHydrogenBondTransportProofs.PositiveHydrogenBondTransport

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.PositiveHydrogenBondTransportProofs.PositiveHydrogenBondTransport

/-! Physical graph admission is independent of semantic source conversion. Keeping this layer
separate allows parser and checked-intake gates to use only their physical dependencies. -/

private theorem physical_listGet_eq_getElem {Alpha : Type} (values : List Alpha) (index : Nat) :
    listGet? values index = values[index]? := by
  induction values generalizing index with
  | nil => cases index <;> rfl
  | cons head tail ih =>
      cases index with
      | zero => rfl
      | succ index => exact ih index

theorem raw_bonds_chronological (parity : TetrahedralInputParity) (n : Nat)
    (bond : RawBond) (retained : bond ∈ (raw parity n).bonds) :
    bond.source < bond.target := by
  change bond ∈ prefixBonds ++ tailBonds n at retained
  rcases List.mem_append.mp retained with inPrefix | tail
  · simp only [prefixBonds, List.mem_cons, List.not_mem_nil, or_false] at inPrefix
    rcases inPrefix with rfl | rfl | rfl | rfl | rfl <;> decide
  · obtain ⟨offset, _, rfl⟩ := List.mem_map.mp tail
    exact tail_parent_lt offset

private theorem raw_targets_nodup (parity : TetrahedralInputParity) (n : Nat) :
    ((raw parity n).bonds.map RawBond.target).Nodup := by
  change ((prefixBonds ++ tailBonds n).map RawBond.target).Nodup
  rw [List.map_append, List.nodup_append]
  refine ⟨by decide, ?_, ?_⟩
  · simp only [tailBonds, List.map_map]
    change ((List.range (n + 1)).map (fun offset => offset + 6)).Nodup
    exact (List.nodup_range (n := n + 1)).map (fun _ _ equal => by omega)
  · intro left leftMember right rightMember equal
    have small : left ≤ 5 := by
      simp only [prefixBonds, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at leftMember
      rcases leftMember with rfl | rfl | rfl | rfl | rfl <;> omega
    obtain ⟨bond, member, rfl⟩ := List.mem_map.mp rightMember
    obtain ⟨offset, _, rfl⟩ := List.mem_map.mp member
    change left = offset + 6 at equal
    omega

theorem raw_bonds_unique (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).BondRecordsUnique := by
  apply List.Nodup.of_map Prod.snd
  have equal : (((raw parity n).bonds.map RawBond.edgeKey).map Prod.snd) =
      (raw parity n).bonds.map RawBond.target := by
    rw [List.map_map]
    apply List.map_congr_left
    intro bond retained
    exact Nat.max_eq_right (Nat.le_of_lt (raw_bonds_chronological parity n bond retained))
  rw [equal]
  exact raw_targets_nodup parity n

theorem raw_admissible (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).Admissible :=
  ⟨raw_wellFormed parity n, raw_bonds_unique parity n⟩

/-- Expansion's edge-admission proof only needs the source edge contract. A possibly incomplete
source written table is repaired by the actual final exact-neighbor canonicalizer. -/
theorem expansion_admissible_of_raw (mol : RawMolecule) (admitted : mol.Admissible) :
    mol.withExplicitHydrogens.Admissible := by
  have initial : (initialHydrogenExpansionState mol).toRawMolecule.Admissible := by
    constructor
    · intro bond retained
      have ends := admitted.1 bond retained
      simpa [BondEndpointsOK, initialHydrogenExpansionState,
        HydrogenExpansionState.toRawMolecule, atomCount] using ends
    · exact admitted.2
  unfold withExplicitHydrogens
  apply (withExactWrittenNeighbors_admissible_iff _).mpr
  exact fold_withExplicitHydrogensStep_preserves_admissible mol
    (List.range mol.atomCount) (initialHydrogenExpansionState mol)
    (by intro index member; exact List.mem_range.mp member)
    (initialHydrogenExpansionState_shapeInvariant mol) initial

theorem expanded_admissible (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).Admissible :=
  expansion_admissible_of_raw _ (raw_admissible parity n)

theorem expanded_written_exact (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).WrittenNeighborExact :=
  withExplicitHydrogens_writtenNeighborExact _

theorem expanded_stereochemical_admissible (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).StereochemicalAdmissible :=
  ⟨expanded_admissible parity n, expanded_written_exact parity n⟩

theorem expanded_bond_kinds (parity : TetrahedralInputParity) (n : Nat)
    (bond : RawBond) (retained : bond ∈ (expanded parity n).bonds) :
    bond.kind = .single ∨ bond.kind = .triple := by
  by_cases original : bond ∈ (raw parity n).bonds
  · exact raw_bond_kinds parity n bond original
  · exact Or.inl (withExplicitHydrogens_generated_bond_shape (raw parity n) retained original).2.2.2.2

theorem expanded_known_elements (parity : TetrahedralInputParity) (n : Nat)
    (spec : AtomSpec) (retained : spec ∈ (expanded parity n).atoms) :
    spec.element ≠ .wildcard := by
  obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp retained
  have observed : (expanded parity n).atomAt? index = some spec := by
    exact (physical_listGet_eq_getElem _ _).trans lookup
  by_cases old : index < (raw parity n).atomCount
  · obtain ⟨original, sourceLookup⟩ := listGet?_exists_of_lt (raw parity n).atoms index old
    have source : (raw parity n).atomAt? index = some original := sourceLookup
    have same := Option.some.inj
      ((expanded_original_atom parity n index original source).symm.trans observed)
    subst spec
    exact raw_known_elements parity n original
      (listGet?_eq_some_implies_mem _ _ _ sourceLookup)
  · have same := (expanded_fresh_hydrogen parity n index spec
      (by rw [raw_atomCount] at old; omega) observed).1
    subst spec
    decide

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
