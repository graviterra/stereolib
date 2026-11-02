import TetraStereo.UniversalProof.NextFrontier.NativeNitrileLocalExpansion
import TetraStereo.UniversalProof.NextFrontier.NativeNitrilePhysicalAdmission
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileDuplicateProvenance
import TetraStereo.OneCenter.ProductionCIPExactExpansion

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.PositiveHydrogenBondTransportProofs.PositiveHydrogenBondTransport

private def incidentAt (index : Nat) (bond : RawBond) : Bool :=
  bond.source == index || bond.target == index

private theorem raw_nitrile_incident (parity : TetrahedralInputParity) (n : Nat)
    (bond : RawBond) :
    bond ∈ (raw parity n).bonds ∧ incidentAt 2 bond = true ↔
      bond = ⟨0, 2, .single⟩ ∨ bond = ⟨2, 3, .triple⟩ := by
  constructor
  · rintro ⟨retained, incident⟩
    change bond ∈ prefixBonds ++ tailBonds n at retained
    rcases List.mem_append.mp retained with inPrefix | inTail
    · simp only [prefixBonds, List.mem_cons, List.not_mem_nil, or_false] at inPrefix
      rcases inPrefix with rfl | rfl | rfl | rfl | rfl <;>
        simp_all [incidentAt]
    · obtain ⟨offset, _, rfl⟩ := List.mem_map.mp inTail
      simp only [incidentAt, Bool.or_eq_true, beq_iff_eq] at incident
      by_cases root : offset = 0
      · simp [tailParent, root] at incident
      · rw [tailParent, if_neg root] at incident
        omega
  · rintro (rfl | rfl) <;> simp [raw, prefixBonds, incidentAt]

theorem expanded_nitrile_incident_records (parity : TetrahedralInputParity) (n : Nat) :
    (((expanded parity n).bonds).filter (incidentAt 2)).Perm
      [⟨0, 2, .single⟩, ⟨2, 3, .triple⟩] := by
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact (List.Nodup.of_map RawBond.edgeKey (expanded_admissible parity n).2).filter _
  · decide
  · apply Finset.ext
    intro bond
    simp only [List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false]
    by_cases incident : incidentAt 2 bond = true
    · have physical : bond.source = 2 ∨ bond.target = 2 := by
        simpa only [incidentAt, Bool.or_eq_true, beq_iff_eq] using incident
      rw [expanded_zero_demand_incident parity n 2 (by omega)
        (raw_nitrile_hydrogens parity n).1 bond physical]
      exact raw_nitrile_incident parity n bond
    · constructor
      · exact fun present => False.elim (incident present.2)
      · rintro (rfl | rfl) <;> simp [incidentAt] at incident

private def copySeeds (mol : RawMolecule) (node : CanonicalBranchNode) (bond : RawBond) :
    List (Nat × Nat) :=
  let next? :=
    if bond.source == node.atom then some bond.target
    else if bond.target == node.atom then some bond.source else none
  match next? with
  | none => []
  | some next => (List.range (mol.canonicalBondOrder node next)).map fun copy => (next, copy)

private theorem copySeeds_incident_filter (mol : RawMolecule) (node : CanonicalBranchNode)
    (bonds : List RawBond) :
    (bonds.filter (incidentAt node.atom)).flatMap (copySeeds mol node) =
      bonds.flatMap (copySeeds mol node) := by
  induction bonds with
  | nil => rfl
  | cons head tail ih =>
      by_cases source : head.source = node.atom
      · simp [incidentAt, source, ih]
      · by_cases target : head.target = node.atom
        · simp [incidentAt, target, ih]
        · simp [incidentAt, source, target, copySeeds, ih]

theorem expanded_nitrile_bond_orders (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).bondOrder 2 0 = 1 ∧ (expanded parity n).bondOrder 2 3 = 3 := by
  have admitted := expanded_admissible parity n
  constructor
  · exact bondOrder_eq_kind_of_mem_connects _ admitted.1 admitted.2
      (withExplicitHydrogens_retains_original_bonds (raw parity n) ⟨0, 2, .single⟩
        (by simp [raw, prefixBonds])) (by decide)
  · exact bondOrder_eq_kind_of_mem_connects _ admitted.1 admitted.2
      (withExplicitHydrogens_retains_original_bonds (raw parity n) ⟨2, 3, .triple⟩
        (raw_triple_present parity n)) (by decide)

theorem expanded_nitrile_canonical_orders (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).canonicalBondOrder (canonicalRoot 0 2) 0 = 1 ∧
      (expanded parity n).canonicalBondOrder (canonicalRoot 0 2) 3 = 3 := by
  have root := expanded_original_atom parity n 0 (centerSpec parity) (raw_center parity n)
  have carbon := expanded_original_atom parity n 2 (bracket .C) (raw_nitrile_carbon parity n)
  have orders := expanded_nitrile_bond_orders parity n
  simp [canonicalBondOrder, canonicalRoot, isTrigonalPyramidalOxidoRootEdge,
    root, carbon, materializedAtomSpec, centerSpec, bracket, orders.1, orders.2]

/-- The actual occurrence constructor produces exactly one real N and two duplicate N copies,
up to bond-list order. The duplicate provenance is assigned by `canonicalChildren` itself. -/
theorem expanded_nitrile_child_copies (parity : TetrahedralInputParity) (n : Nat) :
    ((expanded parity n).canonicalChildCopies (canonicalRoot 0 2)).Perm
      [(3, 0), (3, 1), (3, 2)] := by
  have seeds := (expanded_nitrile_incident_records parity n).flatMap_right
    (copySeeds (expanded parity n) (canonicalRoot 0 2))
  have filtered := copySeeds_incident_filter (expanded parity n) (canonicalRoot 0 2)
    (expanded parity n).bonds
  change ((expanded parity n).bonds.filter (incidentAt 2)).flatMap
    (copySeeds (expanded parity n) (canonicalRoot 0 2)) = _ at filtered
  rw [filtered] at seeds
  have erased := seeds.erase (0, 0)
  have orders := expanded_nitrile_canonical_orders parity n
  have parentSeeds : copySeeds (expanded parity n) (canonicalRoot 0 2)
      ⟨0, 2, .single⟩ = [(0, 0)] := by
    change (List.range ((expanded parity n).canonicalBondOrder (canonicalRoot 0 2) 0)).map
      (fun copy => (0, copy)) = _
    rw [orders.1]
    rfl
  have nitrogenSeeds : copySeeds (expanded parity n) (canonicalRoot 0 2)
      ⟨2, 3, .triple⟩ = [(3, 0), (3, 1), (3, 2)] := by
    change (List.range ((expanded parity n).canonicalBondOrder (canonicalRoot 0 2) 3)).map
      (fun copy => (3, copy)) = _
    rw [orders.2]
    rfl
  change (eraseCanonicalParentCopy 0 ((expanded parity n).bonds.flatMap
    (copySeeds (expanded parity n) (canonicalRoot 0 2)))).Perm _
  rw [eraseCanonicalParentCopy_eq_erase]
  simpa only [List.flatMap_cons, List.flatMap_nil, parentSeeds, nitrogenSeeds,
    List.append_nil, List.cons_append, List.nil_append, List.erase_cons_head] using erased

def realNitrileNitrogen : CanonicalBranchNode :=
  { atom := 3, parent := 2, history := [3, 2, 0], provenance := .realAtom }

theorem expanded_nitrile_children (parity : TetrahedralInputParity) (n : Nat) :
    ((expanded parity n).canonicalChildren (canonicalRoot 0 2)).Perm
      [realNitrileNitrogen, nitrileDuplicate, nitrileDuplicate] := by
  have mapped := (expanded_nitrile_child_copies parity n).map
    (fun copy : Nat × Nat =>
      ({ atom := copy.1, parent := 2, history := [copy.1, 2, 0],
         provenance := if copy.2 != 0 then .multipleBondDuplicate 1
           else if ([2, 0] : List Nat).contains copy.1 then
             .ringDuplicate (canonicalHistoryDistance (canonicalRoot 0 2) copy.1)
           else .realAtom } : CanonicalBranchNode))
  simpa [canonicalChildren, canonicalRoot, CanonicalBranchNode.forcedLeaf,
    CanonicalBranchNode.depth, realNitrileNitrogen, nitrileDuplicate] using mapped

theorem expanded_nitrile_child_atom_ids (parity : TetrahedralInputParity) (n : Nat) :
    ((expanded parity n).canonicalChildren (canonicalRoot 0 2)).map CanonicalBranchNode.atom =
      [3, 3, 3] := by
  have same := (expanded_nitrile_children parity n).map CanonicalBranchNode.atom
  apply (List.perm_replicate (n := 3) (a := 3)).mp
  simpa [realNitrileNitrogen, nitrileDuplicate] using same

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
