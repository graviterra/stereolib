import TetraStereo.UniversalProof.NextFrontier.NativeNitrileOrderedChildren
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileAtomicLabels

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule

private theorem raw_nitrogen_incident (parity : TetrahedralInputParity) (n : Nat)
    (bond : RawBond) :
    bond ∈ (raw parity n).bonds ∧ (bond.source == 3 || bond.target == 3) = true ↔
      bond = ⟨2, 3, .triple⟩ := by
  constructor
  · rintro ⟨retained, incident⟩
    change bond ∈ prefixBonds ++ tailBonds n at retained
    rcases List.mem_append.mp retained with inPrefix | inTail
    · simp only [prefixBonds, List.mem_cons, List.not_mem_nil, or_false] at inPrefix
      rcases inPrefix with rfl | rfl | rfl | rfl | rfl <;> simp_all
    · obtain ⟨offset, _, rfl⟩ := List.mem_map.mp inTail
      simp only [Bool.or_eq_true, beq_iff_eq] at incident
      by_cases root : offset = 0
      · simp [tailParent, root] at incident
      · rw [tailParent, if_neg root] at incident
        omega
  · rintro rfl
    exact ⟨raw_triple_present parity n, rfl⟩

theorem expanded_nitrogen_incident_records (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).bonds.filter (fun bond => bond.source == 3 || bond.target == 3) =
      [⟨2, 3, .triple⟩] := by
  apply List.Perm.eq_singleton
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact (List.Nodup.of_map RawBond.edgeKey (expanded_admissible parity n).2).filter _
  · decide
  · apply Finset.ext
    intro bond
    simp only [List.mem_toFinset, List.mem_filter, List.mem_singleton]
    by_cases incident : (bond.source == 3 || bond.target == 3) = true
    · have physical : bond.source = 3 ∨ bond.target = 3 := by
        simpa only [Bool.or_eq_true, beq_iff_eq] using incident
      rw [expanded_zero_demand_incident parity n 3 (by omega)
        (raw_nitrile_hydrogens parity n).2 bond physical]
      exact raw_nitrogen_incident parity n bond
    · constructor
      · exact fun retained => False.elim (incident retained.2)
      · rintro rfl
        simp at incident

def nitrileParentDuplicate : CanonicalBranchNode :=
  { atom := 2, parent := 3, history := [2, 3, 2, 0],
    provenance := .multipleBondDuplicate 2 }

def nitrileParentDuplicateCursor : CanonicalRerootCursor :=
  ⟨nitrileParentDuplicate, some realNitrileNitrogen⟩

private def nitrogenSeeds (mol : RawMolecule) (bond : RawBond) : List (Nat × Nat) :=
  let next? := if bond.source == 3 then some bond.target
    else if bond.target == 3 then some bond.source else none
  match next? with
  | none => []
  | some next => (List.range (mol.canonicalBondOrder realNitrileNitrogen next)).map
      fun copy => (next, copy)

private theorem nitrogenSeeds_filter (mol : RawMolecule) (bonds : List RawBond) :
    (bonds.filter (fun bond => bond.source == 3 || bond.target == 3)).flatMap
        (nitrogenSeeds mol) = bonds.flatMap (nitrogenSeeds mol) := by
  induction bonds with
  | nil => rfl
  | cons head tail ih =>
      by_cases source : head.source = 3
      · simp [source, ih]
      · by_cases target : head.target = 3
        · simp [target, ih]
        · simp [source, target, nitrogenSeeds, ih]

theorem expanded_nitrogen_canonical_order (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).canonicalBondOrder realNitrileNitrogen 2 = 3 := by
  have order : (expanded parity n).bondOrder 3 2 = 3 := by
    rw [bondOrder_symm]
    exact (expanded_nitrile_bond_orders parity n).2
  simp [canonicalBondOrder, realNitrileNitrogen, order]

theorem expanded_nitrogen_child_copies (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).canonicalChildCopies realNitrileNitrogen = [(2, 1), (2, 2)] := by
  change eraseCanonicalParentCopy 2
    ((expanded parity n).bonds.flatMap (nitrogenSeeds (expanded parity n))) = _
  rw [eraseCanonicalParentCopy_eq_erase, ← nitrogenSeeds_filter,
    expanded_nitrogen_incident_records]
  simp [nitrogenSeeds, expanded_nitrogen_canonical_order]
  rfl

/-- The real nitrile nitrogen retains the two duplicate copies of its bonded carbon; it is
therefore not treated as a terminal leaf merely because its physical degree is one. -/
theorem expanded_nitrogen_children (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).canonicalChildren realNitrileNitrogen =
      [nitrileParentDuplicate, nitrileParentDuplicate] := by
  unfold canonicalChildren
  simp only [realNitrileNitrogen, CanonicalBranchNode.forcedLeaf,
    Bool.false_eq_true, ↓reduceIte]
  change ((expanded parity n).canonicalChildCopies realNitrileNitrogen).map _ = _
  rw [expanded_nitrogen_child_copies]
  rfl

theorem expanded_real_nitrogen_cursor_children (parity : TetrahedralInputParity) (n : Nat) :
    realNitrileCursor.children (expanded parity n) =
      [nitrileParentDuplicateCursor, nitrileParentDuplicateCursor] := by
  change ((expanded parity n).canonicalChildren realNitrileNitrogen).filterMap
    (fun neighbor => if neighbor == canonicalRoot 0 2 then none
      else some ({ node := neighbor, previous? := some realNitrileNitrogen } :
        CanonicalRerootCursor)) = _
  rw [expanded_nitrogen_children]
  rfl

theorem expanded_duplicate_nitrogen_cursor_children (parity : TetrahedralInputParity)
    (n : Nat) : duplicateNitrileCursor.children (expanded parity n) = [] := by rfl

theorem expanded_parent_duplicate_cursor_children (parity : TetrahedralInputParity)
    (n : Nat) : nitrileParentDuplicateCursor.children (expanded parity n) = [] := by rfl

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
