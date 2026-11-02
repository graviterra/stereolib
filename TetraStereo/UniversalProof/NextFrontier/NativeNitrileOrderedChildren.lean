import TetraStereo.UniversalProof.NextFrontier.NativeNitrileCanonicalChildren

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule

private theorem pair_permutation_cases {Alpha : Type} (values : List Alpha) (left right : Alpha)
    (permutation : values.Perm [left, right]) :
    values = [left, right] ∨ values = [right, left] := by
  have length : values.length = 2 := permutation.length_eq
  obtain ⟨first, second, rfl⟩ := List.length_eq_two.mp length
  have firstMember : first = left ∨ first = right := by
    have member := permutation.mem_iff.mp (List.mem_cons_self : first ∈ [first, second])
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
  rcases firstMember with same | same
  · subst first
    have tail := permutation.cons_inv
    have same : second = right := by simpa using tail
    exact Or.inl (by rw [same])
  · subst first
    have swapped : ([left, right] : List Alpha).Perm [right, left] := List.Perm.swap _ _ _
    have tail := (permutation.trans swapped).cons_inv
    have same : second = left := by simpa using tail
    exact Or.inr (by rw [same])

private def nitrileSeeds (mol : RawMolecule) (bond : RawBond) : List (Nat × Nat) :=
  let next? := if bond.source == 2 then some bond.target
    else if bond.target == 2 then some bond.source else none
  match next? with
  | none => []
  | some next => (List.range (mol.canonicalBondOrder (canonicalRoot 0 2) next)).map
      fun copy => (next, copy)

private theorem nitrileSeeds_filter (mol : RawMolecule) (bonds : List RawBond) :
    (bonds.filter (fun bond => bond.source == 2 || bond.target == 2)).flatMap
        (nitrileSeeds mol) = bonds.flatMap (nitrileSeeds mol) := by
  induction bonds with
  | nil => rfl
  | cons head tail ih =>
      by_cases source : head.source = 2
      · simp [source, ih]
      · by_cases target : head.target = 2
        · simp [target, ih]
        · simp [source, target, nitrileSeeds, ih]

/-- A triple-bond record emits its copies in the actual constructor order. Removing the
single parent copy leaves this exact block regardless of the two incident records' order. -/
theorem expanded_nitrile_child_copies_exact (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).canonicalChildCopies (canonicalRoot 0 2) =
      [(3, 0), (3, 1), (3, 2)] := by
  have incident := expanded_nitrile_incident_records parity n
  change (((expanded parity n).bonds).filter
    (fun bond => bond.source == 2 || bond.target == 2)).Perm
      [⟨0, 2, .single⟩, ⟨2, 3, .triple⟩] at incident
  have alternatives := pair_permutation_cases _ _ _ incident
  change eraseCanonicalParentCopy 0
    ((expanded parity n).bonds.flatMap (nitrileSeeds (expanded parity n))) = _
  rw [eraseCanonicalParentCopy_eq_erase, ← nitrileSeeds_filter]
  have orders := expanded_nitrile_canonical_orders parity n
  rcases alternatives with first | reverse
  · rw [first]
    simp [nitrileSeeds, orders.1, orders.2]
    rfl
  · rw [reverse]
    simp [nitrileSeeds, orders.1, orders.2]
    rfl

theorem expanded_nitrile_children_exact (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).canonicalChildren (canonicalRoot 0 2) =
      [realNitrileNitrogen, nitrileDuplicate, nitrileDuplicate] := by
  unfold canonicalChildren
  simp only [canonicalRoot, CanonicalBranchNode.forcedLeaf, Bool.false_eq_true, ↓reduceIte]
  change ((expanded parity n).canonicalChildCopies (canonicalRoot 0 2)).map _ = _
  rw [expanded_nitrile_child_copies_exact]
  rfl

def nitrileCursor : CanonicalRerootCursor :=
  ⟨canonicalRoot 0 2, some (canonicalCenterRoot 0)⟩

def realNitrileCursor : CanonicalRerootCursor :=
  ⟨realNitrileNitrogen, some (canonicalRoot 0 2)⟩

def duplicateNitrileCursor : CanonicalRerootCursor :=
  ⟨nitrileDuplicate, some (canonicalRoot 0 2)⟩

theorem expanded_nitrile_cursor_children (parity : TetrahedralInputParity) (n : Nat) :
    nitrileCursor.children (expanded parity n) =
      [realNitrileCursor, duplicateNitrileCursor, duplicateNitrileCursor] := by
  change ((expanded parity n).canonicalChildren (canonicalRoot 0 2)).filterMap
    (fun neighbor => if neighbor == canonicalCenterRoot 0 then none
      else some ({ node := neighbor, previous? := some (canonicalRoot 0 2) } :
        CanonicalRerootCursor)) = _
  rw [expanded_nitrile_children_exact]
  rfl

/-- The unsorted constructor's second nitrogen is an actual multiple-bond duplicate. Sorting
provenance is a separate downstream obligation, rather than inferred from this statement. -/
theorem expanded_nitrile_second_child_provenance (parity : TetrahedralInputParity) (n : Nat) :
    ((nitrileCursor.children (expanded parity n))[1]?).map
      (fun cursor => cursor.node.provenance) = some (.multipleBondDuplicate 1) := by
  rw [expanded_nitrile_cursor_children]
  rfl

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
