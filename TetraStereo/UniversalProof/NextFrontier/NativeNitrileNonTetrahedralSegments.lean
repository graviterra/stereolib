import TetraStereo.UniversalProof.NextFrontier.NativeNitrileInitialSeed

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileInitialSeed

theorem raw_no_double (parity : TetrahedralInputParity) (n : Nat) :
    ∀ bond ∈ (raw parity n).bonds, bond.kind ≠ .double := by
  intro bond retained
  rcases raw_bond_kinds parity n bond retained with single | triple <;> simp_all

theorem expanded_no_double (parity : TetrahedralInputParity) (n : Nat) :
    ∀ bond ∈ (expanded parity n).bonds, bond.kind ≠ .double := by
  intro bond retained
  rcases expanded_bond_kinds parity n bond retained with single | triple <;> simp_all

private theorem no_double_neighbors (mol : RawMolecule)
    (absent : ∀ bond ∈ mol.bonds, bond.kind ≠ .double) (index : Nat) :
    mol.doubleBondNeighbors index = [] := by
  have none : (mol.bonds.filterMap fun bond =>
      if bond.kind != ParsedBondKind.double then none
      else if bond.source == index then some bond.target
      else if bond.target == index then some bond.source else none) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro bond retained
    simp [absent bond retained]
  change (mol.bonds.filterMap fun bond =>
    if bond.kind != ParsedBondKind.double then Option.none
    else if bond.source == index then some bond.target
    else if bond.target == index then some bond.source else Option.none).eraseDups = []
  rw [none]
  rfl

theorem no_double_extended_chains (mol : RawMolecule)
    (absent : ∀ bond ∈ mol.bonds, bond.kind ≠ .double) : mol.extendedDoubleBondChains = [] := by
  unfold extendedDoubleBondChains
  apply List.filterMap_eq_nil_iff.mpr
  intro index _
  simp only [no_double_neighbors mol absent index]

theorem no_double_stereobond_assignments (mol : RawMolecule)
    (absent : ∀ bond ∈ mol.bonds, bond.kind ≠ .double) :
    (stereobondSemantics mol).doubleBondAssignments = [] := by
  change (mol.bonds.filterMap fun bond =>
    if bond.kind = ParsedBondKind.double then
      some (bond.source, bond.target, DoubleBondStereo.unspecified) else none) = []
  apply List.filterMap_eq_nil_iff.mpr
  intro bond retained
  simp [absent bond retained]

theorem actual_stereobonds_nil (n : Nat) (parity : TetrahedralInputParity) :
    (nitrileResult n parity).stereobonds.doubleBondAssignments = [] := by
  change (stereobondSemantics (raw parity n).normalizeUnspecifiedBonds).doubleBondAssignments = []
  rw [raw_normalization_identity]
  exact no_double_stereobond_assignments _ (raw_no_double parity n)

/-- The triple bond is preserved. It creates no ordinary/coupled/cumulene/axial double-bond
report segment, proved from the actual non-double bond inventory rather than an all-single premise. -/
theorem actual_other_four_segments_nil (n : Nat) (parity : TetrahedralInputParity) :
    let branches := normalizedStereoAnalysisBranches (nitrileResult n parity)
    branches.ordinaryDoubleBond = [] ∧ branches.coupledDoubleBond = [] ∧
      branches.oddCumuleneDoubleBond = [] ∧ branches.extendedAxial = [] := by
  have ordinary := actual_stereobonds_nil n parity
  have chains : (nitrileResult n parity).parsed.extendedDoubleBondChains = [] := by
    rw [nitrileResult, raw_normalized_parsed]
    exact no_double_extended_chains _ (raw_no_double parity n)
  have expandedChains : (expanded parity n).extendedDoubleBondChains = [] :=
    no_double_extended_chains _ (expanded_no_double parity n)
  have carriers :
      (nitrileResult n parity).parsed.withExplicitHydrogens.extendedTetrahedralParityCarriers = [] := by
    rw [actual_normalized_materialization]
    simp [extendedTetrahedralParityCarriers, expandedChains]
  simp [normalizedStereoAnalysisBranches, ordinaryDoubleBondAssignments,
    oddCumuleneDoubleBondAssignments, ordinary, chains, carriers]

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
