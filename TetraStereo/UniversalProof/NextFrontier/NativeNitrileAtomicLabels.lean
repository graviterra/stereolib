import TetraStereo.UniversalProof.NextFrontier.NativeNitrileLocalExpansion
import TetraStereo.UniversalProof.NextFrontier.NativeNitrilePhysicalAdmission
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileValence
import TetraStereo.OneCenter.CIPAuthoritativeBranchComparator

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule

theorem raw_neutral_atom (parity : TetrahedralInputParity) (n : Nat)
    (spec : AtomSpec) (retained : spec ∈ (raw parity n).atoms) : spec.charge = 0 := by
  change spec ∈ prefixAtoms parity ++ tailAtoms n at retained
  rcases List.mem_append.mp retained with inPrefix | inTail
  · simp only [prefixAtoms, List.mem_cons, List.not_mem_nil, or_false] at inPrefix
    rcases inPrefix with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rcases List.mem_append.mp inTail with repeated | terminal
    · have same := (List.mem_replicate.mp repeated).2
      subst spec
      rfl
    · have same := List.mem_singleton.mp terminal
      subst spec
      rfl

theorem expanded_neutral_atom (parity : TetrahedralInputParity) (n index : Nat)
    (spec : AtomSpec) (observed : (expanded parity n).atomAt? index = some spec) :
    spec.charge = 0 := by
  by_cases old : index < (raw parity n).atomCount
  · obtain ⟨original, lookup⟩ := listGet?_exists_of_lt (raw parity n).atoms index old
    have transported := expanded_original_atom parity n index original lookup
    have same := Option.some.inj (observed.symm.trans transported)
    rw [same]
    exact raw_neutral_atom parity n original
      (listGet?_eq_some_implies_mem (raw parity n).atoms index original lookup)
  · have fresh : n + 7 ≤ index := by rw [raw_atomCount] at old; omega
    rw [(expanded_fresh_hydrogen parity n index spec fresh observed).1]
    rfl

theorem expanded_double_bond_count_zero (parity : TetrahedralInputParity) (n index : Nat) :
    (expanded parity n).incidentDoubleBondCount index = 0 := by
  have empty : (expanded parity n).bonds.filter (fun bond =>
      bond.kind.order == 2 && (bond.source == index || bond.target == index)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro bond retained
    rcases expanded_bond_kinds parity n bond retained with single | triple
    · simp [single, ParsedBondKind.order]
    · simp [triple, ParsedBondKind.order]
  simp only [incidentDoubleBondCount, empty, List.length_nil]

theorem expanded_no_mancude_vertex (parity : TetrahedralInputParity) (n index : Nat) :
    (expanded parity n).localizedMancudeVertex index = false := by
  unfold localizedMancudeVertex
  rw [expanded_double_bond_count_zero]
  cases observed : (expanded parity n).atomAt? index with
  | none => rfl
  | some spec => simp [expanded_neutral_atom parity n index spec observed]

theorem expanded_no_mancude_edges (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).localizedMancudeEdges = [] := by
  have candidates : (expanded parity n).localizedMancudeCandidateEdges = [] := by
    unfold localizedMancudeCandidateEdges
    apply List.filterMap_eq_nil_iff.mpr
    intro bond retained
    simp [expanded_no_mancude_vertex]
  simp only [localizedMancudeEdges, candidates, List.filter_nil]

/-- Every nonphantom occurrence, including actual multiple-bond duplicates, has the natural
atomic-number label in this independent family. No label-success premise is supplied. -/
theorem expanded_natural_labels (parity : TetrahedralInputParity) (n : Nat)
    (node : CanonicalBranchNode)
    (nonphantom : ∀ distance, node.provenance ≠ .phantom distance) :
    (expanded parity n).canonicalRule1aLabel? node =
        some ⟨(expanded parity n).atomZAt node.atom, 1⟩ ∧
      (expanded parity n).canonicalRule1aLabelAuthoritative? node =
        some ⟨(expanded parity n).atomZAt node.atom, 1⟩ := by
  cases provenance : node.provenance with
  | realAtom => simp [canonicalRule1aLabel?, canonicalRule1aLabelAuthoritative?, provenance]
  | ringDuplicate distance =>
      simp [canonicalRule1aLabel?, canonicalRule1aLabelAuthoritative?, provenance]
  | multipleBondDuplicate distance =>
      simp [canonicalRule1aLabel?, canonicalRule1aLabelAuthoritative?, provenance,
        mancudeRule1aLabel?, mancudeRule1aLabelAuthoritative?, expanded_no_mancude_edges,
        containsUndirectedEdge]
  | phantom distance => exact False.elim (nonphantom distance provenance)

theorem expanded_local_atomic_numbers (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).atomZAt 0 = 6 ∧
    (expanded parity n).atomZAt 1 = 9 ∧
    (expanded parity n).atomZAt 2 = 6 ∧
    (expanded parity n).atomZAt 3 = 7 ∧
    (expanded parity n).atomZAt 4 = 6 ∧
    (expanded parity n).atomZAt 5 = 7 ∧
    (expanded parity n).atomZAt 6 = 6 ∧
    (expanded parity n).atomZAt (n + 7) = 1 ∧
    (expanded parity n).atomZAt (n + 8) = 1 := by
  have center := expanded_original_atom parity n 0 (centerSpec parity) (raw_center parity n)
  have fluorine := expanded_original_atom parity n 1 (bracket .F) (raw_fluorine parity n)
  have nitrile := expanded_original_atom parity n 2 (bracket .C) (raw_nitrile_carbon parity n)
  have nitrogen := expanded_original_atom parity n 3 (bracket .N) (raw_nitrile_nitrogen parity n)
  have amino := expanded_original_atom parity n 4 (bracket .C 1) (raw_amino_carbon parity n)
  have amine := expanded_original_atom parity n 5 (bracket .N 2) (by rfl)
  have next := expanded_original_atom parity n 6
    (bracket .C (if 0 < n then 2 else 3)) (by
      simpa only [Nat.zero_add] using raw_tail_atom parity n 0 (by omega))
  simp [atomZAt, center, fluorine, nitrile, nitrogen, amino, amine, next,
    actual_center_hydrogen_atom, actual_amino_hydrogen_atom,
    materializedAtomSpec, centerSpec, bracket, AtomSpec.aliphatic, Element.atomicNumber]

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
