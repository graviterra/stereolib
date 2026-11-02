import TetraStereo.OneCenter.CIPP93TrigonalPyramidalIntegration

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.TrigonalPyramidal

/-!
# Locally computed written-phantom candidates

This module computes, from the molecule alone, the centers at which the existing P-93.3
`WrittenConfigurationFrame` applies.  The candidate view is deliberately *non-circular*:

* the enumeration is a plain `List.range mol.atomCount` filter over the parsed atom record and
  the written-neighbour list;
* the parity used by the filter is the atom's written `tetrahedral?` annotation, which the parser
  fills only from `@`/`@@` source tokens (see `writtenParityAt?`); no geometry observation is an
  input and no parity is inferred from geometry;
* completeness is proved against the actual pre-existing
  `WrittenConfigurationFrame`, not against a bespoke predicate.

A candidate establishes only the shape of the notional four-position frame.  It does **not**
establish strict CIP priorities, nondegenerate spatial geometry, or the existence of a descriptor.
The last section links candidates to the production `tetrahedralAssignments` reporter, but states
only that the center is routed into that report (the emitted outcome may still be a refusal).
-/

/-! ## Written parity source -/

/-- The written `@`/`@@` parity supplied at one atom, if any.  This is read from the parsed atom
record; it is never derived from observed geometry. -/
def writtenParityAt? (mol : RawMolecule) (center : Nat) :
    Option TetrahedralInputParity :=
  (mol.atomAt? center).bind AtomSpec.tetrahedral?

/-- On a present atom, the bundled parity source is exactly the atom's written annotation. -/
theorem writtenParityAt?_eq_tetrahedral? (mol : RawMolecule) (center : Nat)
    (atom : AtomSpec) (present : mol.atomAt? center = some atom) :
    writtenParityAt? mol center = atom.tetrahedral? := by
  simp [writtenParityAt?, present]

/-- The supplied-parity source is present exactly when some atom at the center carries a written
`tetrahedral?` annotation. -/
theorem writtenParityAt?_isSome_iff (mol : RawMolecule) (center : Nat) :
    (writtenParityAt? mol center).isSome = true ↔
      ∃ atom parity,
        mol.atomAt? center = some atom ∧ atom.tetrahedral? = some parity := by
  unfold writtenParityAt?
  cases present : mol.atomAt? center with
  | none => simp
  | some atom =>
      simp only [Option.bind_some]
      rw [Option.isSome_iff_exists]
      constructor
      · rintro ⟨parity, parity_eq⟩
        exact ⟨atom, parity, rfl, parity_eq⟩
      · rintro ⟨atom', parity, atom_eq, parity_eq⟩
        simp only [Option.some.injEq] at atom_eq
        subst atom'
        exact ⟨parity, parity_eq⟩

/-! ## Candidate computation -/

/-- Executable P-93.3 shape filter at one center.

The predicate inspects (1) the parsed atom's element against `ElementSupportsPhantom`, (2) the
atom's supplied written parity annotation, and (3) the written-neighbour count.  It has no
geometry parameter. -/
def IsWrittenPhantomCandidate (mol : RawMolecule) (center : Nat) : Bool :=
  match mol.atomAt? center with
  | none => false
  | some atom =>
      decide (ElementSupportsPhantom atom.element) &&
        atom.tetrahedral?.isSome &&
        ((mol.writtenNeighbors center).length == 3)

/-- The finite, duplicate-free candidate enumeration: traverse every physical atom index and keep
the centers satisfying the written-phantom shape filter. -/
def writtenPhantomCandidates (mol : RawMolecule) : List Nat :=
  (List.range mol.atomCount).filter (IsWrittenPhantomCandidate mol)

/-- Unfolding form of the shape filter, exposing the three independently checked conditions. -/
theorem isWrittenPhantomCandidate_eq_true_iff
    (mol : RawMolecule) (center : Nat) :
    IsWrittenPhantomCandidate mol center = true ↔
      ∃ atom parity,
        mol.atomAt? center = some atom ∧
          atom.tetrahedral? = some parity ∧
          ElementSupportsPhantom atom.element ∧
          (mol.writtenNeighbors center).length = 3 := by
  unfold IsWrittenPhantomCandidate
  cases present : mol.atomAt? center with
  | none => simp
  | some atom =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc]
      constructor
      · rintro ⟨supported, parityPresent, three⟩
        obtain ⟨parity, parity_eq⟩ := Option.isSome_iff_exists.mp parityPresent
        exact ⟨atom, parity, rfl, parity_eq, supported, three⟩
      · rintro ⟨atom', parity, atom_eq, parity_eq, supported, three⟩
        simp only [Option.some.injEq] at atom_eq
        subst atom'
        exact ⟨supported, Option.isSome_iff_exists.mpr ⟨parity, parity_eq⟩, three⟩

/-! ## Exact frame membership -/

/-- Membership in the computed candidate list is exactly nonemptiness of the pre-existing
`WrittenConfigurationFrame`.  No caller-supplied candidate or frame is used. -/
theorem mem_writtenPhantomCandidates_iff
    (mol : RawMolecule) (center : Nat) :
    center ∈ writtenPhantomCandidates mol ↔
      Nonempty (WrittenConfigurationFrame mol center) := by
  unfold writtenPhantomCandidates
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨bound, shape⟩
    obtain ⟨atom, parity, atom_eq, parity_eq, supported, three⟩ :=
      (isWrittenPhantomCandidate_eq_true_iff mol center).mp shape
    exact ⟨{ atom := atom
             atom_eq := atom_eq
             parity := parity
             parity_eq := parity_eq
             element_supported := supported
             three_physical := three }⟩
  · rintro ⟨frame⟩
    refine ⟨?_, (isWrittenPhantomCandidate_eq_true_iff mol center).mpr
      ⟨frame.atom, frame.parity, frame.atom_eq, frame.parity_eq,
        frame.element_supported, frame.three_physical⟩⟩
    exact listGet?_eq_some_implies_lt mol.atoms center frame.atom
      (by simpa [RawMolecule.atomAt?] using frame.atom_eq)

/-- Sound direction, named for direct use. -/
theorem nonempty_writtenConfigurationFrame_of_mem_writtenPhantomCandidates
    (mol : RawMolecule) (center : Nat)
    (mem : center ∈ writtenPhantomCandidates mol) :
    Nonempty (WrittenConfigurationFrame mol center) :=
  (mem_writtenPhantomCandidates_iff mol center).mp mem

/-- Exhaustive direction: every actual written-configuration frame is enumerated. -/
theorem mem_writtenPhantomCandidates_of_writtenConfigurationFrame
    (mol : RawMolecule) (center : Nat)
    (frame : WrittenConfigurationFrame mol center) :
    center ∈ writtenPhantomCandidates mol :=
  (mem_writtenPhantomCandidates_iff mol center).mpr ⟨frame⟩

/-- The shape data carried by a candidate, without introducing a frame. -/
theorem exists_atom_parity_of_mem_writtenPhantomCandidates
    (mol : RawMolecule) {center : Nat}
    (mem : center ∈ writtenPhantomCandidates mol) :
    ∃ atom parity,
      mol.atomAt? center = some atom ∧
        atom.tetrahedral? = some parity ∧
        ElementSupportsPhantom atom.element ∧
        (mol.writtenNeighbors center).length = 3 := by
  unfold writtenPhantomCandidates at mem
  exact (isWrittenPhantomCandidate_eq_true_iff mol center).mp
    (List.mem_filter.mp mem).2

/-- Every enumerated center is a real parsed atom, not an out-of-range sentinel. -/
theorem exists_atom_of_mem_writtenPhantomCandidates
    (mol : RawMolecule) {center : Nat}
    (mem : center ∈ writtenPhantomCandidates mol) :
    ∃ atom, mol.atomAt? center = some atom := by
  obtain ⟨atom, _, atom_eq, _, _, _⟩ :=
    exists_atom_parity_of_mem_writtenPhantomCandidates mol mem
  exact ⟨atom, atom_eq⟩

/-! ## Finiteness and duplicate-freedom -/

/-- Candidates are duplicate-free because the underlying `List.range` is. -/
theorem writtenPhantomCandidates_nodup (mol : RawMolecule) :
    (writtenPhantomCandidates mol).Nodup := by
  unfold writtenPhantomCandidates
  exact List.Nodup.sublist
    (List.filter_sublist (p := IsWrittenPhantomCandidate mol)) List.nodup_range

/-- Every candidate index is a physical atom index. -/
theorem mem_writtenPhantomCandidates_lt
    (mol : RawMolecule) {center : Nat}
    (mem : center ∈ writtenPhantomCandidates mol) :
    center < mol.atomCount := by
  unfold writtenPhantomCandidates at mem
  exact List.mem_range.mp (List.mem_filter.mp mem).1

/-- The enumeration is a sublist of the physical index range. -/
theorem writtenPhantomCandidates_subset_range (mol : RawMolecule) :
    writtenPhantomCandidates mol ⊆ List.range mol.atomCount := by
  intro center mem
  exact List.mem_range.mpr (mem_writtenPhantomCandidates_lt mol mem)

/-- The candidate list is finite and bounded by the atom count. -/
theorem writtenPhantomCandidates_length_le (mol : RawMolecule) :
    (writtenPhantomCandidates mol).length ≤ mol.atomCount := by
  unfold writtenPhantomCandidates
  simpa using
    (List.length_filter_le (IsWrittenPhantomCandidate mol) (List.range mol.atomCount))

/-- The phantom sentinel has no atom record: `atomAt?` is `none` past the end of the atom list. -/
theorem listGet?_eq_none_of_length_le {α : Type*} (values : List α) (index : Nat)
    (bound : values.length ≤ index) : listGet? values index = none := by
  induction values generalizing index with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => simp at bound
      | succ index =>
          simp only [listGet?]
          apply inductionHypothesis
          simp only [List.length_cons] at bound
          omega

/-- The out-of-range phantom index used by `writtenPhantomFrame` is not a parsed atom. -/
theorem atomAt?_atomCount_eq_none (mol : RawMolecule) :
    mol.atomAt? mol.atomCount = none := by
  unfold RawMolecule.atomAt? RawMolecule.atomCount
  exact listGet?_eq_none_of_length_le mol.atoms mol.atoms.length (le_refl _)

/-- The phantom sentinel is never enumerated as a candidate center. -/
theorem atomCount_not_mem_writtenPhantomCandidates (mol : RawMolecule) :
    mol.atomCount ∉ writtenPhantomCandidates mol := by
  intro mem
  have bound := mem_writtenPhantomCandidates_lt mol mem
  omega

/-- Both sentinel facts together: the frame's phantom position stays a typed out-of-range index
and is never treated as a real center. -/
theorem phantom_sentinel_not_real_atom (mol : RawMolecule) :
    mol.atomCount ∉ writtenPhantomCandidates mol ∧
      mol.atomAt? mol.atomCount = none :=
  ⟨atomCount_not_mem_writtenPhantomCandidates mol, atomAt?_atomCount_eq_none mol⟩

/-! ## Certificates for every candidate -/

/-- Every candidate of a molecule with exact written neighbours yields the existing notional
four-position certificate, by the existing integration theorem. -/
theorem writtenPhantomCandidate_certificate
    (mol : RawMolecule) (exact : mol.WrittenNeighborExact) {center : Nat}
    (mem : center ∈ writtenPhantomCandidates mol) :
    NotionalTetrahedralFrameCertificate mol center := by
  obtain ⟨frame⟩ :=
    nonempty_writtenConfigurationFrame_of_mem_writtenPhantomCandidates mol center mem
  exact writtenConfigurationFrame_certificate mol center frame exact

/-- Connectivity-only perception still rejects every computed candidate.  This is a direct reuse
of the existing general theorem, not a new completeness claim. -/
theorem connectivityOnlyTetrahedralLigands?_eq_none_of_mem_writtenPhantomCandidates
    (result : ChemistryNormalizationResult) (mol : RawMolecule) {center : Nat}
    (mem : center ∈ writtenPhantomCandidates mol) :
    connectivityOnlyTetrahedralLigands? result mol center = none := by
  obtain ⟨frame⟩ :=
    nonempty_writtenConfigurationFrame_of_mem_writtenPhantomCandidates mol center mem
  exact connectivityOnlyTetrahedralLigands?_eq_none_of_writtenConfigurationFrame
    result mol center frame

/-! ## Link to the production reported-candidate pipeline -/

/-- If the parsed result agrees with the molecule at a candidate center and that center is not an
extended-tetrahedral carrier, the annotated tetrahedral reporter produces an outcome for it.

The conclusion only says that the production reporter **reaches** the center.  The outcome may be
`StereoOutcome.refused`; no `R/S` descriptor, strict priority order, or nondegenerate geometry is
asserted. -/
theorem annotatedTetrahedralOutcome?_isSome_of_written
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel idx : Nat) (spec : AtomSpec)
    (present : result.parsed.atomAt? idx = some spec)
    (written : spec.tetrahedral?.isSome = true)
    (not_extended : mol.isExtendedTetrahedralParityCarrier idx = false) :
    (annotatedTetrahedralOutcome? result mol state fuel idx).isSome = true := by
  unfold annotatedTetrahedralOutcome?
  cases atom_eq : result.parsed.atomAt? idx with
  | none => simp [atom_eq] at present
  | some parsedSpec =>
      have parsedEq : parsedSpec = spec :=
        Option.some.inj (atom_eq.symm.trans present)
      subst parsedSpec
      cases parity_eq : spec.tetrahedral? with
      | none => simp [parity_eq] at written
      | some parity =>
          cases extended_eq : mol.isExtendedTetrahedralParityCarrier idx with
          | true => simp [extended_eq] at not_extended
          | false =>
              cases fact_eq : Option.first (state.factAt? idx)
                  (tetrahedralFactThroughExtendedTetrahedralPseudo? mol fuel idx) with
              | some fact => simp [parity_eq]
              | none =>
                  cases supported : RawMolecule.centreElementSupported spec.element with
                  | false => simp [parity_eq, supported]
                  | true =>
                      by_cases count_eq : (mol.ligandsWithLonePair idx).length = 4
                      · cases ranking : rankBranchPositionsThroughOfficialContext?
                            result mol state fuel idx (mol.ligandsWithLonePair idx) with
                        | some positions => simp [parity_eq, supported, count_eq, ranking]
                        | none =>
                            cases rule6 : tetrahedralRule6Stereogenicity?
                                result mol state fuel idx with
                            | some decision =>
                                cases decision <;>
                                  simp [parity_eq, supported, count_eq, ranking]
                            | none => simp [parity_eq, supported, count_eq, ranking]
                      · simp [parity_eq, supported, count_eq]

/-- A candidate is routed by the production `tetrahedralAssignment?` dispatcher to an assignment
whose unit is `StereoUnit.tetrahedral center`. -/
theorem tetrahedralAssignment?_eq_some_of_candidate
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (parsed_eq : result.parsed.atomAt? center = mol.atomAt? center)
    (not_extended : mol.isExtendedTetrahedralParityCarrier center = false)
    (mem : center ∈ writtenPhantomCandidates mol) :
    ∃ outcome,
      tetrahedralAssignment? result mol state fuel center =
        some { unit := StereoUnit.tetrahedral center, outcome := outcome } := by
  obtain ⟨atom, parity, atom_eq, parity_eq, _supported, _three⟩ :=
    exists_atom_parity_of_mem_writtenPhantomCandidates mol mem
  have parsed_atom : result.parsed.atomAt? center = some atom := parsed_eq.trans atom_eq
  have written : atom.tetrahedral?.isSome = true := by
    rw [parity_eq]
    rfl
  have produced := annotatedTetrahedralOutcome?_isSome_of_written
    result mol state fuel center atom parsed_atom written not_extended
  obtain ⟨outcome, outcome_eq⟩ := Option.isSome_iff_exists.mp produced
  refine ⟨outcome, ?_⟩
  unfold tetrahedralAssignment?
  rw [parsed_atom]
  simp only [parity_eq]
  unfold annotatedTetrahedralAssignment?
  rw [outcome_eq]
  rfl

/-- Candidate centers appear in the real reported list `tetrahedralAssignments`, with the actual
`StereoUnit.tetrahedral center` unit.  The report may still carry a refusal outcome. -/
theorem mem_tetrahedralAssignments_of_candidate
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (parsed_eq : result.parsed.atomAt? center = mol.atomAt? center)
    (not_extended : mol.isExtendedTetrahedralParityCarrier center = false)
    (mem : center ∈ writtenPhantomCandidates mol) :
    ∃ outcome,
      { unit := StereoUnit.tetrahedral center, outcome := outcome } ∈
        tetrahedralAssignments result mol state fuel := by
  obtain ⟨atom, _parity, atom_eq, _parity_eq, _supported, _three⟩ :=
    exists_atom_parity_of_mem_writtenPhantomCandidates mol mem
  have parsed_atom : result.parsed.atomAt? center = some atom := parsed_eq.trans atom_eq
  have bound : center < result.parsed.atomCount :=
    listGet?_eq_some_implies_lt result.parsed.atoms center atom
      (by simpa [RawMolecule.atomAt?] using parsed_atom)
  obtain ⟨outcome, assignment_eq⟩ :=
    tetrahedralAssignment?_eq_some_of_candidate result mol state fuel center
      parsed_eq not_extended mem
  refine ⟨outcome, ?_⟩
  unfold tetrahedralAssignments
  exact List.mem_filterMap.mpr ⟨center, List.mem_range.mpr bound, assignment_eq⟩

/-! ## Explicit ethyl methyl sulfoxide fragment

The parcel below is an acyclic ethyl methyl sulfoxide fragment.  Atom `0` is the sulfoxide sulfur
with a written `@` annotation; its three written ligands are the oxido oxygen `1`, the ethyl
`CH₂` atom `2` (which continues to `CH₃` atom `3`), and the methyl atom `4`.  The ethyl and methyl
substituents are constitutionally distinct, so this is not the dimethyl sulfoxide case.
-/

/-- Ethyl methyl sulfoxide fragment `CCO[S@](=O)C`, with the sulfur centre at index `0`. -/
def ethylMethylSulfoxide : RawMolecule where
  atoms :=
    [ { element := Element.S, tetrahedral? := some TetrahedralInputParity.clockwise }
    , { element := Element.O }
    , { element := Element.C, explicitHydrogens? := some 2 }
    , { element := Element.C, explicitHydrogens? := some 3 }
    , { element := Element.C, explicitHydrogens? := some 3 } ]
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.double }
    , { source := 0, target := 2, kind := ParsedBondKind.single }
    , { source := 2, target := 3, kind := ParsedBondKind.single }
    , { source := 0, target := 4, kind := ParsedBondKind.single } ]
  neighborOrder := [[1, 2, 4], [0], [0, 3], [2], [0]]

/-- The written atom record at the sulfur center, including the supplied `@` parity. -/
theorem ethylMethylSulfoxide_center_atom :
    ethylMethylSulfoxide.atomAt? 0 =
      some { element := Element.S
             tetrahedral? := some TetrahedralInputParity.clockwise } := by
  decide

/-- The explicit all-three-neighbour source for the sulfur center. -/
theorem ethylMethylSulfoxide_writtenNeighbors_center :
    ethylMethylSulfoxide.writtenNeighbors 0 = [1, 2, 4] := by
  decide

/-- The three written neighbours are pairwise distinct. -/
theorem ethylMethylSulfoxide_center_neighbors_nodup :
    (ethylMethylSulfoxide.writtenNeighbors 0).Nodup := by
  rw [ethylMethylSulfoxide_writtenNeighbors_center]
  decide

/-- The ethyl substituent continues to the terminal methyl, while the methyl ligand does not:
the two carbon substituents are constitutionally distinct. -/
theorem ethylMethylSulfoxide_substituents_distinct :
    ethylMethylSulfoxide.writtenNeighbors 2 = [0, 3] ∧
      ethylMethylSulfoxide.writtenNeighbors 4 = [0] := by
  decide

/-- Candidate admission of the sulfur center. -/
theorem ethylMethylSulfoxide_center_mem_writtenPhantomCandidates :
    0 ∈ writtenPhantomCandidates ethylMethylSulfoxide := by
  decide

/-- The computed candidate list consists exactly of the sulfur center. -/
theorem ethylMethylSulfoxide_writtenPhantomCandidates :
    writtenPhantomCandidates ethylMethylSulfoxide = [0] := by
  decide

/-- The sulfur center really satisfies the pre-existing written-configuration frame. -/
theorem ethylMethylSulfoxide_nonempty_frame :
    Nonempty (WrittenConfigurationFrame ethylMethylSulfoxide 0) :=
  nonempty_writtenConfigurationFrame_of_mem_writtenPhantomCandidates
    ethylMethylSulfoxide 0 ethylMethylSulfoxide_center_mem_writtenPhantomCandidates

/-- The fragment's written-neighbour view is exact. -/
theorem ethylMethylSulfoxide_writtenNeighborExact :
    ethylMethylSulfoxide.WrittenNeighborExact := by
  change ethylMethylSulfoxide.writtenNeighborExact? = true
  decide

/-- The existing integration theorem yields the notional four-position certificate. -/
theorem ethylMethylSulfoxide_certificate :
    NotionalTetrahedralFrameCertificate ethylMethylSulfoxide 0 :=
  writtenPhantomCandidate_certificate ethylMethylSulfoxide
    ethylMethylSulfoxide_writtenNeighborExact
    ethylMethylSulfoxide_center_mem_writtenPhantomCandidates

/-- The phantom position is present in the generated frame. -/
theorem ethylMethylSulfoxide_phantom_mem_frame :
    ethylMethylSulfoxide.atomCount ∈ writtenPhantomFrame ethylMethylSulfoxide 0 :=
  atomCount_mem_writtenPhantomFrame ethylMethylSulfoxide 0

/-- The phantom sentinel is outside the physical atom indices and is not a candidate. -/
theorem ethylMethylSulfoxide_phantom_not_candidate :
    ethylMethylSulfoxide.atomCount ∉
      writtenPhantomCandidates ethylMethylSulfoxide :=
  atomCount_not_mem_writtenPhantomCandidates ethylMethylSulfoxide

end BlueBookP93.TrigonalPyramidal
end TetraStereo.OneCenter
