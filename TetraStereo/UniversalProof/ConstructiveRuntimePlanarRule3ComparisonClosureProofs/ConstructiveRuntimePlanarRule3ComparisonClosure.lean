import TetraStereo.UniversalProof.SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource
import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.OneCenter.OfficialContextPerception
import TetraStereo.OneCenter.ChemistrySemantics

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace TetraStereo.UniversalProof.ConstructiveRuntimePlanarRule3ComparisonClosureProofs.ConstructiveRuntimePlanarRule3ComparisonClosure

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.PlanarRule3DoubleBondGeometryProofs.PlanarRule3DoubleBondGeometry
open TetraStereo.UniversalProof.SourceNativePlanarRule3UnitProofs.SourceNativePlanarRule3Unit



























































/-! ## 1. The independently specified double-bond source -/

def fluorineElement : PeriodicElement := ⟨9, by decide, by decide⟩
def chlorineElement : PeriodicElement := ⟨17, by decide, by decide⟩
def carbonElement : PeriodicElement := ⟨6, by decide, by decide⟩

def fluorineAtom : SemanticAtom := { element := fluorineElement }
def chlorineAtom : SemanticAtom := { element := chlorineElement }
def carbonAtom : SemanticAtom := { element := carbonElement }


def molecule : SemanticMolecule :=
  { atoms := [fluorineAtom, carbonAtom, carbonAtom, chlorineAtom, fluorineAtom, chlorineAtom]
    interactions :=
      [ { participants := [0, 1], kind := .covalent 1 }
      , { participants := [1, 2], kind := .covalent 2 }
      , { participants := [1, 3], kind := .covalent 1 }
      , { participants := [2, 4], kind := .covalent 1 }
      , { participants := [2, 5], kind := .covalent 1 } ] }

/-- An exact drawing-plane point literal. -/
def pt (x y : ℚ) : CartesianPoint2 := { x := x, y := y }

/-- The actual drawing: atom 1 at the origin, atom 2 on the positive x-axis, the two senior
references (atoms 3 and 5) strictly above the bond base. -/
def positions : List CartesianPoint2 :=
  [pt (-1) (-1), pt 0 0, pt 2 0, pt (-1) 1, pt 3 (-1), pt 3 1]

/-- One plain diagram bond. -/
def plainBond (source target : ℕ) : DiagramBond :=
  { source := source, target := target, style := .plain }

def diagram : DiagramConfiguration :=
  { atomPositions? := some positions
    bonds := [plainBond 0 1, plainBond 1 2, plainBond 1 3, plainBond 2 4, plainBond 2 5]
    atomConfigurations := [] }

/-- The drawing-only source: no three-dimensional channel, actual diagram positions and bonds. -/
def source : AuthoritativeChemicalInput :=
  { molecule, spatial? := none, diagram? := some diagram }

theorem source_shape :
    source.molecule.atomCount = 6 ∧ source.spatial? = none ∧
      diagram.atomConfigurations = [] :=
  ⟨rfl, rfl, rfl⟩

local instance : NeZero source.molecule.atomCount :=
  ⟨by change (6 : Nat) ≠ 0; decide⟩

abbrev Atom : Type := source.AromaticCanonicalAtom

/-! ## 2. The source-owned planar Rule-3 observation, derived by the actual APIs -/

/-- The represented left substituents of the drawn double bond are exactly atoms 0 and 3. -/
theorem left_candidates : ∀ atom : Atom,
    atom ∈ source.aromaticCanonicalRule3Substituents 1 2 ↔ atom = 0 ∨ atom = 3 := by
  simp only [mem_aromaticCanonicalRule3Substituents_iff]
  unfold AromaticCanonicalAdjacent
  decide +kernel

/-- The represented right substituents of the drawn double bond are exactly atoms 4 and 5. -/
theorem right_candidates : ∀ atom : Atom,
    atom ∈ source.aromaticCanonicalRule3Substituents 2 1 ↔ atom = 4 ∨ atom = 5 := by
  simp only [mem_aromaticCanonicalRule3Substituents_iff]
  unfold AromaticCanonicalAdjacent
  decide +kernel



theorem own_left_senior :
    source.CanonicalAromaticCanonicalRule3ConstitutionalSeniorReference 1 2 3 := by
  apply TetraStereo.UniversalProof.SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource.canonical_senior_of_strict_atomic_heads
    source 1 2 3
  · exact (left_candidates 3).mpr (Or.inr rfl)
  · intro atom present different
    rcases (left_candidates atom).mp present with rfl | rfl
    · change 9 < 17
      decide
    · exact (different rfl).elim



theorem own_right_senior :
    source.CanonicalAromaticCanonicalRule3ConstitutionalSeniorReference 2 1 5 := by
  apply TetraStereo.UniversalProof.SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource.canonical_senior_of_strict_atomic_heads
    source 2 1 5
  · exact (right_candidates 5).mpr (Or.inr rfl)
  · intro atom present different
    rcases (right_candidates atom).mp present with rfl | rfl
    · change 9 < 17
      decide
    · exact (different rfl).elim

/-- The source-owned planar Rule-3 observation: the two actual senior references and the
`seqcis` label read from the actual drawing. -/
def cisUnit : source.AromaticCanonicalRule3SpatialUnitResult := ⟨3, 5, OfficialRule3Geometry.seqcis⟩

/-- The source-owned planar observation is genuinely canonical: an actual ordinary double bond, the
two actual strict senior references, the four actual drawing points and the actual same-side
relation. -/
theorem own_unit_canonical : CanonicalAromaticCanonicalPlanarRule3Unit source 1 2 cisUnit := by
  refine ⟨?_, own_left_senior, own_right_senior, pt 0 0, pt 2 0, pt (-1) 1, pt 3 1,
    ?_, ?_, ?_, ?_, Or.inl ⟨rfl, ?_⟩⟩
  · unfold AromaticCanonicalOrdinaryDoubleBond AromaticCanonicalAdjacent
    decide +kernel
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 1 _).mp (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 2 _).mp (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 3 _).mp (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 5 _).mp (by decide +kernel)
  · norm_num [SameSide, planarDirectedArea, pt]

/-- The actual planar reader emits the source-owned observation at the drawn double bond. -/
theorem own_unit : aromaticCanonicalPlanarRule3Unit? source 1 2 = some cisUnit :=
  (aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical source 1 2 cisUnit).mpr own_unit_canonical

/-- The emitted geometry is `seqcis`, not supplied: it follows from the actual same-side drawing. -/
theorem own_unit_geometry : cisUnit.geometry = OfficialRule3Geometry.seqcis := rfl

/-! ## 3. The same-source parser record with directional alkene markers -/

/-- The source's own connectivity as a parser record.  The double bond `1=2` is ordinary; the two
directional markers `1-3.up` and `2-5.up` are written on the *senior* substituent bonds, exactly the
runtime's own alkene-stereo representation. -/
def witnessRaw : RawMolecule where
  atoms := [AtomSpec.aliphatic .F, AtomSpec.aliphatic .C, AtomSpec.aliphatic .C,
    AtomSpec.aliphatic .Cl, AtomSpec.aliphatic .F, AtomSpec.aliphatic .Cl]
  bonds := [ { source := 0, target := 1, kind := ParsedBondKind.single }
           , { source := 1, target := 2, kind := ParsedBondKind.double }
           , { source := 1, target := 3, kind := ParsedBondKind.up }
           , { source := 2, target := 4, kind := ParsedBondKind.single }
           , { source := 2, target := 5, kind := ParsedBondKind.up } ]

/-- The parser record converts back to the source molecule: this is the same source, not a parallel
implementation. -/
theorem witnessRaw_converts : witnessRaw.toSemanticMolecule? = some molecule := by
  decide +kernel

/-- Same-source ownership: the parser record is a writing of the source's own molecule. -/
theorem same_source_ownership : witnessRaw.toSemanticMolecule? = some source.molecule :=
  witnessRaw_converts

/-! ## 4. The actual generated runtime occurrence, sequence, key and comparison -/

abbrev runtimeResult : ChemistryNormalizationResult := normalizeRawMolecule witnessRaw

/-- The actual occurrence the production producer generates at centre 0 / ligand 1.  Its value is
not supplied: it is derived by evaluating the runtime below. -/
def witnessOccurrence : ChemistryNormalizationResult.Rule3GeometryOccurrence :=
  { left := 1, right := 2, near := 1, distance := 0, geometry := OfficialRule3Geometry.seqcis }

/-- The runtime's directional side-marker channel at the source. -/
theorem runtimeResult_directionalBonds : runtimeResult.stereobonds.directionalBonds =
    [ { source := 1, target := 3, marker := DirectionalBondMarker.up }
    , { source := 2, target := 5, marker := DirectionalBondMarker.up } ] := by
  decide +kernel

/-- The runtime perceives exactly the ordinary double bond `1=2`; its stored value is `unspecified`
(see §6: the stored channel can never be otherwise). -/
theorem runtimeResult_doubleBondAssignments : runtimeResult.stereobonds.doubleBondAssignments =
    [(1, 2, DoubleBondStereo.unspecified)] := by
  decide +kernel

/-- The senior-side reading at the left endpoint is the written `up` marker. -/
theorem runtimeResult_seniorSide_left :
    runtimeResult.seniorSideAt? 1 2 = some DirectionalBondMarker.up := by
  decide +kernel

/-- The senior-side reading at the right endpoint is the written `up` marker. -/
theorem runtimeResult_seniorSide_right :
    runtimeResult.seniorSideAt? 2 1 = some DirectionalBondMarker.up := by
  decide +kernel

/-- The runtime CIP `E/Z` reading of the drawn unit is `Z`. -/
theorem runtimeResult_cip :
    runtimeResult.cipDoubleBondStereo? 1 2 = some DoubleBondStereo.Z := by
  decide +kernel

/-- The perceived stereo the production producer consumes is `Z`. -/
theorem runtimeResult_perceived :
    runtimeResult.perceivedDoubleBondStereo? 1 2 = some DoubleBondStereo.Z := by
  decide +kernel

/-- **The actual generated occurrence.**  The production producer emits exactly one Rule-3
occurrence at centre 0 / ligand 1, with geometry `seqcis`. -/
theorem runtimeResult_occurrences :
    runtimeResult.rule3GeometryOccurrencesOnBranch witnessRaw 0 1 = [witnessOccurrence] := by
  decide +kernel

/-- The runtime geometry sequence at that branch is `[seqcis]`. -/
theorem runtimeResult_sequence :
    runtimeResult.rule3GeometrySequenceOnBranch witnessRaw 0 1 = [OfficialRule3Geometry.seqcis] := by
  unfold ChemistryNormalizationResult.rule3GeometrySequenceOnBranch
  rw [runtimeResult_occurrences]
  rfl

/-- The unary production key of the ligand that reaches the unit is `[2]`. -/
theorem runtimeResult_signature_left :
    runtimeResult.rule3CanonicalSignature witnessRaw 7 0 1 = [2] := by
  decide +kernel

/-- The unary production key of the ligand that does not own the unit is empty. -/
theorem runtimeResult_signature_right :
    runtimeResult.rule3CanonicalSignature witnessRaw 7 0 2 = [] := by
  decide +kernel

/-- **The actual generated comparison.**  The runtime Rule-3 comparator decides the two branches:
the ligand that reaches the drawn unit outranks the one that does not. -/
theorem runtimeResult_comparison :
    runtimeResult.compareRule3GeometryAtCenter witnessRaw 7 0 1 2 = Ordering.gt := by
  unfold ChemistryNormalizationResult.compareRule3GeometryAtCenter
    ChemistryNormalizationResult.compareRule3CanonicalSignatures
  rw [runtimeResult_signature_left, runtimeResult_signature_right]
  decide

/-! ## 5. The generated occurrence contains the source-owned planar observation -/

/-- The actual runtime geometry sequence is exactly the source-owned planar observation's label. -/
theorem runtime_sequence_eq_planar :
    runtimeResult.rule3GeometrySequenceOnBranch witnessRaw 0 1 = [cisUnit.geometry] := by
  unfold ChemistryNormalizationResult.rule3GeometrySequenceOnBranch
  rw [runtimeResult_occurrences]
  rfl

/-- **The headline result.**  At one and the same source: the actual planar reader emits the
source-owned Rule-3 observation; the actual runtime producer emits a genuine occurrence whose
geometry is that observation; and the actual runtime comparator returns a strict decision that
contains it. -/
theorem runtime_comparison_contains_planar_observation :
    (aromaticCanonicalPlanarRule3Unit? source 1 2 = some cisUnit) ∧
      (runtimeResult.rule3GeometrySequenceOnBranch witnessRaw 0 1 = [cisUnit.geometry]) ∧
      (runtimeResult.compareRule3GeometryAtCenter witnessRaw 7 0 1 2 = Ordering.gt) :=
  ⟨own_unit, runtime_sequence_eq_planar, runtimeResult_comparison⟩

/-- Existential form: the runtime recovers *some* source-owned planar observation's own label, and
its geometry is the derived `seqcis` (no label is supplied as a premise). -/
theorem runtime_recovers_source_planar_observation :
    ∃ unit : source.AromaticCanonicalRule3SpatialUnitResult,
      aromaticCanonicalPlanarRule3Unit? source 1 2 = some unit ∧
      unit.geometry = OfficialRule3Geometry.seqcis ∧
      runtimeResult.rule3GeometrySequenceOnBranch witnessRaw 0 1 = [unit.geometry] :=
  ⟨cisUnit, own_unit, rfl, runtime_sequence_eq_planar⟩

/-! ## 6. A general API fact: the runtime's stored double-bond channel is vacuous -/

/-- Every stored double-bond assignment produced by the runtime's own `stereobondSemantics` carries
`DoubleBondStereo.unspecified`: the extractor never writes a specified stored `E`/`Z`.  Hence the
"stored" first source of `perceivedDoubleBondStereo?` is dead in the actual pipeline and the runtime
depends on the directional-marker channel alone. -/
theorem doubleBondAssignments_eq_unspecified (mol : RawMolecule)
    (assignment : ℕ × ℕ × DoubleBondStereo)
    (present : assignment ∈ (stereobondSemantics mol).doubleBondAssignments) :
    assignment.2.2 = DoubleBondStereo.unspecified := by
  have hdecomp : (stereobondSemantics mol).doubleBondAssignments =
      mol.bonds.filterMap (fun bond =>
        if bond.kind = ParsedBondKind.double then
          some (bond.source, bond.target, DoubleBondStereo.unspecified) else none) := rfl
  rw [hdecomp] at present
  rw [List.mem_filterMap] at present
  obtain ⟨bond, _, hbond⟩ := present
  by_cases hdouble : bond.kind = ParsedBondKind.double
  · rw [if_pos hdouble] at hbond
    cases hbond
    rfl
  · rw [if_neg hdouble] at hbond
    cases hbond

/-- Corollary at the runtime reader: the stored reading is always absent for a normalized
`stereobondSemantics`. -/
theorem stereobondSemantics_storedDoubleBondStereo?_eq_none (mol : RawMolecule) (u v : ℕ) :
    (stereobondSemantics mol).storedDoubleBondStereo? u v = none := by
  unfold StereobondSemantics.storedDoubleBondStereo?
  cases hfind : (stereobondSemantics mol).doubleBondAssignments.find?
      (fun assignment => StereobondSemantics.doubleBondAssignmentConnects assignment u v) with
  | none => rfl
  | some assignment =>
      obtain ⟨l, r, s⟩ := assignment
      have hs : s = DoubleBondStereo.unspecified := by
        have hmem := doubleBondAssignments_eq_unspecified mol (l, r, s)
          (List.mem_of_find?_eq_some hfind)
        simpa using hmem
      simp only [StereobondSemantics.doubleBondAssignmentStereo, hs]

end TetraStereo.UniversalProof.ConstructiveRuntimePlanarRule3ComparisonClosureProofs.ConstructiveRuntimePlanarRule3ComparisonClosure
