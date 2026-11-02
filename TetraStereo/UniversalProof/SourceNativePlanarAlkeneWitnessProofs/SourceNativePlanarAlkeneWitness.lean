import TetraStereo.UniversalProof.SourceNativePlanarRule3UnitProofs.SourceNativePlanarRule3Unit

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.SourceNativePlanarAlkeneWitnessProofs.SourceNativePlanarAlkeneWitness

open TetraStereo.OneCenter
open TetraStereo.UniversalProof.PlanarRule3DoubleBondGeometryProofs.PlanarRule3DoubleBondGeometry
open TetraStereo.UniversalProof.SourceNativePlanarRule3UnitProofs.SourceNativePlanarRule3Unit



























/-! ## The concrete six-atom source -/

/-- An exact drawing-plane point literal. -/
def pt (x y : ℚ) : CartesianPoint2 := { x := x, y := y }

def carbonElement : PeriodicElement := ⟨6, by decide, by decide⟩
def fluorineElement : PeriodicElement := ⟨9, by decide, by decide⟩
def chlorineElement : PeriodicElement := ⟨17, by decide, by decide⟩

def carbonAtom : SemanticAtom := { element := carbonElement }
def fluorineAtom : SemanticAtom := { element := fluorineElement }
def chlorineAtom : SemanticAtom := { element := chlorineElement }


def alkeneMolecule : SemanticMolecule :=
  { atoms := [carbonAtom, carbonAtom, fluorineAtom, chlorineAtom, fluorineAtom, chlorineAtom]
    interactions :=
      [ { participants := [0, 1], kind := .covalent 2 }
      , { participants := [0, 2], kind := .covalent 1 }
      , { participants := [0, 3], kind := .covalent 1 }
      , { participants := [1, 4], kind := .covalent 1 }
      , { participants := [1, 5], kind := .covalent 1 } ] }

/-- One plain diagram bond. -/
def plainBond (source target : ℕ) : DiagramBond :=
  { source := source, target := target, style := .plain }

/-- A diagram with the actual positions and only plain bonds, no atom configurations. -/
def diagramOfPositions (positions : List CartesianPoint2) : DiagramConfiguration :=
  { atomPositions? := some positions
    bonds := [plainBond 0 1, plainBond 0 2, plainBond 0 3, plainBond 1 4, plainBond 1 5]
    atomConfigurations := [] }

/-- The diagram-only source: `spatial? = none`, actual diagram positions, no spatial lift. -/
def sourceOfPositions (positions : List CartesianPoint2) : AuthoritativeChemicalInput :=
  { molecule := alkeneMolecule, spatial? := none, diagram? := some (diagramOfPositions positions) }

/-- The base cis drawing. -/
def cisPositions : List CartesianPoint2 :=
  [pt 0 0, pt 2 0, pt (-1) (-1), pt (-1) 1, pt 3 (-1), pt 3 1]


def transPositions : List CartesianPoint2 :=
  [pt 0 0, pt 2 0, pt (-1) (-1), pt (-1) 1, pt 3 1, pt 3 (-1)]

/-- The refusal drawing: the selected right `Cl5` is collinear with the bond base. -/
def collinearPositions : List CartesianPoint2 :=
  [pt 0 0, pt 2 0, pt (-1) (-1), pt (-1) 1, pt 3 (-1), pt 3 0]

def sourceCis : AuthoritativeChemicalInput := sourceOfPositions cisPositions
def sourceTrans : AuthoritativeChemicalInput := sourceOfPositions transPositions
def sourceCollinear : AuthoritativeChemicalInput := sourceOfPositions collinearPositions

/-! ## Structural machinery: terminal branch keys and atomic-number separation -/

/-- When the exact Rule-1a projection of two compiled keys is already decisive, the rule trace
outcome is precisely that projection. -/
theorem exactCompareTrace_outcome_eq_rule1a_of_decisive {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (left right : ExactOfficialRuleMajorKey V)
    (decisive : OfficialRuleMajorKey.compareSparseLayers
        ExactOfficialRuleMajorKey.compareExactAtomicNumber
        (ExactOfficialRuleMajorKey.exactRule1aLayers m left.sourceNodes)
        (ExactOfficialRuleMajorKey.exactRule1aLayers m right.sourceNodes) ≠ Ordering.eq) :
    cipTraceOutcome (ExactOfficialRuleMajorKey.compareTrace m left right) =
      OfficialRuleMajorKey.compareSparseLayers
        ExactOfficialRuleMajorKey.compareExactAtomicNumber
        (ExactOfficialRuleMajorKey.exactRule1aLayers m left.sourceNodes)
        (ExactOfficialRuleMajorKey.exactRule1aLayers m right.sourceNodes) := by
  unfold ExactOfficialRuleMajorKey.compareTrace ExactOfficialRuleMajorKey.compareAddressedSourceTrace
  exact cipTraceOutcome_cons_decisive _ _ decisive

/-- Exact terminal vertex comparison: two terminal root branches are decided by their actual atomic
numbers, with the larger atomic number the strict senior.  This is proved from the exact Rule-1a
layer projection (`compareSparseExactRule1a_gt_of_heads_gt`) and the first-decisive-rule trace. -/
theorem exactCompare_terminalRootKey_gt {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (edgeAtom leftReference rightReference : V)
    (higher : m.atomZ rightReference < m.atomZ leftReference) :
    ExactOfficialRuleMajorKey.compare m
        (MoleculeGraph.exactOfficialRuleMajorRootKey
          (OfficialCIPNode.rootFromEdge edgeAtom leftReference) true)
        (MoleculeGraph.exactOfficialRuleMajorRootKey
          (OfficialCIPNode.rootFromEdge edgeAtom rightReference) true) = Ordering.gt := by
  have leftHead : (ExactOfficialRuleMajorKey.exactRule1aLayers m
        (MoleculeGraph.exactOfficialRuleMajorRootKey
          (OfficialCIPNode.rootFromEdge edgeAtom leftReference) true).sourceNodes).head? =
      some [([], DeclarativeCIP.ExactAtomicNumber.ofNat (m.atomZ leftReference))] := by
    rw [ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head m
      (MoleculeGraph.exactOfficialRuleMajorRootKey
        (OfficialCIPNode.rootFromEdge edgeAtom leftReference) true).sourceNodes
      (OfficialCIPNode.rootFromEdge edgeAtom leftReference) rfl]
    simp
  have rightHead : (ExactOfficialRuleMajorKey.exactRule1aLayers m
        (MoleculeGraph.exactOfficialRuleMajorRootKey
          (OfficialCIPNode.rootFromEdge edgeAtom rightReference) true).sourceNodes).head? =
      some [([], DeclarativeCIP.ExactAtomicNumber.ofNat (m.atomZ rightReference))] := by
    rw [ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head m
      (MoleculeGraph.exactOfficialRuleMajorRootKey
        (OfficialCIPNode.rootFromEdge edgeAtom rightReference) true).sourceNodes
      (OfficialCIPNode.rootFromEdge edgeAtom rightReference) rfl]
    simp
  have atomic := ExactOfficialRuleMajorKey.compareSparseExactRule1a_gt_of_heads_gt
    leftHead rightHead higher
  have decisive : OfficialRuleMajorKey.compareSparseLayers
      ExactOfficialRuleMajorKey.compareExactAtomicNumber
      (ExactOfficialRuleMajorKey.exactRule1aLayers m
        (MoleculeGraph.exactOfficialRuleMajorRootKey
          (OfficialCIPNode.rootFromEdge edgeAtom leftReference) true).sourceNodes)
      (ExactOfficialRuleMajorKey.exactRule1aLayers m
        (MoleculeGraph.exactOfficialRuleMajorRootKey
          (OfficialCIPNode.rootFromEdge edgeAtom rightReference) true).sourceNodes) ≠
        Ordering.eq := by
    rw [atomic]
    simp
  have outcome := ExactOfficialRuleMajorKey.compareTrace_outcome m
    (MoleculeGraph.exactOfficialRuleMajorRootKey
      (OfficialCIPNode.rootFromEdge edgeAtom leftReference) true)
    (MoleculeGraph.exactOfficialRuleMajorRootKey
      (OfficialCIPNode.rootFromEdge edgeAtom rightReference) true)
  rw [← outcome]
  rw [exactCompareTrace_outcome_eq_rule1a_of_decisive m
    (MoleculeGraph.exactOfficialRuleMajorRootKey
      (OfficialCIPNode.rootFromEdge edgeAtom leftReference) true)
    (MoleculeGraph.exactOfficialRuleMajorRootKey
      (OfficialCIPNode.rootFromEdge edgeAtom rightReference) true) decisive]
  exact atomic

/-- `List.Forall₂` against a pointwise map needs the property only on members. -/
theorem forall₂_map_of_mem {α β : Type*} (P : α → β → Prop) (f : α → β) :
    ∀ (l : List α), (∀ a, a ∈ l → P a (f a)) → List.Forall₂ P l (l.map f)
  | [], _ => List.Forall₂.nil
  | a :: l, h =>
      List.Forall₂.cons (h a (by simp))
        (forall₂_map_of_mem P f l fun b hb => h b (by simp [hb]))

/-- A leaf substituent's canonical branch key is its terminal root provenance tree. -/
theorem canonicalBranchKey_of_children_nil (source : AuthoritativeChemicalInput)
    (endpoint reference : source.AromaticCanonicalAtom)
    (empty : source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
        (OfficialCIPNode.rootFromEdge endpoint reference) = []) :
    source.CanonicalAromaticCanonicalRule3BranchKey endpoint reference
      (MoleculeGraph.exactOfficialRuleMajorRootKey
        (OfficialCIPNode.rootFromEdge endpoint reference) true) :=
  MoleculeGraph.CanonicalCompleteExactOfficialRuleMajorKey.terminal empty

/-! ## The actual ranked source branches -/

/-- The represented substituents of one endpoint, each compiled to its actual terminal branch. -/
noncomputable def rankedSubstituents (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    List source.AromaticCanonicalRule3RankedSubstituent :=
  (source.aromaticCanonicalRule3Substituents endpoint partner).map fun reference =>
    { atom := reference
      key := MoleculeGraph.exactOfficialRuleMajorRootKey
        (OfficialCIPNode.rootFromEdge endpoint reference) true }

/-- The represented constitutional neighbours of the left endpoint are exactly atoms 1, 2 and 3. -/
theorem adjacent_zero_iff (positions : List CartesianPoint2) :
    ∀ a : (sourceOfPositions positions).AromaticCanonicalAtom,
      (sourceOfPositions positions).AromaticCanonicalAdjacent ⟨0, by change 0 < 6; decide⟩ a ↔
        a = ⟨1, by change 1 < 6; decide⟩ ∨ a = ⟨2, by change 2 < 6; decide⟩ ∨ a = ⟨3, by change 3 < 6; decide⟩ := by
  change ∀ a : sourceCis.AromaticCanonicalAtom,
    sourceCis.AromaticCanonicalAdjacent ⟨0, by change 0 < 6; decide⟩ a ↔
      a = ⟨1, by change 1 < 6; decide⟩ ∨ a = ⟨2, by change 2 < 6; decide⟩ ∨ a = ⟨3, by change 3 < 6; decide⟩
  unfold AuthoritativeChemicalInput.AromaticCanonicalAdjacent
  decide +kernel

/-- The represented constitutional neighbours of the right endpoint are exactly atoms 0, 4 and 5. -/
theorem adjacent_one_iff (positions : List CartesianPoint2) :
    ∀ a : (sourceOfPositions positions).AromaticCanonicalAtom,
      (sourceOfPositions positions).AromaticCanonicalAdjacent ⟨1, by change 1 < 6; decide⟩ a ↔
        a = ⟨0, by change 0 < 6; decide⟩ ∨ a = ⟨4, by change 4 < 6; decide⟩ ∨ a = ⟨5, by change 5 < 6; decide⟩ := by
  change ∀ a : sourceCis.AromaticCanonicalAtom,
    sourceCis.AromaticCanonicalAdjacent ⟨1, by change 1 < 6; decide⟩ a ↔
      a = ⟨0, by change 0 < 6; decide⟩ ∨ a = ⟨4, by change 4 < 6; decide⟩ ∨ a = ⟨5, by change 5 < 6; decide⟩
  unfold AuthoritativeChemicalInput.AromaticCanonicalAdjacent
  decide +kernel


theorem children_nil_left (positions : List CartesianPoint2) :
    ∀ a, a ∈ (sourceOfPositions positions).aromaticCanonicalRule3Substituents
        ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩ →
      (sourceOfPositions positions).molecule.aromaticCanonicalOfficialCIPChildrenAt
        (sourceOfPositions positions).molecule.atomCount
        (OfficialCIPNode.rootFromEdge ⟨0, by change 0 < 6; decide⟩ a) = [] := by
  intro a present
  have adjacent := ((sourceOfPositions positions).mem_aromaticCanonicalRule3Substituents_iff
    ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩ a).mp present
  rcases (adjacent_zero_iff positions a).mp adjacent.1 with h | h | h
  · exact absurd h adjacent.2
  · rw [h]
    change alkeneMolecule.aromaticCanonicalOfficialCIPChildrenAt 6
      (OfficialCIPNode.rootFromEdge ⟨0, by decide⟩ ⟨2, by decide⟩) = []
    decide +kernel
  · rw [h]
    change alkeneMolecule.aromaticCanonicalOfficialCIPChildrenAt 6
      (OfficialCIPNode.rootFromEdge ⟨0, by decide⟩ ⟨3, by decide⟩) = []
    decide +kernel


theorem children_nil_right (positions : List CartesianPoint2) :
    ∀ a, a ∈ (sourceOfPositions positions).aromaticCanonicalRule3Substituents
        ⟨1, by change 1 < 6; decide⟩ ⟨0, by change 0 < 6; decide⟩ →
      (sourceOfPositions positions).molecule.aromaticCanonicalOfficialCIPChildrenAt
        (sourceOfPositions positions).molecule.atomCount
        (OfficialCIPNode.rootFromEdge ⟨1, by change 1 < 6; decide⟩ a) = [] := by
  intro a present
  have adjacent := ((sourceOfPositions positions).mem_aromaticCanonicalRule3Substituents_iff
    ⟨1, by change 1 < 6; decide⟩ ⟨0, by change 0 < 6; decide⟩ a).mp present
  rcases (adjacent_one_iff positions a).mp adjacent.1 with h | h | h
  · exact absurd h adjacent.2
  · rw [h]
    change alkeneMolecule.aromaticCanonicalOfficialCIPChildrenAt 6
      (OfficialCIPNode.rootFromEdge ⟨1, by decide⟩ ⟨4, by decide⟩) = []
    decide +kernel
  · rw [h]
    change alkeneMolecule.aromaticCanonicalOfficialCIPChildrenAt 6
      (OfficialCIPNode.rootFromEdge ⟨1, by decide⟩ ⟨5, by decide⟩) = []
    decide +kernel

/-! ## Derived strict canonical senior references -/


theorem rankedSubstituents_forall₂_left (positions : List CartesianPoint2) :
    List.Forall₂
      ((sourceOfPositions positions).CanonicalAromaticCanonicalRule3RankedSubstituent
        ⟨0, by change 0 < 6; decide⟩)
      ((sourceOfPositions positions).aromaticCanonicalRule3Substituents ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩)
      (rankedSubstituents (sourceOfPositions positions) ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩) := by
  unfold rankedSubstituents
  exact forall₂_map_of_mem
    ((sourceOfPositions positions).CanonicalAromaticCanonicalRule3RankedSubstituent ⟨0, by change 0 < 6; decide⟩)
    (fun reference : (sourceOfPositions positions).AromaticCanonicalAtom =>
      ({ atom := reference
         key := MoleculeGraph.exactOfficialRuleMajorRootKey
           (OfficialCIPNode.rootFromEdge ⟨0, by change 0 < 6; decide⟩ reference) true } :
        (sourceOfPositions positions).AromaticCanonicalRule3RankedSubstituent))
    ((sourceOfPositions positions).aromaticCanonicalRule3Substituents ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩)
    (fun a ha => ⟨rfl, canonicalBranchKey_of_children_nil (sourceOfPositions positions)
      ⟨0, by change 0 < 6; decide⟩ a (children_nil_left positions a ha)⟩)


theorem rankedSubstituents_forall₂_right (positions : List CartesianPoint2) :
    List.Forall₂
      ((sourceOfPositions positions).CanonicalAromaticCanonicalRule3RankedSubstituent
        ⟨1, by change 1 < 6; decide⟩)
      ((sourceOfPositions positions).aromaticCanonicalRule3Substituents ⟨1, by change 1 < 6; decide⟩ ⟨0, by change 0 < 6; decide⟩)
      (rankedSubstituents (sourceOfPositions positions) ⟨1, by change 1 < 6; decide⟩ ⟨0, by change 0 < 6; decide⟩) := by
  unfold rankedSubstituents
  exact forall₂_map_of_mem
    ((sourceOfPositions positions).CanonicalAromaticCanonicalRule3RankedSubstituent ⟨1, by change 1 < 6; decide⟩)
    (fun reference : (sourceOfPositions positions).AromaticCanonicalAtom =>
      ({ atom := reference
         key := MoleculeGraph.exactOfficialRuleMajorRootKey
           (OfficialCIPNode.rootFromEdge ⟨1, by change 1 < 6; decide⟩ reference) true } :
        (sourceOfPositions positions).AromaticCanonicalRule3RankedSubstituent))
    ((sourceOfPositions positions).aromaticCanonicalRule3Substituents ⟨1, by change 1 < 6; decide⟩ ⟨0, by change 0 < 6; decide⟩)
    (fun a ha => ⟨rfl, canonicalBranchKey_of_children_nil (sourceOfPositions positions)
      ⟨1, by change 1 < 6; decide⟩ a (children_nil_right positions a ha)⟩)



theorem canonicalSeniorReference_left (positions : List CartesianPoint2) :
    (sourceOfPositions positions).CanonicalAromaticCanonicalRule3ConstitutionalSeniorReference
      ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩ ⟨3, by change 3 < 6; decide⟩ := by
  refine ⟨rankedSubstituents (sourceOfPositions positions) ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩,
    { atom := ⟨3, by change 3 < 6; decide⟩
      key := MoleculeGraph.exactOfficialRuleMajorRootKey
        (OfficialCIPNode.rootFromEdge ⟨0, by change 0 < 6; decide⟩ ⟨3, by change 3 < 6; decide⟩) true },
    rankedSubstituents_forall₂_left positions, ?_, rfl⟩
  refine ⟨?_, ?_⟩
  · unfold rankedSubstituents
    exact List.mem_map.mpr ⟨⟨3, by change 3 < 6; decide⟩,
      ((sourceOfPositions positions).mem_aromaticCanonicalRule3Substituents_iff
        ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩ ⟨3, by change 3 < 6; decide⟩).mpr
        ⟨by
          change sourceCis.AromaticCanonicalAdjacent ⟨0, by decide⟩ ⟨3, by decide⟩
          unfold AuthoritativeChemicalInput.AromaticCanonicalAdjacent
          decide +kernel, by
          change (3 : Fin 6) ≠ 1
          decide⟩, rfl⟩
  · intro other hother different
    unfold rankedSubstituents at hother
    rcases List.mem_map.mp hother with ⟨a, ha, rfl⟩
    have adjacent := ((sourceOfPositions positions).mem_aromaticCanonicalRule3Substituents_iff
      ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩ a).mp ha
    have notSenior : a ≠ ⟨3, by change 3 < 6; decide⟩ := different
    rcases (adjacent_zero_iff positions a).mp adjacent.1 with h | h | h
    · exact absurd h adjacent.2
    · rw [h]
      exact exactCompare_terminalRootKey_gt
        (sourceOfPositions positions).molecule.toLocalizedMoleculeGraph
        ⟨0, by change 0 < 6; decide⟩ ⟨3, by change 3 < 6; decide⟩ ⟨2, by change 2 < 6; decide⟩ (by change 9 < 17; decide)
    · exact absurd h notSenior



theorem canonicalSeniorReference_right (positions : List CartesianPoint2) :
    (sourceOfPositions positions).CanonicalAromaticCanonicalRule3ConstitutionalSeniorReference
      ⟨1, by change 1 < 6; decide⟩ ⟨0, by change 0 < 6; decide⟩ ⟨5, by change 5 < 6; decide⟩ := by
  refine ⟨rankedSubstituents (sourceOfPositions positions) ⟨1, by change 1 < 6; decide⟩ ⟨0, by change 0 < 6; decide⟩,
    { atom := ⟨5, by change 5 < 6; decide⟩
      key := MoleculeGraph.exactOfficialRuleMajorRootKey
        (OfficialCIPNode.rootFromEdge ⟨1, by change 1 < 6; decide⟩ ⟨5, by change 5 < 6; decide⟩) true },
    rankedSubstituents_forall₂_right positions, ?_, rfl⟩
  refine ⟨?_, ?_⟩
  · unfold rankedSubstituents
    exact List.mem_map.mpr ⟨⟨5, by change 5 < 6; decide⟩,
      ((sourceOfPositions positions).mem_aromaticCanonicalRule3Substituents_iff
        ⟨1, by change 1 < 6; decide⟩ ⟨0, by change 0 < 6; decide⟩ ⟨5, by change 5 < 6; decide⟩).mpr
        ⟨by
          change sourceCis.AromaticCanonicalAdjacent ⟨1, by decide⟩ ⟨5, by decide⟩
          unfold AuthoritativeChemicalInput.AromaticCanonicalAdjacent
          decide +kernel, by
          change (5 : Fin 6) ≠ 0
          decide⟩, rfl⟩
  · intro other hother different
    unfold rankedSubstituents at hother
    rcases List.mem_map.mp hother with ⟨a, ha, rfl⟩
    have adjacent := ((sourceOfPositions positions).mem_aromaticCanonicalRule3Substituents_iff
      ⟨1, by change 1 < 6; decide⟩ ⟨0, by change 0 < 6; decide⟩ a).mp ha
    have notSenior : a ≠ ⟨5, by change 5 < 6; decide⟩ := different
    rcases (adjacent_one_iff positions a).mp adjacent.1 with h | h | h
    · exact absurd h adjacent.2
    · rw [h]
      exact exactCompare_terminalRootKey_gt
        (sourceOfPositions positions).molecule.toLocalizedMoleculeGraph
        ⟨1, by change 1 < 6; decide⟩ ⟨5, by change 5 < 6; decide⟩ ⟨4, by change 4 < 6; decide⟩ (by change 9 < 17; decide)
    · exact absurd h notSenior

/-- The strict left senior reference selector returns the actual `Cl3`. -/
theorem seniorReference_left (positions : List CartesianPoint2) :
    (sourceOfPositions positions).aromaticCanonicalRule3ConstitutionalSeniorReference?
        ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩ = some ⟨3, by change 3 < 6; decide⟩ :=
  ((sourceOfPositions positions).aromaticCanonicalRule3ConstitutionalSeniorReference?_eq_some_iff_canonical
    ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩ ⟨3, by change 3 < 6; decide⟩).mpr (canonicalSeniorReference_left positions)

/-- The strict right senior reference selector returns the actual `Cl5`. -/
theorem seniorReference_right (positions : List CartesianPoint2) :
    (sourceOfPositions positions).aromaticCanonicalRule3ConstitutionalSeniorReference?
        ⟨1, by change 1 < 6; decide⟩ ⟨0, by change 0 < 6; decide⟩ = some ⟨5, by change 5 < 6; decide⟩ :=
  ((sourceOfPositions positions).aromaticCanonicalRule3ConstitutionalSeniorReference?_eq_some_iff_canonical
    ⟨1, by change 1 < 6; decide⟩ ⟨0, by change 0 < 6; decide⟩ ⟨5, by change 5 < 6; decide⟩).mpr (canonicalSeniorReference_right positions)

/-! ## The actual diagram positions and the closed reader outputs -/

/-- The actual diagram point lookup is the actual position-list entry at the atom index. -/
theorem planarPointAt?_sourceOfPositions (positions : List CartesianPoint2)
    (atom : (sourceOfPositions positions).AromaticCanonicalAtom) :
    aromaticCanonicalPlanarPointAt? (sourceOfPositions positions) atom = positions[atom.val]? :=
  rfl

/-- The base source is structurally well formed: valid index lists, plain in-range bonds. -/
theorem sourceCis_structurallyWellFormed : sourceCis.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff sourceCis).mp (by decide +kernel)

/-- All three literal six-atom sources satisfy actual source structural admission. -/
theorem all_variants_structurallyWellFormed :
    sourceCis.StructurallyWellFormed ∧ sourceTrans.StructurallyWellFormed ∧
      sourceCollinear.StructurallyWellFormed :=
  ⟨sourceCis_structurallyWellFormed,
    (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff sourceTrans).mp (by decide +kernel),
    (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff sourceCollinear).mp (by decide +kernel)⟩

/-- The source owns six actual atoms, five interactions and exactly the supplied drawing channel. -/
theorem actual_source_shape (positions : List CartesianPoint2) :
    (sourceOfPositions positions).molecule.atomCount = 6 ∧
      (sourceOfPositions positions).molecule.interactions.length = 5 ∧
      (sourceOfPositions positions).spatial? = none ∧
      (sourceOfPositions positions).diagram? = some (diagramOfPositions positions) ∧
      (diagramOfPositions positions).atomConfigurations = [] := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The actual base source has no three-dimensional channel: `spatial? = none`. -/
theorem sourceCis_spatial?_eq_none : sourceCis.spatial? = none := rfl

/-- The actual base source has an ordinary double bond at the drawn base `C0=C1`. -/
theorem ordinaryDoubleBond (positions : List CartesianPoint2) :
    (sourceOfPositions positions).AromaticCanonicalOrdinaryDoubleBond ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩ := by
  change sourceCis.AromaticCanonicalOrdinaryDoubleBond ⟨0, by decide⟩ ⟨1, by decide⟩
  unfold AuthoritativeChemicalInput.AromaticCanonicalOrdinaryDoubleBond
    AuthoritativeChemicalInput.AromaticCanonicalAdjacent
  decide +kernel

/-- The cis drawing emits `seqcis` from the actual positions, references and diagram channel. -/
theorem sourceCis_emits_seqcis :
    aromaticCanonicalPlanarRule3Unit? sourceCis ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩ =
      some { leftReference := ⟨3, by change 3 < 6; decide⟩
             rightReference := ⟨5, by change 5 < 6; decide⟩
             geometry := OfficialRule3Geometry.seqcis } := by
  refine (aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical sourceCis
    ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩ _).mpr ?_
  refine ⟨ordinaryDoubleBond cisPositions,
    canonicalSeniorReference_left cisPositions,
    canonicalSeniorReference_right cisPositions,
    pt 0 0, pt 2 0, pt (-1) 1, pt 3 1, ?_, ?_, ?_, ?_, ?_⟩
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff sourceCis ⟨0, by change 0 < 6; decide⟩ (pt 0 0)).mp
      (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff sourceCis ⟨1, by change 1 < 6; decide⟩ (pt 2 0)).mp
      (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff sourceCis ⟨3, by change 3 < 6; decide⟩ (pt (-1) 1)).mp
      (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff sourceCis ⟨5, by change 5 < 6; decide⟩ (pt 3 1)).mp
      (by decide +kernel)
  · exact Or.inl ⟨rfl, by norm_num [SameSide, planarDirectedArea, pt]⟩

/-- The trans drawing (right `F/Cl` positions exchanged) emits `seqtrans`. -/
theorem sourceTrans_emits_seqtrans :
    aromaticCanonicalPlanarRule3Unit? sourceTrans ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩ =
      some { leftReference := ⟨3, by change 3 < 6; decide⟩
             rightReference := ⟨5, by change 5 < 6; decide⟩
             geometry := OfficialRule3Geometry.seqtrans } := by
  refine (aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical sourceTrans
    ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩ _).mpr ?_
  refine ⟨ordinaryDoubleBond transPositions,
    canonicalSeniorReference_left transPositions,
    canonicalSeniorReference_right transPositions,
    pt 0 0, pt 2 0, pt (-1) 1, pt 3 (-1), ?_, ?_, ?_, ?_, ?_⟩
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff sourceTrans ⟨0, by change 0 < 6; decide⟩ (pt 0 0)).mp
      (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff sourceTrans ⟨1, by change 1 < 6; decide⟩ (pt 2 0)).mp
      (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff sourceTrans ⟨3, by change 3 < 6; decide⟩ (pt (-1) 1)).mp
      (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff sourceTrans ⟨5, by change 5 < 6; decide⟩ (pt 3 (-1))).mp
      (by decide +kernel)
  · exact Or.inr ⟨rfl, by norm_num [OppositeSide, planarDirectedArea, pt]⟩

/-- The collinear drawing places the selected right `Cl5` on the bond base, so the reader refuses. -/
theorem sourceCollinear_refuses :
    aromaticCanonicalPlanarRule3Unit? sourceCollinear ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩ = none := by
  refine aromaticCanonicalPlanarRule3Unit?_eq_none_of_collinear sourceCollinear
    ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩ ⟨3, by change 3 < 6; decide⟩ ⟨5, by change 5 < 6; decide⟩
    (pt 0 0) (pt 2 0) (pt (-1) 1) (pt 3 0)
    (ordinaryDoubleBond collinearPositions)
    (seniorReference_left collinearPositions)
    (seniorReference_right collinearPositions)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Or.inr (by decide +kernel))

/-! ## The old three-dimensional reader refuses without a spatial channel -/

/-- A source with no spatial channel refuses the three-dimensional reader at every endpoint; no
coordinate is invented and no spatial lift is fabricated. -/
theorem spatialUnit?_eq_none_of_spatial?_eq_none (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom) (absent : source.spatial? = none) :
    source.aromaticCanonicalRule3SpatialUnit? left right = none := by
  rw [source.aromaticCanonicalRule3SpatialUnit?_eq_none_iff_no_canonical]
  rintro ⟨result, canonical⟩
  obtain ⟨_, _, _, leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
    leftPointDerived, _, _, _, _⟩ := canonical
  obtain ⟨spatial, spatialComputed, _⟩ := leftPointDerived
  rw [absent] at spatialComputed
  exact absurd spatialComputed (by simp)

/-- The actual base source refuses the old three-dimensional reader at the drawn base. -/
theorem sourceCis_spatialUnit_refuses :
    sourceCis.aromaticCanonicalRule3SpatialUnit? ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩ = none :=
  spatialUnit?_eq_none_of_spatial?_eq_none sourceCis ⟨0, by change 0 < 6; decide⟩ ⟨1, by change 1 < 6; decide⟩ rfl

end TetraStereo.UniversalProof.SourceNativePlanarAlkeneWitnessProofs.SourceNativePlanarAlkeneWitness
