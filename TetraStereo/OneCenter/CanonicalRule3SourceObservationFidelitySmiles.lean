import TetraStereo.OneCenter.CanonicalRule3SourceObservationFidelity
import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace RawMolecule

/-!
# SMILES instantiation of Rule-3 source-observation fidelity

This staged module instantiates the generic source-binding theorem of
`CanonicalRule3SourceObservationFidelity` with the green Rule-3 source-observation API:

* `children := ChemistryNormalizationResult.rule3BranchChildren mol center`
* `observe := ChemistryNormalizationResult.rule3BranchObserver result mol center policy ligand`
* root `canonicalRoot center ligand`
* compiled key `ChemistryNormalizationResult.compileRule3HierarchyKey?` /
  `compileRule3HierarchyKeyComplete?`.

It also unpacks the observer's positive result: the stored observation carries exactly the physical
`Rule3SourceUnit` key, near/far endpoints and recorded entry, the source node is a real atom whose
incoming parent–atom edge is the double bond, the addressed occurrence is not policy-excluded, the
unit is not structurally inapplicable, and the geometry is the center geometry with only the
documented non-cyclic transport flip.

Finally it records the refusal-versus-inapplicability distinction: `some none` is a determinate
absence (non-source, excluded occurrence, or structurally inapplicable unit), while `none` is
unknown evidence for an applicable, non-excluded source unit and must propagate as a refusal.

**Integration gate.**  The current main `SmilesTetrahedral` still carries the old flat Rule-3
semantics.  This module references the supplied green candidate API (b01cbc3b) and must be
integrated only after that candidate replaces the old file.  It establishes source binding, not
universal chemical validity of policy flips or exclusions.
-/

/-! ## Unpacking the source unit recorded by a node -/

/-- A successful `rule3SourceUnitOfNode?` read exposes the real-node conditions and the exact
parent/atom/history fields it records. -/
theorem rule3SourceUnitOfNode?_some_fields
    {mol : RawMolecule} {center : ℕ} {node : CanonicalBranchNode}
    {unit : ChemistryNormalizationResult.Rule3SourceUnit}
    (computed : ChemistryNormalizationResult.rule3SourceUnitOfNode? mol center node = some unit) :
    node.provenance = CanonicalNodeProvenance.realAtom ∧
      node.atom ≠ center ∧ node.parent ≠ center ∧
      mol.bondOrder node.parent node.atom = 2 ∧
      unit.near = node.parent ∧ unit.far = node.atom ∧
      unit.entry? = (node.history.drop 2).head? := by
  unfold ChemistryNormalizationResult.rule3SourceUnitOfNode? at computed
  split at computed
  · rename_i conditions
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, and_assoc] at conditions
    rcases conditions with ⟨provenanceEq, atomNe, parentNe, bondEq⟩
    have unitEq := Option.some.inj computed
    subst unit
    exact ⟨provenanceEq, atomNe, parentNe, bondEq, rfl, rfl, rfl⟩
  · cases computed

/-! ## Unpacking a positive observation -/

/-- Every `some (some value)` returned by the source-bound observer exposes the actual unit read
from the real node, the policy decisions, and the geometry provenance of `value`. -/
theorem rule3BranchObserver_some_some_unpacked
    {result : ChemistryNormalizationResult} {mol : RawMolecule}
    {center ligand : ℕ}
    {policy : ChemistryNormalizationResult.Rule3CenterPolicy}
    {node : CanonicalBranchNode} {value : CanonicalRule3Observation}
    (observed : ChemistryNormalizationResult.rule3BranchObserver
      result mol center policy ligand node = some (some value)) :
    ∃ unit : ChemistryNormalizationResult.Rule3SourceUnit,
      ChemistryNormalizationResult.rule3SourceUnitOfNode? mol center node = some unit ∧
      node.provenance = CanonicalNodeProvenance.realAtom ∧
      node.atom ≠ center ∧ node.parent ≠ center ∧
      mol.bondOrder node.parent node.atom = 2 ∧
      unit.near = node.parent ∧ unit.far = node.atom ∧
      unit.entry? = (node.history.drop 2).head? ∧
      value.unit = unit.key ∧
      value.near = unit.near ∧
      value.far = unit.far ∧
      value.entry? = unit.entry? ∧
      policy.excluded.contains (unit.addressedKey ligand) = false ∧
      ChemistryNormalizationResult.rule3UnitStructurallyInapplicable mol unit = false ∧
      ∃ geometry : OfficialRule3Geometry,
        ChemistryNormalizationResult.rule3CenterGeometry? result mol center
            (ChemistryNormalizationResult.rule3CenterTetrahedral mol center)
            policy.cyclic unit = some geometry ∧
        value.geometry =
          (if policy.flipped.contains ligand && !policy.cyclic
            then ChemistryNormalizationResult.flipRule3Geometry geometry
            else geometry) := by
  unfold ChemistryNormalizationResult.rule3BranchObserver at observed
  cases sourceUnit : ChemistryNormalizationResult.rule3SourceUnitOfNode? mol center node with
  | none =>
      rw [sourceUnit] at observed
      cases observed
  | some unit =>
      rw [sourceUnit] at observed
      try dsimp at observed
      by_cases excluded : policy.excluded.contains (unit.addressedKey ligand) = true
      · rw [if_pos excluded] at observed
        cases observed
      · rw [if_neg excluded] at observed
        try dsimp at observed
        by_cases inapplicable :
            ChemistryNormalizationResult.rule3UnitStructurallyInapplicable mol unit = true
        · rw [if_pos inapplicable] at observed
          cases observed
        · rw [if_neg inapplicable] at observed
          try dsimp at observed
          cases geometryComputed : ChemistryNormalizationResult.rule3CenterGeometry?
              result mol center
              (ChemistryNormalizationResult.rule3CenterTetrahedral mol center)
              policy.cyclic unit with
          | none =>
              rw [geometryComputed] at observed
              try dsimp at observed
              cases observed
          | some geometry =>
              rw [geometryComputed] at observed
              try dsimp at observed
              have valueEq := Option.some.inj (Option.some.inj observed)
              subst value
              obtain ⟨provenanceEq, atomNe, parentNe, bondEq, nearEq, farEq, entryEq⟩ :=
                rule3SourceUnitOfNode?_some_fields sourceUnit
              have excludedFalse :
                  policy.excluded.contains (unit.addressedKey ligand) = false :=
                Bool.eq_false_iff.mpr excluded
              have inapplicableFalse :
                  ChemistryNormalizationResult.rule3UnitStructurallyInapplicable mol unit =
                    false :=
                Bool.eq_false_iff.mpr inapplicable
              exact ⟨unit, rfl, provenanceEq, atomNe, parentNe, bondEq,
                nearEq, farEq, entryEq, rfl, rfl, rfl, rfl,
                excludedFalse, inapplicableFalse, geometry, geometryComputed, rfl⟩

/-! ## Source binding through the production compiler -/

/-- Every addressed observation stored by `compileRule3HierarchyKey?` comes from a reachable real
source node of the ligand's canonical branch tree, and the supplied observer returned exactly that
observation there. -/
theorem compileRule3HierarchyKey?_observation_source
    {result : ChemistryNormalizationResult} {mol : RawMolecule}
    {center ligand fuel : ℕ}
    {policy : ChemistryNormalizationResult.Rule3CenterPolicy}
    {key : CanonicalRule3Key}
    (computed : ChemistryNormalizationResult.compileRule3HierarchyKey?
      result mol center ligand fuel policy = some key)
    {addr : List ℕ} {value : CanonicalRule3Observation}
    (mem : ObservationEntryMem key.observations addr value) :
    ∃ source : CanonicalBranchNode,
      SourceReachable (ChemistryNormalizationResult.rule3BranchChildren mol center)
        (canonicalRoot center ligand) source ∧
      ChemistryNormalizationResult.rule3BranchObserver result mol center policy ligand source =
        some (some value) := by
  unfold ChemistryNormalizationResult.compileRule3HierarchyKey? at computed
  exact buildCanonicalRule3Key?_observation_source fuel (canonicalRoot center ligand) key computed mem

/-- Source binding through `compileRule3HierarchyKeyComplete?`, which additionally requires the
compiled constitutional key to be complete. -/
theorem compileRule3HierarchyKeyComplete?_observation_source
    {result : ChemistryNormalizationResult} {mol : RawMolecule}
    {center ligand fuel : ℕ}
    {policy : ChemistryNormalizationResult.Rule3CenterPolicy}
    {key : CanonicalRule3Key}
    (computed : ChemistryNormalizationResult.compileRule3HierarchyKeyComplete?
      result mol center ligand fuel policy = some key)
    {addr : List ℕ} {value : CanonicalRule3Observation}
    (mem : ObservationEntryMem key.observations addr value) :
    ∃ source : CanonicalBranchNode,
      SourceReachable (ChemistryNormalizationResult.rule3BranchChildren mol center)
        (canonicalRoot center ligand) source ∧
      ChemistryNormalizationResult.rule3BranchObserver result mol center policy ligand source =
        some (some value) := by
  unfold ChemistryNormalizationResult.compileRule3HierarchyKeyComplete? at computed
  cases inner : ChemistryNormalizationResult.compileRule3HierarchyKey?
      result mol center ligand fuel policy with
  | none =>
      rw [inner] at computed
      dsimp at computed
      cases computed
  | some compiledKey =>
      rw [inner] at computed
      dsimp at computed
      by_cases complete : compiledKey.constitutional.complete = true
      · rw [if_pos complete] at computed
        have keyEq : compiledKey = key := by
          simpa using computed
        subst key
        exact compileRule3HierarchyKey?_observation_source inner mem
      · rw [if_neg complete] at computed
        cases computed

/-- Full unpacked source binding: a stored addressed observation of a successfully completed key
is the observer's own value at a reachable real source node, with the physical unit, near/far
endpoints, recorded entry, policy decisions and geometry provenance all exposed. -/
theorem compileRule3HierarchyKeyComplete?_observation_source_unpacked
    {result : ChemistryNormalizationResult} {mol : RawMolecule}
    {center ligand fuel : ℕ}
    {policy : ChemistryNormalizationResult.Rule3CenterPolicy}
    {key : CanonicalRule3Key}
    (computed : ChemistryNormalizationResult.compileRule3HierarchyKeyComplete?
      result mol center ligand fuel policy = some key)
    {addr : List ℕ} {value : CanonicalRule3Observation}
    (mem : ObservationEntryMem key.observations addr value) :
    ∃ source : CanonicalBranchNode,
      ∃ unit : ChemistryNormalizationResult.Rule3SourceUnit,
        SourceReachable (ChemistryNormalizationResult.rule3BranchChildren mol center)
          (canonicalRoot center ligand) source ∧
        ChemistryNormalizationResult.rule3SourceUnitOfNode? mol center source = some unit ∧
        ChemistryNormalizationResult.rule3BranchObserver result mol center policy ligand source =
          some (some value) ∧
        source.provenance = CanonicalNodeProvenance.realAtom ∧
        source.atom ≠ center ∧ source.parent ≠ center ∧
        mol.bondOrder source.parent source.atom = 2 ∧
        unit.near = source.parent ∧ unit.far = source.atom ∧
        unit.entry? = (source.history.drop 2).head? ∧
        value.unit = unit.key ∧
        value.near = unit.near ∧
        value.far = unit.far ∧
        value.entry? = unit.entry? ∧
        policy.excluded.contains (unit.addressedKey ligand) = false ∧
        ChemistryNormalizationResult.rule3UnitStructurallyInapplicable mol unit = false ∧
        ∃ geometry : OfficialRule3Geometry,
          ChemistryNormalizationResult.rule3CenterGeometry? result mol center
              (ChemistryNormalizationResult.rule3CenterTetrahedral mol center)
              policy.cyclic unit = some geometry ∧
          value.geometry =
            (if policy.flipped.contains ligand && !policy.cyclic
              then ChemistryNormalizationResult.flipRule3Geometry geometry
              else geometry) := by
  obtain ⟨source, reachable, observedSource⟩ :=
    compileRule3HierarchyKeyComplete?_observation_source computed mem
  obtain ⟨unit, sourceUnit, provenanceEq, atomNe, parentNe, bondEq, nearEq, farEq,
    entryEq, unitEq, nearValueEq, farValueEq, entryValueEq, excludedFalse,
    inapplicableFalse, geometry, geometryComputed, geometryEq⟩ :=
    rule3BranchObserver_some_some_unpacked observedSource
  exact ⟨source, unit, reachable, sourceUnit, observedSource, provenanceEq, atomNe,
    parentNe, bondEq, nearEq, farEq, entryEq, unitEq, nearValueEq, farValueEq,
    entryValueEq, excludedFalse, inapplicableFalse, geometry, geometryComputed, geometryEq⟩

/-! ## Generated policies preserve the selected source-reference geometry -/

/-- A positive observation under the actual generated policy keeps the geometry returned by
its source reader.  This states provenance, without assuming that a change of reference occurred. -/
theorem rule3BranchObserver_generated_policy_geometry
    {result : ChemistryNormalizationResult} {mol : RawMolecule}
    {center ligand : ℕ} {node : CanonicalBranchNode} {value : CanonicalRule3Observation}
    (observed : ChemistryNormalizationResult.rule3BranchObserver result mol center
      (ChemistryNormalizationResult.rule3CenterPolicy result mol center) ligand node =
        some (some value)) :
    ∃ unit : ChemistryNormalizationResult.Rule3SourceUnit,
      ChemistryNormalizationResult.rule3SourceUnitOfNode? mol center node = some unit ∧
      value.unit = unit.key ∧ value.near = unit.near ∧ value.far = unit.far ∧
      value.entry? = unit.entry? ∧
      ChemistryNormalizationResult.rule3CenterGeometry? result mol center
        (ChemistryNormalizationResult.rule3CenterTetrahedral mol center)
        (ChemistryNormalizationResult.rule3CenterPolicy result mol center).cyclic unit =
          some value.geometry := by
  obtain ⟨unit, sourceUnit, _provenance, _atomNe, _parentNe, _bondEq,
    _nearEq, _farEq, _entryEq, unitEq, nearValueEq, farValueEq, entryValueEq,
    _excluded, _inapplicable, geometry, geometryComputed, geometryEq⟩ :=
    rule3BranchObserver_some_some_unpacked observed
  have same : value.geometry = geometry := by simpa using geometryEq
  exact ⟨unit, sourceUnit, unitEq, nearValueEq, farValueEq, entryValueEq,
    by simpa only [same] using geometryComputed⟩

/-- Every stored observation of a completed production key is a reachable source observation
whose geometry is preserved by the generated center policy. -/
theorem compileRule3HierarchyKeyComplete?_generated_policy_geometry
    {result : ChemistryNormalizationResult} {mol : RawMolecule}
    {center ligand fuel : ℕ} {key : CanonicalRule3Key}
    (computed : ChemistryNormalizationResult.compileRule3HierarchyKeyComplete?
      result mol center ligand fuel
      (ChemistryNormalizationResult.rule3CenterPolicy result mol center) = some key)
    {addr : List ℕ} {value : CanonicalRule3Observation}
    (mem : ObservationEntryMem key.observations addr value) :
    ∃ source : CanonicalBranchNode,
      ∃ unit : ChemistryNormalizationResult.Rule3SourceUnit,
        SourceReachable (ChemistryNormalizationResult.rule3BranchChildren mol center)
          (canonicalRoot center ligand) source ∧
        ChemistryNormalizationResult.rule3SourceUnitOfNode? mol center source = some unit ∧
        value.unit = unit.key ∧ value.near = unit.near ∧ value.far = unit.far ∧
        value.entry? = unit.entry? ∧
        ChemistryNormalizationResult.rule3CenterGeometry? result mol center
          (ChemistryNormalizationResult.rule3CenterTetrahedral mol center)
          (ChemistryNormalizationResult.rule3CenterPolicy result mol center).cyclic unit =
            some value.geometry := by
  obtain ⟨source, reachable, observed⟩ :=
    compileRule3HierarchyKeyComplete?_observation_source computed mem
  obtain ⟨unit, sourceUnit, unitEq, nearEq, farEq, entryEq, geometry⟩ :=
    rule3BranchObserver_generated_policy_geometry observed
  exact ⟨source, unit, reachable, sourceUnit, unitEq, nearEq, farEq, entryEq, geometry⟩

/-! ## Refusal versus determinate absence -/

/-- A non-source node is a determinate absence (`some none`), never an unknown observation. -/
theorem rule3BranchObserver_some_none_of_not_source
    {result : ChemistryNormalizationResult} {mol : RawMolecule}
    {center ligand : ℕ}
    {policy : ChemistryNormalizationResult.Rule3CenterPolicy}
    {node : CanonicalBranchNode}
    (notSource : ChemistryNormalizationResult.rule3SourceUnitOfNode? mol center node = none) :
    ChemistryNormalizationResult.rule3BranchObserver result mol center policy ligand node =
      some none := by
  unfold ChemistryNormalizationResult.rule3BranchObserver
  rw [notSource]

/-- A policy-excluded addressed occurrence is a determinate absence (`some none`). -/
theorem rule3BranchObserver_some_none_of_excluded
    {result : ChemistryNormalizationResult} {mol : RawMolecule}
    {center ligand : ℕ}
    {policy : ChemistryNormalizationResult.Rule3CenterPolicy}
    {node : CanonicalBranchNode}
    {unit : ChemistryNormalizationResult.Rule3SourceUnit}
    (sourceUnit : ChemistryNormalizationResult.rule3SourceUnitOfNode? mol center node = some unit)
    (excluded : policy.excluded.contains (unit.addressedKey ligand) = true) :
    ChemistryNormalizationResult.rule3BranchObserver result mol center policy ligand node =
      some none := by
  unfold ChemistryNormalizationResult.rule3BranchObserver
  rw [sourceUnit]
  try dsimp
  rw [if_pos excluded]

/-- A structurally inapplicable unit is a determinate absence (`some none`). -/
theorem rule3BranchObserver_some_none_of_structurally_inapplicable
    {result : ChemistryNormalizationResult} {mol : RawMolecule}
    {center ligand : ℕ}
    {policy : ChemistryNormalizationResult.Rule3CenterPolicy}
    {node : CanonicalBranchNode}
    {unit : ChemistryNormalizationResult.Rule3SourceUnit}
    (sourceUnit : ChemistryNormalizationResult.rule3SourceUnitOfNode? mol center node = some unit)
    (notExcluded : policy.excluded.contains (unit.addressedKey ligand) = false)
    (inapplicable :
      ChemistryNormalizationResult.rule3UnitStructurallyInapplicable mol unit = true) :
    ChemistryNormalizationResult.rule3BranchObserver result mol center policy ligand node =
      some none := by
  unfold ChemistryNormalizationResult.rule3BranchObserver
  rw [sourceUnit]
  try dsimp
  rw [if_neg (Bool.eq_false_iff.mp notExcluded)]
  try dsimp
  rw [if_pos inapplicable]

/-- **Refusal is not inapplicability.**  For an applicable, non-excluded source unit whose
center-mode geometry is missing, the observer returns `none` (unknown evidence that must propagate
as a refusal), never `some none`. -/
theorem rule3BranchObserver_none_of_unknown_geometry
    {result : ChemistryNormalizationResult} {mol : RawMolecule}
    {center ligand : ℕ}
    {policy : ChemistryNormalizationResult.Rule3CenterPolicy}
    {node : CanonicalBranchNode}
    {unit : ChemistryNormalizationResult.Rule3SourceUnit}
    (sourceUnit : ChemistryNormalizationResult.rule3SourceUnitOfNode? mol center node = some unit)
    (notExcluded : policy.excluded.contains (unit.addressedKey ligand) = false)
    (applicable :
      ChemistryNormalizationResult.rule3UnitStructurallyInapplicable mol unit = false)
    (geometryMissing : ChemistryNormalizationResult.rule3CenterGeometry?
      result mol center
      (ChemistryNormalizationResult.rule3CenterTetrahedral mol center)
      policy.cyclic unit = none) :
    ChemistryNormalizationResult.rule3BranchObserver result mol center policy ligand node =
      none := by
  unfold ChemistryNormalizationResult.rule3BranchObserver
  rw [sourceUnit]
  try dsimp
  rw [if_neg (Bool.eq_false_iff.mp notExcluded)]
  try dsimp
  rw [if_neg (Bool.eq_false_iff.mp applicable)]
  try dsimp
  cases geometryComputed : ChemistryNormalizationResult.rule3CenterGeometry?
      result mol center
      (ChemistryNormalizationResult.rule3CenterTetrahedral mol center)
      policy.cyclic unit with
  | none => rfl
  | some geometry =>
      rw [geometryMissing] at geometryComputed
      cases geometryComputed

/- Kernel trust checks for every theorem in this module. -/
assert_kernel_only rule3SourceUnitOfNode?_some_fields
assert_kernel_only ChemistryNormalizationResult.rule3CenterPolicy_flipped
assert_kernel_only rule3BranchObserver_generated_policy_geometry
assert_kernel_only compileRule3HierarchyKeyComplete?_generated_policy_geometry
assert_kernel_only rule3BranchObserver_some_some_unpacked
assert_kernel_only compileRule3HierarchyKey?_observation_source
assert_kernel_only compileRule3HierarchyKeyComplete?_observation_source
assert_kernel_only compileRule3HierarchyKeyComplete?_observation_source_unpacked
assert_kernel_only rule3BranchObserver_some_none_of_not_source
assert_kernel_only rule3BranchObserver_some_none_of_excluded
assert_kernel_only rule3BranchObserver_some_none_of_structurally_inapplicable
assert_kernel_only rule3BranchObserver_none_of_unknown_geometry

end RawMolecule
end OneCenter
end TetraStereo
