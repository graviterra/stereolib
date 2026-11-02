import TetraStereo.OneCenter.ProductionCIPCarrier
import TetraStereo.OneCenter.CanonicalRule3Hierarchy
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

/-!
# Production Rules 3--5 semantic bridge

This module identifies production descriptor domains with the independent declarative domains and
begins the executable soundness bridge with opponent-independent Rule-3 and Rule-4b keys.

Rule 3 is no longer read through a separate flat priority list.  A production key stores the
complete compiled `RawMolecule.CanonicalRule3Key` together with a proof that its observation
evidence is aligned with its compared priority projection.  The declarative Rule-3 signature is a
derived projection of that compiled key, and the live trace compares the compiled sparse priority
layers.  This module proves the two readings agree.
-/

/-! ## Exact primitive-domain translations -/

def OfficialRule3Geometry.toDeclarative : OfficialRule3Geometry → Rule3Geometry
  | .seqcis => .seqCis
  | .seqtrans => .seqTrans
  | .nonstereogenic => .nonstereogenic

def OfficialStereogenicUnitKind.toDeclarative :
    OfficialStereogenicUnitKind → StereogenicUnitKind
  | .chiral => .chiral
  | .pseudoasymmetric => .pseudoasymmetric
  | .nonstereogenic => .nonstereogenic

def OfficialDescriptorSense.toDeclarative : OfficialDescriptorSense → DescriptorSense
  | .senior => .senior
  | .junior => .junior

def OfficialDescriptorPairKind.toDeclarative :
    OfficialDescriptorPairKind → DescriptorPairKind
  | .like => .like
  | .unlike => .unlike

def OfficialPseudoasymmetricDescriptor.toDeclarative :
    OfficialPseudoasymmetricDescriptor → Rule4cDescriptor
  | .r => ⟨PseudoDescriptorFamily.tetrahedral, .senior⟩
  | .s => ⟨PseudoDescriptorFamily.tetrahedral, .junior⟩
  | .m => ⟨PseudoDescriptorFamily.axialOrPlanar, .senior⟩
  | .p => ⟨PseudoDescriptorFamily.axialOrPlanar, .junior⟩

def OfficialRule5DescriptorKind.toDeclarative :
    OfficialRule5DescriptorKind → Rule5DescriptorKind
  | .tetrahedralCenter => .tetrahedralCenter
  | .axisOrPlane => .axisOrPlane
  | .doubleBondOrCumulene => .doubleBondOrCumulene

def OfficialRule5Descriptor.toDeclarative (descriptor : OfficialRule5Descriptor) :
    Rule5Descriptor :=
  { kind := descriptor.kind.toDeclarative
    auxiliary := descriptor.auxiliary
    sense := descriptor.sense.toDeclarative }

theorem descendingNatOutcome_lt_iff (left right : ℕ) :
    DescendingNatOutcome left right Ordering.lt ↔ left < right := by
  constructor
  · intro h
    cases h with
    | lt h => exact h
  · exact DescendingNatOutcome.lt

theorem descendingNatOutcome_eq_iff (left right : ℕ) :
    DescendingNatOutcome left right Ordering.eq ↔ left = right := by
  constructor
  · intro h
    cases h with
    | eq h => exact h
  · exact DescendingNatOutcome.eq

theorem descendingNatOutcome_gt_iff (left right : ℕ) :
    DescendingNatOutcome left right Ordering.gt ↔ right < left := by
  constructor
  · intro h
    cases h with
    | gt h => exact h
  · exact DescendingNatOutcome.gt

theorem comparePriorityNat_eq_iff_descendingNatOutcome
    (left right : ℕ) (outcome : Ordering) :
    CIPRuleEngine.comparePriorityNat left right = outcome ↔
      DescendingNatOutcome left right outcome := by
  cases outcome <;>
    simp only [descendingNatOutcome_lt_iff, descendingNatOutcome_eq_iff,
      descendingNatOutcome_gt_iff] <;>
    by_cases hleft : left < right <;>
    by_cases hright : right < left <;>
    simp [CIPRuleEngine.comparePriorityNat, hleft, hright] <;> omega

theorem OfficialRule3Geometry.compare_eq_iff_declarativeOutcome
    (left right : OfficialRule3Geometry) (outcome : Ordering) :
    OfficialRule3Geometry.compare left right = outcome ↔
      Rule3Geometry.Outcome left.toDeclarative right.toDeclarative outcome := by
  unfold OfficialRule3Geometry.compare Rule3Geometry.Outcome PriorityOutcome
  rw [comparePriorityNat_eq_iff_descendingNatOutcome]
  cases left <;> cases right <;> rfl

theorem OfficialStereogenicUnitKind.compare_eq_iff_declarativeOutcome
    (left right : OfficialStereogenicUnitKind) (outcome : Ordering) :
    OfficialStereogenicUnitKind.compare left right = outcome ↔
      StereogenicUnitKind.Outcome left.toDeclarative right.toDeclarative outcome := by
  unfold OfficialStereogenicUnitKind.compare StereogenicUnitKind.Outcome PriorityOutcome
  rw [comparePriorityNat_eq_iff_descendingNatOutcome]
  cases left <;> cases right <;> rfl

theorem OfficialDescriptorPairKind.compare_eq_iff_declarativePriority
    (left right : OfficialDescriptorPairKind) (outcome : Ordering) :
    OfficialDescriptorPairKind.compare left right = outcome ↔
      PriorityOutcome DescriptorPairKind.priority left.toDeclarative right.toDeclarative outcome := by
  unfold OfficialDescriptorPairKind.compare PriorityOutcome
  rw [comparePriorityNat_eq_iff_descendingNatOutcome]
  cases left <;> cases right <;> rfl

theorem OfficialPseudoasymmetricDescriptor.compare?_eq_iff_declarativeOutcome
    (left right : OfficialPseudoasymmetricDescriptor) (outcome : Ordering) :
    OfficialPseudoasymmetricDescriptor.compare? left right = some outcome ↔
      Rule4cDescriptor.Outcome left.toDeclarative right.toDeclarative outcome := by
  cases left <;> cases right <;> cases outcome <;>
    simp [OfficialPseudoasymmetricDescriptor.compare?,
      OfficialPseudoasymmetricDescriptor.toDeclarative,
      Rule4cDescriptor.Outcome, PriorityOutcome, DescriptorSense.priority,
      descendingNatOutcome_lt_iff, descendingNatOutcome_eq_iff,
      descendingNatOutcome_gt_iff]

theorem OfficialRule5Descriptor.compare?_eq_iff_declarativeOutcome
    (left right : OfficialRule5Descriptor) (outcome : Ordering) :
    OfficialRule5Descriptor.compare? left right = some outcome ↔
      Rule5Descriptor.Outcome left.toDeclarative right.toDeclarative outcome := by
  rcases left with ⟨leftKind, leftAuxiliary, leftSense⟩
  rcases right with ⟨rightKind, rightAuxiliary, rightSense⟩
  cases leftKind <;> cases rightKind <;> cases leftAuxiliary <;> cases rightAuxiliary <;>
    cases leftSense <;> cases rightSense <;> cases outcome <;>
    simp [OfficialRule5Descriptor.compare?, OfficialDescriptorSense.compare,
      OfficialRule5Descriptor.toDeclarative, OfficialRule5DescriptorKind.toDeclarative,
      OfficialDescriptorSense.toDeclarative, Rule5Descriptor.Outcome, PriorityOutcome,
      DescriptorSense.priority, descendingNatOutcome_lt_iff, descendingNatOutcome_eq_iff,
      descendingNatOutcome_gt_iff]

/-! ## Rule 3: compiled observations versus the derived declarative projection -/

/-- The official Rule-3 priority and the declarative Rule-3 priority agree after translation. -/
theorem officialRule3Geometry_priority_toDeclarative (geometry : OfficialRule3Geometry) :
    Rule3Geometry.priority geometry.toDeclarative = OfficialRule3Geometry.priority geometry := by
  cases geometry <;> rfl

/-- Generic lexicographic-comparison congruence under two elementwise maps.

This is the reusable form of the Rule-3 projection argument: it does not assume that the two
maps agree syntactically, only that the mapped entry comparators do. -/
theorem list_compareLex_map_map_congr {α β γ : Type*}
    (compareSource : β → β → Ordering) (compareTarget : γ → γ → Ordering)
    (sourceMap : α → β) (targetMap : α → γ)
    (entryAgreement : ∀ left right,
      compareSource (sourceMap left) (sourceMap right) =
        compareTarget (targetMap left) (targetMap right)) :
    ∀ (left right : List α),
      List.compareLex compareSource (left.map sourceMap) (right.map sourceMap) =
        List.compareLex compareTarget (left.map targetMap) (right.map targetMap)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | leftHead :: leftTail, rightHead :: rightTail => by
      simp only [List.map_cons, List.compareLex_cons_cons, entryAgreement,
        list_compareLex_map_map_congr compareSource compareTarget sourceMap targetMap
          entryAgreement leftTail rightTail]

/-- Binding a constant-`none` continuation always refuses. -/
theorem option_bind_const_none_eq {α β : Type*} (option : Option α) :
    option.bind (fun _ => (none : Option β)) = none := by
  cases option <;> rfl

/-- The identity-key numeric comparator is the bare numeric comparator. -/
theorem ordering_byKey_id_compare_eq :
    Ordering.byKey id compare = (compare : ℕ → ℕ → Ordering) := rfl

/-- One compiled observation entry, projected to its addressed declarative geometry. -/
def RawMolecule.CanonicalRule3Observation.declarativeEntry
    (entry : List ℕ × RawMolecule.CanonicalRule3Observation) :
    List ℕ × Rule3Geometry :=
  (entry.1, entry.2.geometry.toDeclarative)

/-- One compiled observation entry, projected to its addressed numeric priority. -/
def RawMolecule.CanonicalRule3Observation.priorityEntry
    (entry : List ℕ × RawMolecule.CanonicalRule3Observation) :
    List ℕ × ℕ :=
  (entry.1, entry.2.priority)

/-- Addressed declarative layers derived from the stored observation evidence. -/
def RawMolecule.CanonicalRule3Key.declarativeLayers
    (key : RawMolecule.CanonicalRule3Key) :
    AddressedHierarchy Rule3Geometry :=
  key.observations.map fun layer => layer.map RawMolecule.CanonicalRule3Observation.declarativeEntry

/-- The priority projection of the stored observation evidence, in addressed form. -/
theorem mapObservationPriorityLayers_eq_map
    (layers : List (List (List ℕ × RawMolecule.CanonicalRule3Observation))) :
    RawMolecule.mapObservationPriorityLayers layers =
      layers.map fun layer =>
        layer.map RawMolecule.CanonicalRule3Observation.priorityEntry := by
  rfl

/-- Entry comparison is unchanged by the declarative projection and by alignment with the stored
priority projection. -/
theorem compareAddressedEntry_observations
    (left right : List ℕ × RawMolecule.CanonicalRule3Observation) :
    compareAddressedEntry Rule3Geometry.priority
        (RawMolecule.CanonicalRule3Observation.declarativeEntry left)
        (RawMolecule.CanonicalRule3Observation.declarativeEntry right) =
      compareAddressedEntry id
        (RawMolecule.CanonicalRule3Observation.priorityEntry left)
        (RawMolecule.CanonicalRule3Observation.priorityEntry right) := by
  simp only [RawMolecule.CanonicalRule3Observation.declarativeEntry,
    RawMolecule.CanonicalRule3Observation.priorityEntry,
    compareAddressedEntry, Ordering.byKey, compareLex,
    RawMolecule.CanonicalRule3Observation.priority,
    officialRule3Geometry_priority_toDeclarative, id]

/-- Layer comparison is unchanged by the declarative projection. -/
theorem compareAddressedLayer_observations
    (left right : List (List ℕ × RawMolecule.CanonicalRule3Observation)) :
    compareAddressedLayer Rule3Geometry.priority
        (left.map RawMolecule.CanonicalRule3Observation.declarativeEntry)
        (right.map RawMolecule.CanonicalRule3Observation.declarativeEntry) =
      compareAddressedLayer id
        (left.map RawMolecule.CanonicalRule3Observation.priorityEntry)
        (right.map RawMolecule.CanonicalRule3Observation.priorityEntry) := by
  simpa only [compareAddressedLayer] using
    list_compareLex_map_map_congr (compareAddressedEntry Rule3Geometry.priority)
      (compareAddressedEntry id)
      RawMolecule.CanonicalRule3Observation.declarativeEntry
      RawMolecule.CanonicalRule3Observation.priorityEntry
      compareAddressedEntry_observations left right

/-- Whole-hierarchy comparison is unchanged by the declarative projection. -/
theorem compareAddressedHierarchy_observations
    (left right : List (List (List ℕ × RawMolecule.CanonicalRule3Observation))) :
    compareAddressedHierarchy Rule3Geometry.priority
        (left.map fun layer =>
          layer.map RawMolecule.CanonicalRule3Observation.declarativeEntry)
        (right.map fun layer =>
          layer.map RawMolecule.CanonicalRule3Observation.declarativeEntry) =
      compareAddressedHierarchy id
        (left.map fun layer =>
          layer.map RawMolecule.CanonicalRule3Observation.priorityEntry)
        (right.map fun layer =>
          layer.map RawMolecule.CanonicalRule3Observation.priorityEntry) := by
  simpa only [compareAddressedHierarchy] using
    list_compareLex_map_map_congr (compareAddressedLayer Rule3Geometry.priority)
      (compareAddressedLayer id)
      (fun layer => layer.map RawMolecule.CanonicalRule3Observation.declarativeEntry)
      (fun layer => layer.map RawMolecule.CanonicalRule3Observation.priorityEntry)
      compareAddressedLayer_observations left right

/-- The derived declarative Rule-3 comparison is exactly the compiled sparse priority comparison. -/
theorem compareAddressedHierarchy_declarativeLayers_eq_compiled
    (left right : RawMolecule.CanonicalRule3Key)
    (leftAligned : left.Rule3Aligned) (rightAligned : right.Rule3Aligned) :
    compareAddressedHierarchy Rule3Geometry.priority left.declarativeLayers
        right.declarativeLayers =
      RawMolecule.compareSparseCanonicalLayers compare left.rule3 right.rule3 := by
  unfold RawMolecule.CanonicalRule3Key.declarativeLayers
  rw [compareAddressedHierarchy_observations]
  change compareAddressedHierarchy id
      (RawMolecule.mapObservationPriorityLayers left.observations)
      (RawMolecule.mapObservationPriorityLayers right.observations) =
    RawMolecule.compareSparseCanonicalLayers compare left.rule3 right.rule3
  unfold RawMolecule.CanonicalRule3Key.Rule3Aligned at leftAligned rightAligned
  rw [leftAligned, rightAligned]
  simp only [compareAddressedHierarchy, compareAddressedLayer, compareAddressedEntry,
    RawMolecule.compareSparseCanonicalLayers, RawMolecule.compareSparseCanonicalLayer,
    RawMolecule.compareSparseCanonicalEntry, compareSemanticAddress,
    RawMolecule.compareCanonicalPath, ordering_byKey_id_compare_eq]

/-! ## The exact production Rules 3--5 key and trace -/

/-- One production ligand's opponent-independent data for all ordinary stereochemical rules.

The Rule-3 component is the complete compiled canonical hierarchy, not a separately recomputed flat
list.  `rule3Aligned` records that its observation evidence projects exactly to the compared
priority layers, which is derived during compilation.  Construction is option-valued because Rule
4a may still be waiting for an annotated stereogenic center, or the Rule-3 hierarchy may be
incomplete; such a missing earlier-rule observation is a refusal, not a tie. -/
structure ProductionRules35Key where
  rule3Key : RawMolecule.CanonicalRule3Key
  rule3Aligned : rule3Key.Rule3Aligned
  rule4a : List (List (List ℕ × OfficialStereogenicUnitKind))
  rule4b : List (List ℕ)
  rule4c : List (List (List ℕ × ℕ))
  rule5 : List (List (List ℕ × ℕ))

noncomputable instance ProductionRules35Key.instDecidableEq :
    DecidableEq ProductionRules35Key :=
  Classical.decEq _

instance ProductionRules35Key.instRepr : Repr ProductionRules35Key where
  reprPrec key _ :=
    "{" ++ "rule3Key := " ++ repr key.rule3Key ++
      ", rule4a := " ++ repr key.rule4a ++
      ", rule4b := " ++ repr key.rule4b ++
      ", rule4c := " ++ repr key.rule4c ++
      ", rule5 := " ++ repr key.rule5 ++ "}"

/-- The declarative Rule-3 signature derived from the compiled observations.

Addresses are preserved verbatim; only the geometry label is translated to its declarative twin.
This is a projection of the live compiled key, not an independent parallel semantics. -/
def ProductionRules35Key.rule3 (key : ProductionRules35Key) : Rule3Signature :=
  { layers := key.rule3Key.declarativeLayers }

/-- Every complete compiled Rule-3 key is aligned with its priority projection. -/
theorem compileRule3HierarchyKeyComplete?_rule3Aligned
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (center ligand fuel : ℕ) (policy : ChemistryNormalizationResult.Rule3CenterPolicy)
    {key : RawMolecule.CanonicalRule3Key}
    (computed : ChemistryNormalizationResult.compileRule3HierarchyKeyComplete?
      result mol center ligand fuel policy = some key) :
    key.Rule3Aligned := by
  unfold ChemistryNormalizationResult.compileRule3HierarchyKeyComplete? at computed
  cases compiled : ChemistryNormalizationResult.compileRule3HierarchyKey?
      result mol center ligand fuel policy with
  | none =>
      rw [compiled] at computed
      simp only [Option.bind_none] at computed
      cases computed
  | some compiledKey =>
      rw [compiled] at computed
      simp only [Option.bind_some] at computed
      by_cases complete : compiledKey.constitutional.complete = true
      · rw [if_pos complete] at computed
        cases computed
        unfold ChemistryNormalizationResult.compileRule3HierarchyKey? at compiled
        exact RawMolecule.buildCanonicalRule3Key?_rule3Aligned mol
          (ChemistryNormalizationResult.rule3BranchChildren mol center)
          (ChemistryNormalizationResult.rule3BranchObserver result mol center policy ligand)
          fuel (RawMolecule.canonicalRoot center ligand) key compiled
      · rw [if_neg complete] at computed
        cases computed

/-- Attach an alignment proof to whichever complete key a raw compile returned.

The equation is carried by `Option.attach`, so the dependent proof stays inside this opaque
combinator instead of appearing in downstream case splits. -/
def attachAlignedRule3Key (compiled : Option RawMolecule.CanonicalRule3Key)
    (align : ∀ key, compiled = some key → key.Rule3Aligned) :
    Option { key : RawMolecule.CanonicalRule3Key // key.Rule3Aligned } :=
  compiled.attach.map fun keyWithEquation =>
    ⟨keyWithEquation.1, align keyWithEquation.1 keyWithEquation.2⟩

/-- A refused compile yields no aligned key. -/
theorem attachAlignedRule3Key_none (compiled : Option RawMolecule.CanonicalRule3Key)
    (align : ∀ key, compiled = some key → key.Rule3Aligned)
    (h : compiled = none) :
    attachAlignedRule3Key compiled align = none := by
  revert h
  revert align
  cases compiled with
  | none =>
      intro align h
      rfl
  | some key =>
      intro align h
      cases h

/-- A successful compile yields its key together with the requested alignment proof. -/
theorem attachAlignedRule3Key_some (compiled : Option RawMolecule.CanonicalRule3Key)
    (align : ∀ key, compiled = some key → key.Rule3Aligned)
    {key : RawMolecule.CanonicalRule3Key} (h : compiled = some key) :
    attachAlignedRule3Key compiled align = some ⟨key, align key h⟩ := by
  revert h
  revert align
  cases compiled with
  | none =>
      intro align h
      cases h
  | some compiledKey =>
      intro align h
      have hkey : compiledKey = key := by simpa using h
      cases hkey
      simp only [attachAlignedRule3Key, Option.attach_some, Option.map_some]

/-- Compile one ligand and retain the proof that its observations are aligned with its compared
Rule-3 priorities. -/
def compileAlignedRule3Key? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (center ligand fuel : ℕ) (policy : ChemistryNormalizationResult.Rule3CenterPolicy) :
    Option { key : RawMolecule.CanonicalRule3Key // key.Rule3Aligned } :=
  attachAlignedRule3Key
    (ChemistryNormalizationResult.compileRule3HierarchyKeyComplete?
      result mol center ligand fuel policy)
    (fun _key h => compileRule3HierarchyKeyComplete?_rule3Aligned
      result mol center ligand fuel policy h)

/-- Compile one ligand into the exact unary data read by the production Rules 3--5 trace. -/
def productionRules35Key? (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center ligand : ℕ) : Option ProductionRules35Key :=
  (branchRule4aSparseLayers mol state center ligand).bind fun rule4a =>
    (compileAlignedRule3Key? result mol center ligand
      (2 * mol.atomCount + 2) (result.rule3CenterPolicy mol center)).bind fun rule3 =>
      some
        { rule3Key := rule3.1
          rule3Aligned := rule3.2
          rule4a
          rule4b := rule4bCanonicalSignature (branchDescriptorLayers mol state center ligand)
          rule4c := branchRule4cSparseLayers mol state center ligand
          rule5 := branchRule5SparseLayers mol state center ligand }

/-- A missing Rule-4a observation refuses the production key. -/
theorem productionRules35Key?_eq_none_of_rule4a_none
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center ligand : ℕ)
    (hrule4a : branchRule4aSparseLayers mol state center ligand = none) :
    productionRules35Key? result mol state center ligand = none := by
  unfold productionRules35Key?
  rw [hrule4a]
  rfl

/-- A refused Rule-3 compile refuses the production key. -/
theorem productionRules35Key?_eq_none_of_compile_none
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center ligand : ℕ)
    {rule4a : List (List (List ℕ × OfficialStereogenicUnitKind))}
    (hrule4a : branchRule4aSparseLayers mol state center ligand = some rule4a)
    (hcompile : ChemistryNormalizationResult.compileRule3HierarchyKeyComplete?
      result mol center ligand (2 * mol.atomCount + 2)
      (result.rule3CenterPolicy mol center) = none) :
    productionRules35Key? result mol state center ligand = none := by
  unfold productionRules35Key? compileAlignedRule3Key?
  rw [hrule4a]
  simp only [Option.bind_some]
  rw [attachAlignedRule3Key_none
    (ChemistryNormalizationResult.compileRule3HierarchyKeyComplete?
      result mol center ligand (2 * mol.atomCount + 2)
      (result.rule3CenterPolicy mol center))
    (fun key h => compileRule3HierarchyKeyComplete?_rule3Aligned
      result mol center ligand (2 * mol.atomCount + 2)
      (result.rule3CenterPolicy mol center) h)
    hcompile]
  rfl

/-- A successful Rule-3 compile yields the production key with the derived alignment proof. -/
theorem productionRules35Key?_eq_some_of_compile
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center ligand : ℕ)
    {rule4a : List (List (List ℕ × OfficialStereogenicUnitKind))}
    {key : RawMolecule.CanonicalRule3Key}
    (hrule4a : branchRule4aSparseLayers mol state center ligand = some rule4a)
    (hcompile : ChemistryNormalizationResult.compileRule3HierarchyKeyComplete?
      result mol center ligand (2 * mol.atomCount + 2)
      (result.rule3CenterPolicy mol center) = some key) :
    productionRules35Key? result mol state center ligand =
      some
        { rule3Key := key
          rule3Aligned := compileRule3HierarchyKeyComplete?_rule3Aligned
            result mol center ligand (2 * mol.atomCount + 2)
            (result.rule3CenterPolicy mol center) hcompile
          rule4a := rule4a
          rule4b := rule4bCanonicalSignature (branchDescriptorLayers mol state center ligand)
          rule4c := branchRule4cSparseLayers mol state center ligand
          rule5 := branchRule5SparseLayers mol state center ligand } := by
  unfold productionRules35Key? compileAlignedRule3Key?
  rw [hrule4a]
  simp only [Option.bind_some]
  rw [attachAlignedRule3Key_some
    (ChemistryNormalizationResult.compileRule3HierarchyKeyComplete?
      result mol center ligand (2 * mol.atomCount + 2)
      (result.rule3CenterPolicy mol center))
    (fun key h => compileRule3HierarchyKeyComplete?_rule3Aligned
      result mol center ligand (2 * mol.atomCount + 2)
      (result.rule3CenterPolicy mol center) h)
    hcompile]
  rfl

/-- The five official decisions obtained solely by comparing two compiled unary keys.

Rule 3 reads the actual sparse compiled priorities of the complete addressed hierarchy. -/
def ProductionRules35Key.compareTrace
    (left right : ProductionRules35Key) : List CIPRuleDecision :=
  [ { rule := CIPRuleFamily.doubleBondGeometry
      outcome := RawMolecule.compareSparseCanonicalLayers compare
        left.rule3Key.rule3 right.rule3Key.rule3 }
  , { rule := CIPRuleFamily.stereogenicUnitKind
      outcome := RawMolecule.compareSparseCanonicalLayers OfficialStereogenicUnitKind.compare
        left.rule4a right.rule4a }
  , { rule := CIPRuleFamily.likeUnlikeDescriptorPair
      outcome := compare left.rule4b right.rule4b }
  , { rule := CIPRuleFamily.pseudoasymmetricDescriptor
      outcome := RawMolecule.compareSparseCanonicalLayers compare left.rule4c right.rule4c }
  , { rule := CIPRuleFamily.pseudoasymmetricTiebreak
      outcome := RawMolecule.compareSparseCanonicalLayers compare left.rule5 right.rule5 }
  ]

/-- The first-decisive production Rules 3--5 outcome on two complete unary keys. -/
def ProductionRules35Key.compareOutcome
    (left right : ProductionRules35Key) : Ordering :=
  cipTraceOutcome (left.compareTrace right)

/-- The declarative Rule-3 outcome of the derived signature is exactly the compiled sparse
priority comparison used by the live production trace. -/
theorem ProductionRules35Key.rule3_outcome_iff_compiled
    (left right : ProductionRules35Key) (outcome : Ordering) :
    Rule3Signature.Outcome left.rule3 right.rule3 outcome ↔
      RawMolecule.compareSparseCanonicalLayers compare
        left.rule3Key.rule3 right.rule3Key.rule3 = outcome := by
  simp only [Rule3Signature.Outcome, ProductionRules35Key.rule3,
    compareAddressedHierarchy_declarativeLayers_eq_compiled
      left.rule3Key right.rule3Key left.rule3Aligned right.rule3Aligned]

/-- Every key produced by the live production constructor carries aligned Rule-3 evidence. -/
theorem productionRules35Key?_rule3Aligned
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center ligand : ℕ) {key : ProductionRules35Key}
    (_computed : productionRules35Key? result mol state center ligand = some key) :
    key.rule3Key.Rule3Aligned :=
  key.rule3Aligned

/-- The live production trace is exactly key comparison, including refusal behavior. -/
theorem compareRawOfficialSequences_eq_keyTrace
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center left right : ℕ) :
    compareRawOfficialSequences result mol state center left right = (do
      let leftKey ← productionRules35Key? result mol state center left
      let rightKey ← productionRules35Key? result mol state center right
      return leftKey.compareTrace rightKey : Option (List CIPRuleDecision)) := by
  unfold compareRawOfficialSequences
    ChemistryNormalizationResult.compareRule3GeometryAtCenter?
    ChemistryNormalizationResult.compareRule3GeometryWithPolicy?
  cases hleft4a : branchRule4aSparseLayers mol state center left with
  | none =>
      rw [productionRules35Key?_eq_none_of_rule4a_none
        result mol state center left hleft4a]
      rfl
  | some leftRule4a =>
      cases hright4a : branchRule4aSparseLayers mol state center right with
      | none =>
          rw [productionRules35Key?_eq_none_of_rule4a_none
            result mol state center right hright4a]
          cases productionRules35Key? result mol state center left <;> rfl
      | some rightRule4a =>
          cases hleftKey : ChemistryNormalizationResult.compileRule3HierarchyKeyComplete?
              result mol center left (2 * mol.atomCount + 2)
              (result.rule3CenterPolicy mol center) with
          | none =>
              simp only [Option.bind_none]
              rw [productionRules35Key?_eq_none_of_compile_none
                result mol state center left hleft4a hleftKey]
              rfl
          | some leftKey =>
              cases hrightKey : ChemistryNormalizationResult.compileRule3HierarchyKeyComplete?
                  result mol center right (2 * mol.atomCount + 2)
                  (result.rule3CenterPolicy mol center) with
              | none =>
                  simp only [Option.bind_some, Option.bind_none]
                  rw [productionRules35Key?_eq_none_of_compile_none
                    result mol state center right hright4a hrightKey]
                  cases productionRules35Key? result mol state center left <;> rfl
              | some rightKey =>
                  simp only [Option.bind_some]
                  rw [productionRules35Key?_eq_some_of_compile
                    result mol state center left hleft4a hleftKey]
                  rw [productionRules35Key?_eq_some_of_compile
                    result mol state center right hright4a hrightKey]
                  rfl

/-! ## Global order laws for the production Rules 3--5 trace -/

theorem comparePriorityNat_eq_compare (left right : ℕ) :
    CIPRuleEngine.comparePriorityNat left right = compare left right := by
  cases hcompare : compare left right with
  | lt =>
      have hlt : left < right := Nat.compare_eq_lt.mp hcompare
      exact CIPRuleEngine.comparePriorityNat_eq_lt_of_lt hlt
  | eq =>
      have heq : left = right := Nat.compare_eq_eq.mp hcompare
      exact CIPRuleEngine.comparePriorityNat_eq_eq_of_eq heq
  | gt =>
      have hgt : right < left := Nat.compare_eq_gt.mp hcompare
      exact CIPRuleEngine.comparePriorityNat_eq_gt_of_lt hgt

private local instance officialStereogenicUnitKindCompareTrans :
    Std.TransCmp OfficialStereogenicUnitKind.compare := by
  letI : Std.TransCmp (Ordering.byKey OfficialStereogenicUnitKind.priority compare) :=
    inferInstance
  refine { eq_swap := ?_, isLE_trans := ?_ }
  · intro left right
    simpa only [OfficialStereogenicUnitKind.compare, comparePriorityNat_eq_compare,
      Ordering.byKey] using
      (Std.OrientedCmp.eq_swap
        (cmp := Ordering.byKey OfficialStereogenicUnitKind.priority compare)
        (a := left) (b := right))
  · intro first second third hfirst hsecond
    simp only [OfficialStereogenicUnitKind.compare, comparePriorityNat_eq_compare] at hfirst hsecond ⊢
    exact Std.TransCmp.isLE_trans hfirst hsecond

private local instance canonicalPathCompareTrans :
    Std.TransCmp RawMolecule.compareCanonicalPath := by
  unfold RawMolecule.compareCanonicalPath
  infer_instance

private local instance sparseEntryCompareTrans {α : Type*}
    (compareLabel : α → α → Ordering) [Std.TransCmp compareLabel] :
    Std.TransCmp (RawMolecule.compareSparseCanonicalEntry compareLabel) := by
  unfold RawMolecule.compareSparseCanonicalEntry
  infer_instance

private local instance sparseLayerCompareTrans {α : Type*}
    (compareLabel : α → α → Ordering) [Std.TransCmp compareLabel] :
    Std.TransCmp (RawMolecule.compareSparseCanonicalLayer compareLabel) := by
  unfold RawMolecule.compareSparseCanonicalLayer
  infer_instance

private local instance sparseLayersCompareTrans {α : Type*}
    (compareLabel : α → α → Ordering) [Std.TransCmp compareLabel] :
    Std.TransCmp (RawMolecule.compareSparseCanonicalLayers compareLabel) := by
  unfold RawMolecule.compareSparseCanonicalLayers
  infer_instance

/-- The same five comparisons as the emitted trace, assembled with the library's lawful
lexicographic-comparator combinator. -/
def ProductionRules35Key.lawfulCompare
    (left right : ProductionRules35Key) : Ordering :=
  compareLex
    (Ordering.byKey (fun key : ProductionRules35Key => key.rule3Key.rule3)
      (RawMolecule.compareSparseCanonicalLayers compare))
    (compareLex
      (Ordering.byKey ProductionRules35Key.rule4a
        (RawMolecule.compareSparseCanonicalLayers OfficialStereogenicUnitKind.compare))
      (compareLex
        (Ordering.byKey ProductionRules35Key.rule4b compare)
        (compareLex
          (Ordering.byKey ProductionRules35Key.rule4c
            (RawMolecule.compareSparseCanonicalLayers compare))
          (Ordering.byKey ProductionRules35Key.rule5
            (RawMolecule.compareSparseCanonicalLayers compare))))) left right

theorem ProductionRules35Key.compareOutcome_eq_lawfulCompare
    (left right : ProductionRules35Key) :
    left.compareOutcome right = left.lawfulCompare right := by
  cases hrule3 : RawMolecule.compareSparseCanonicalLayers compare
      left.rule3Key.rule3 right.rule3Key.rule3 <;>
  cases hrule4a : RawMolecule.compareSparseCanonicalLayers
      OfficialStereogenicUnitKind.compare left.rule4a right.rule4a <;>
  cases hrule4b : compare left.rule4b right.rule4b <;>
  cases hrule4c : RawMolecule.compareSparseCanonicalLayers compare left.rule4c right.rule4c <;>
  cases hrule5 : RawMolecule.compareSparseCanonicalLayers compare left.rule5 right.rule5 <;>
  simp [ProductionRules35Key.compareOutcome, ProductionRules35Key.compareTrace,
    ProductionRules35Key.lawfulCompare, cipTraceOutcome, compareLex, Ordering.byKey,
    Ordering.then, hrule3, hrule4a, hrule4b, hrule4c, hrule5]

theorem ProductionRules35Key.lawfulCompare_transCmp :
    Std.TransCmp ProductionRules35Key.lawfulCompare := by
  unfold ProductionRules35Key.lawfulCompare
  infer_instance

/-- The actual first-decisive Rules 3--5 trace is an oriented transitive comparator on every
successfully compiled production key. -/
theorem ProductionRules35Key.compareOutcome_transCmp :
    Std.TransCmp ProductionRules35Key.compareOutcome := by
  letI : Std.TransCmp ProductionRules35Key.lawfulCompare := lawfulCompare_transCmp
  refine { eq_swap := ?_, isLE_trans := ?_ }
  · intro left right
    simp only [compareOutcome_eq_lawfulCompare]
    exact Std.OrientedCmp.eq_swap
  · intro first second third hfirst hsecond
    simp only [compareOutcome_eq_lawfulCompare] at hfirst hsecond ⊢
    exact Std.TransCmp.isLE_trans hfirst hsecond

theorem ProductionRules35Key.compareOutcome_eq_refl (key : ProductionRules35Key) :
    key.compareOutcome key = Ordering.eq := by
  letI : Std.TransCmp ProductionRules35Key.compareOutcome := compareOutcome_transCmp
  exact Std.ReflCmp.compare_self

theorem ProductionRules35Key.compareOutcome_eq_trans
    {first second third : ProductionRules35Key}
    (hfirst : first.compareOutcome second = Ordering.eq)
    (hsecond : second.compareOutcome third = Ordering.eq) :
    first.compareOutcome third = Ordering.eq := by
  letI : Std.TransCmp ProductionRules35Key.compareOutcome := compareOutcome_transCmp
  exact Std.TransCmp.eq_trans hfirst hsecond

theorem ProductionRules35Key.compareOutcome_gt_trans
    {first second third : ProductionRules35Key}
    (hfirst : first.compareOutcome second = Ordering.gt)
    (hsecond : second.compareOutcome third = Ordering.gt) :
    first.compareOutcome third = Ordering.gt := by
  letI : Std.TransCmp ProductionRules35Key.compareOutcome := compareOutcome_transCmp
  exact Std.TransCmp.gt_trans hfirst hsecond

theorem ProductionRules35Key.compareOutcome_gt_eq_trans
    {first second third : ProductionRules35Key}
    (hfirst : first.compareOutcome second = Ordering.gt)
    (hsecond : second.compareOutcome third = Ordering.eq) :
    first.compareOutcome third = Ordering.gt := by
  letI : Std.TransCmp ProductionRules35Key.compareOutcome := compareOutcome_transCmp
  exact Std.TransCmp.gt_of_gt_of_eq hfirst hsecond

theorem ProductionRules35Key.compareOutcome_eq_gt_trans
    {first second third : ProductionRules35Key}
    (hfirst : first.compareOutcome second = Ordering.eq)
    (hsecond : second.compareOutcome third = Ordering.gt) :
    first.compareOutcome third = Ordering.gt := by
  letI : Std.TransCmp ProductionRules35Key.compareOutcome := compareOutcome_transCmp
  exact Std.TransCmp.gt_of_eq_of_gt hfirst hsecond

theorem ProductionRules35Key.compareOutcome_reverse_lt
    {left right : ProductionRules35Key}
    (h : left.compareOutcome right = Ordering.lt) :
    right.compareOutcome left = Ordering.gt := by
  letI : Std.TransCmp ProductionRules35Key.compareOutcome := compareOutcome_transCmp
  exact Std.OrientedCmp.gt_iff_lt.mpr h

theorem ProductionRules35Key.compareOutcome_total (left right : ProductionRules35Key) :
    left.compareOutcome right ≠ Ordering.lt ∨
      right.compareOutcome left ≠ Ordering.lt := by
  letI : Std.TransCmp ProductionRules35Key.compareOutcome := compareOutcome_transCmp
  cases h : left.compareOutcome right with
  | lt => exact Or.inr (by simp [ProductionRules35Key.compareOutcome_reverse_lt h])
  | eq => exact Or.inl (by simp)
  | gt => exact Or.inl (by simp)

/-! ## Laws transferred back to the live executable -/

theorem compareRawOfficialSequences_of_keys
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center left right : ℕ)
    (leftKey rightKey : ProductionRules35Key)
    (hleft : productionRules35Key? result mol state center left = some leftKey)
    (hright : productionRules35Key? result mol state center right = some rightKey) :
    compareRawOfficialSequences result mol state center left right =
      some (leftKey.compareTrace rightKey) := by
  rw [compareRawOfficialSequences_eq_keyTrace]
  simp [hleft, hright]

theorem compareRawOfficialSequences_outcome_of_keys
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center left right : ℕ)
    (leftKey rightKey : ProductionRules35Key)
    (hleft : productionRules35Key? result mol state center left = some leftKey)
    (hright : productionRules35Key? result mol state center right = some rightKey) :
    (compareRawOfficialSequences result mol state center left right).map cipTraceOutcome =
      some (leftKey.compareOutcome rightKey) := by
  rw [compareRawOfficialSequences_of_keys result mol state center left right
    leftKey rightKey hleft hright]
  rfl

theorem compareRawOfficialSequences_refuses_of_leftRule4a_missing
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center left right : ℕ)
    (hleft : branchRule4aSparseLayers mol state center left = none) :
    compareRawOfficialSequences result mol state center left right = none := by
  simp [compareRawOfficialSequences, hleft]

theorem compareRawOfficialSequences_refuses_of_rightRule4a_missing
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center left right : ℕ)
    (hright : branchRule4aSparseLayers mol state center right = none) :
    compareRawOfficialSequences result mol state center left right = none := by
  unfold compareRawOfficialSequences
  cases branchRule4aSparseLayers mol state center left <;> simp [hright]

/-- Once the constitutional engine has proved a tie, the public production branch comparator
returns exactly the lawful Rules 3--5 key outcome. -/
theorem compareBranchesThroughOfficialContext?_of_tied_keys
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center left right : ℕ)
    (leftKey rightKey : ProductionRules35Key)
    (htied : mol.compareBranchesAuthoritativeStatus center left right =
      RawMolecule.BranchComparisonStatus.tied)
    (hleft : productionRules35Key? result mol state center left = some leftKey)
    (hright : productionRules35Key? result mol state center right = some rightKey) :
    compareBranchesThroughOfficialContext? result mol state fuel center left right =
      some (leftKey.compareOutcome rightKey) := by
  unfold compareBranchesThroughOfficialContext?
  rw [htied]
  exact compareRawOfficialSequences_outcome_of_keys result mol state center left right
    leftKey rightKey hleft hright

/-- Exact soundness and completeness of trace production relative to the unary production keys. -/
theorem compareRawOfficialSequences_some_iff
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center left right : ℕ) (trace : List CIPRuleDecision) :
    compareRawOfficialSequences result mol state center left right = some trace ↔
      ∃ leftKey rightKey,
        productionRules35Key? result mol state center left = some leftKey ∧
        productionRules35Key? result mol state center right = some rightKey ∧
        trace = leftKey.compareTrace rightKey := by
  rw [compareRawOfficialSequences_eq_keyTrace]
  cases productionRules35Key? result mol state center left <;> simp
  cases productionRules35Key? result mol state center right <;> simp
  constructor <;> intro h <;> exact h.symm

theorem compareRawOfficialSequences_eq_refl
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center ligand : ℕ) (key : ProductionRules35Key)
    (hkey : productionRules35Key? result mol state center ligand = some key) :
    (compareRawOfficialSequences result mol state center ligand ligand).map cipTraceOutcome =
      some Ordering.eq := by
  rw [compareRawOfficialSequences_outcome_of_keys result mol state center ligand ligand
    key key hkey hkey, key.compareOutcome_eq_refl]

theorem compareRawOfficialSequences_eq_trans
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center first second third : ℕ)
    (firstKey secondKey thirdKey : ProductionRules35Key)
    (hfirstKey : productionRules35Key? result mol state center first = some firstKey)
    (hsecondKey : productionRules35Key? result mol state center second = some secondKey)
    (hthirdKey : productionRules35Key? result mol state center third = some thirdKey)
    (hfirst : (compareRawOfficialSequences result mol state center first second).map
      cipTraceOutcome = some Ordering.eq)
    (hsecond : (compareRawOfficialSequences result mol state center second third).map
      cipTraceOutcome = some Ordering.eq) :
    (compareRawOfficialSequences result mol state center first third).map cipTraceOutcome =
      some Ordering.eq := by
  have hfirstOutcome : firstKey.compareOutcome secondKey = Ordering.eq := by
    rw [compareRawOfficialSequences_outcome_of_keys result mol state center first second
      firstKey secondKey hfirstKey hsecondKey] at hfirst
    exact Option.some.inj hfirst
  have hsecondOutcome : secondKey.compareOutcome thirdKey = Ordering.eq := by
    rw [compareRawOfficialSequences_outcome_of_keys result mol state center second third
      secondKey thirdKey hsecondKey hthirdKey] at hsecond
    exact Option.some.inj hsecond
  rw [compareRawOfficialSequences_outcome_of_keys result mol state center first third
    firstKey thirdKey hfirstKey hthirdKey,
    ProductionRules35Key.compareOutcome_eq_trans hfirstOutcome hsecondOutcome]

theorem compareRawOfficialSequences_gt_trans
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center first second third : ℕ)
    (firstKey secondKey thirdKey : ProductionRules35Key)
    (hfirstKey : productionRules35Key? result mol state center first = some firstKey)
    (hsecondKey : productionRules35Key? result mol state center second = some secondKey)
    (hthirdKey : productionRules35Key? result mol state center third = some thirdKey)
    (hfirst : (compareRawOfficialSequences result mol state center first second).map
      cipTraceOutcome = some Ordering.gt)
    (hsecond : (compareRawOfficialSequences result mol state center second third).map
      cipTraceOutcome = some Ordering.gt) :
    (compareRawOfficialSequences result mol state center first third).map cipTraceOutcome =
      some Ordering.gt := by
  have hfirstOutcome : firstKey.compareOutcome secondKey = Ordering.gt := by
    rw [compareRawOfficialSequences_outcome_of_keys result mol state center first second
      firstKey secondKey hfirstKey hsecondKey] at hfirst
    exact Option.some.inj hfirst
  have hsecondOutcome : secondKey.compareOutcome thirdKey = Ordering.gt := by
    rw [compareRawOfficialSequences_outcome_of_keys result mol state center second third
      secondKey thirdKey hsecondKey hthirdKey] at hsecond
    exact Option.some.inj hsecond
  rw [compareRawOfficialSequences_outcome_of_keys result mol state center first third
    firstKey thirdKey hfirstKey hthirdKey,
    ProductionRules35Key.compareOutcome_gt_trans hfirstOutcome hsecondOutcome]

theorem compareRawOfficialSequences_total
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center left right : ℕ)
    (leftKey rightKey : ProductionRules35Key)
    (hleft : productionRules35Key? result mol state center left = some leftKey)
    (hright : productionRules35Key? result mol state center right = some rightKey) :
    ((compareRawOfficialSequences result mol state center left right).map cipTraceOutcome =
        some Ordering.lt → False) ∨
      ((compareRawOfficialSequences result mol state center right left).map cipTraceOutcome =
        some Ordering.lt → False) := by
  rw [compareRawOfficialSequences_outcome_of_keys result mol state center left right
      leftKey rightKey hleft hright,
    compareRawOfficialSequences_outcome_of_keys result mol state center right left
      rightKey leftKey hright hleft]
  simpa using leftKey.compareOutcome_total rightKey

/-! ## Rule 3: counterexample and repaired unary key -/

namespace ProductionRule3Coherence

private def emptyMolecule : RawMolecule := { atoms := [], bonds := [] }

private def occurrenceA : ChemistryNormalizationResult.Rule3GeometryOccurrence :=
  { left := 0, right := 1, near := 0, distance := 0,
    geometry := OfficialRule3Geometry.seqcis }

private def occurrenceB : ChemistryNormalizationResult.Rule3GeometryOccurrence :=
  { left := 0, right := 1, near := 1, distance := 0,
    geometry := OfficialRule3Geometry.seqtrans }

private def occurrenceC : ChemistryNormalizationResult.Rule3GeometryOccurrence :=
  { left := 2, right := 3, near := 2, distance := 0,
    geometry := OfficialRule3Geometry.seqtrans }

/-- The former pair-cancelling comparator had non-transitive ties on abstract admitted occurrence
lists: A tied B by same-unit cancellation, B tied C by equal geometry, but A outranked C. -/
theorem legacy_pair_cancellation_tie_counterexample :
    ChemistryNormalizationResult.compareRule3GeometryOccurrencesAtCenter
        emptyMolecule 0 [occurrenceA] [occurrenceB] = Ordering.eq ∧
    ChemistryNormalizationResult.compareRule3GeometryOccurrencesAtCenter
        emptyMolecule 0 [occurrenceB] [occurrenceC] = Ordering.eq ∧
    ChemistryNormalizationResult.compareRule3GeometryOccurrencesAtCenter
        emptyMolecule 0 [occurrenceA] [occurrenceC] = Ordering.gt := by
  simp [ChemistryNormalizationResult.compareRule3GeometryOccurrencesAtCenter,
    ChemistryNormalizationResult.sharedRule3UnitHasIndependentFarReference,
    ChemistryNormalizationResult.Rule3GeometryOccurrence.sameEntryEndpoint,
    ChemistryNormalizationResult.Rule3GeometryOccurrence.sameUnit,
    OfficialRule3Geometry.compare, OfficialRule3Geometry.priority,
    CIPRuleEngine.comparePriorityNat,
    emptyMolecule, occurrenceA, occurrenceB, occurrenceC]

theorem canonical_compare_eq_key_compare
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel center left right : ℕ) :
    result.compareRule3GeometryAtCenter mol fuel center left right =
      compare (result.rule3CanonicalSignature mol fuel center left)
        (result.rule3CanonicalSignature mol fuel center right) :=
  rfl

theorem canonical_compare_eq_trans
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel center first second third : ℕ)
    (hfirst : result.compareRule3GeometryAtCenter mol fuel center first second = Ordering.eq)
    (hsecond : result.compareRule3GeometryAtCenter mol fuel center second third = Ordering.eq) :
    result.compareRule3GeometryAtCenter mol fuel center first third = Ordering.eq := by
  unfold ChemistryNormalizationResult.compareRule3GeometryAtCenter
    ChemistryNormalizationResult.compareRule3CanonicalSignatures at hfirst hsecond ⊢
  apply Std.LawfulEqCmp.compare_eq_iff_eq.mpr
  exact (Std.LawfulEqCmp.compare_eq_iff_eq.mp hfirst).trans
    (Std.LawfulEqCmp.compare_eq_iff_eq.mp hsecond)

theorem canonical_compare_gt_trans
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel center first second third : ℕ)
    (hfirst : result.compareRule3GeometryAtCenter mol fuel center first second = Ordering.gt)
    (hsecond : result.compareRule3GeometryAtCenter mol fuel center second third = Ordering.gt) :
    result.compareRule3GeometryAtCenter mol fuel center first third = Ordering.gt := by
  unfold ChemistryNormalizationResult.compareRule3GeometryAtCenter
    ChemistryNormalizationResult.compareRule3CanonicalSignatures at hfirst hsecond ⊢
  exact Std.TransCmp.gt_of_gt_of_ge hfirst (by simp [hsecond])

theorem canonical_compare_total
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel center left right : ℕ) :
    result.compareRule3GeometryAtCenter mol fuel center left right ≠ Ordering.lt ∨
      result.compareRule3GeometryAtCenter mol fuel center right left ≠ Ordering.lt := by
  unfold ChemistryNormalizationResult.compareRule3GeometryAtCenter
    ChemistryNormalizationResult.compareRule3CanonicalSignatures
  cases h : compare (result.rule3CanonicalSignature mol fuel center left)
      (result.rule3CanonicalSignature mol fuel center right) with
  | lt =>
      exact Or.inr (by
        have reverse : compare (result.rule3CanonicalSignature mol fuel center right)
            (result.rule3CanonicalSignature mol fuel center left) = Ordering.gt :=
          Std.OrientedCmp.gt_iff_lt.mpr h
        simp [reverse])
  | eq => exact Or.inl (by simp)
  | gt => exact Or.inl (by simp)

end ProductionRule3Coherence

/-! ## Rule 4b: production/declarative key identity -/

theorem compareRule4bLayerHierarchies_eq_declarativeReadings
    (left right : List (List RawDescriptorFact)) :
    compareRule4bLayerHierarchies left right =
      compare (rule4bCanonicalSignature left) (rule4bCanonicalSignature right) :=
  rfl

/-! ## Kernel-authority guards for the live Rule-3 bridge -/

assert_kernel_only TetraStereo.OneCenter.officialRule3Geometry_priority_toDeclarative
assert_kernel_only TetraStereo.OneCenter.list_compareLex_map_map_congr
assert_kernel_only TetraStereo.OneCenter.option_bind_const_none_eq
assert_kernel_only TetraStereo.OneCenter.ordering_byKey_id_compare_eq
assert_kernel_only TetraStereo.OneCenter.compareAddressedEntry_observations
assert_kernel_only TetraStereo.OneCenter.compareAddressedLayer_observations
assert_kernel_only TetraStereo.OneCenter.compareAddressedHierarchy_observations
assert_kernel_only TetraStereo.OneCenter.mapObservationPriorityLayers_eq_map
assert_kernel_only TetraStereo.OneCenter.compileRule3HierarchyKeyComplete?_rule3Aligned
assert_kernel_only TetraStereo.OneCenter.compareAddressedHierarchy_declarativeLayers_eq_compiled
assert_kernel_only TetraStereo.OneCenter.attachAlignedRule3Key_none
assert_kernel_only TetraStereo.OneCenter.attachAlignedRule3Key_some
assert_kernel_only TetraStereo.OneCenter.productionRules35Key?_eq_none_of_rule4a_none
assert_kernel_only TetraStereo.OneCenter.productionRules35Key?_eq_none_of_compile_none
assert_kernel_only TetraStereo.OneCenter.productionRules35Key?_eq_some_of_compile
assert_kernel_only TetraStereo.OneCenter.ProductionRules35Key.rule3_outcome_iff_compiled
assert_kernel_only TetraStereo.OneCenter.productionRules35Key?_rule3Aligned
assert_kernel_only TetraStereo.OneCenter.compareRawOfficialSequences_eq_keyTrace
assert_kernel_only TetraStereo.OneCenter.ProductionRules35Key.compareOutcome_eq_lawfulCompare

end
end OneCenter
end TetraStereo
