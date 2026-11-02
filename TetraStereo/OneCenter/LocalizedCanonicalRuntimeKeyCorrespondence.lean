import TetraStereo.OneCenter.CanonicalRule3Hierarchy
import TetraStereo.OneCenter.LocalizedRerootRecursiveRule3SpatialKey
import TetraStereo.OneCenter.AuthoritativeLocalizedCIPAnalysis
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter


































/-! ## Address vocabulary shared by both sides -/

/-- Raw positional paths and localized sparse addresses use literally the same comparison. -/
theorem compareCanonicalPath_eq_compareNat :
    (RawMolecule.compareCanonicalPath : List ℕ → List ℕ → Ordering) =
      List.compareLex OfficialRuleMajorKey.compareNat :=
  rfl

/-- Raw Rule-1b (reversed root distance) and localized Rule-1b use literally the same comparison. -/
theorem compareRule1bRootDistance_eq_compareRule1b :
    (RawMolecule.compareRule1bRootDistance : ℕ → ℕ → Ordering) =
      OfficialRuleMajorKey.compareRule1b :=
  rfl

/-! ## Mancude-free (plain) Rule-1a labels -/

/-- A plain Rule-1a label (denominator `1`) compares exactly as its numerator. -/
theorem compareCIPAtomicLabel_of_plain (left right : RawMolecule.CIPAtomicLabel)
    (plainLeft : left.denominator = 1) (plainRight : right.denominator = 1) :
    RawMolecule.compareCIPAtomicLabel left right =
      OfficialRuleMajorKey.compareNat left.numerator right.numerator := by
  simp [RawMolecule.compareCIPAtomicLabel, RawMolecule.CIPAtomicLabel.effectiveDenominator,
    OfficialRuleMajorKey.compareNat, plainLeft, plainRight]

/-- A rational Rule-1a value of a natural number compares exactly as that natural number. -/
private theorem compareRule1aValue_ofNat (n m : ℕ) :
    RawMolecule.compareRule1aValue (n : ℚ) (m : ℚ) = OfficialRuleMajorKey.compareNat n m := by
  unfold RawMolecule.compareRule1aValue OfficialRuleMajorKey.compareNat
  change compareOfLessAndEq (n : ℚ) (m : ℚ) = compareOfLessAndEq n m
  unfold compareOfLessAndEq
  by_cases h : n < m
  · have hq : (n : ℚ) < (m : ℚ) := by
      exact_mod_cast h
    simp [hq, h]
  · have hnq : ¬ (n : ℚ) < (m : ℚ) := by
      intro contra
      exact h (by exact_mod_cast contra)
    by_cases h2 : n = m
    · have hq2 : (n : ℚ) = (m : ℚ) := by
        rw [h2]
      simp [h2]
    · have hnq2 : ¬ (n : ℚ) = (m : ℚ) := by
        intro contra
        apply h2
        exact_mod_cast contra
      simp [hnq, h, hnq2, h2]

/-! ## Projection of the comparison-visible Rule-1a layer -/

/-- Numerator projection of a plain Rule-1a addressed layer, landing in the localized sparse-entry
vocabulary. -/
def plainRule1aProjection (layers : List (List RawMolecule.CanonicalAtomicEntry)) :
    List (List (OfficialSparseEntry ℕ)) :=
  layers.map fun layer => layer.map fun e => (e.1, e.2.numerator)

/-! ## List comparison congruence -/

/-- Pointwise comparator agreement on two lists induces agreement of their `List.compareLex`, with a
membership predicate carrying the pointwise hypotheses through the recursion. -/
private theorem list_compareLex_congr_of_forall_mem {α β : Type*}
    {cmp₁ : α → α → Ordering} {cmp₂ : β → β → Ordering} {f : α → β} {P : α → Prop}
    (pointwise : ∀ a b, P a → P b → cmp₁ a b = cmp₂ (f a) (f b)) :
    ∀ left right : List α,
      (∀ a, a ∈ left → P a) → (∀ b, b ∈ right → P b) →
        List.compareLex cmp₁ left right = List.compareLex cmp₂ (left.map f) (right.map f) := by
  intro left
  induction left with
  | nil =>
      intro right _ _
      cases right <;> rfl
  | cons head tail ih =>
      intro right headPlain rightPlain
      cases right with
      | nil => rfl
      | cons otherHead otherTail =>
          rw [List.map_cons, List.map_cons]
          rw [List.compareLex_cons_cons, List.compareLex_cons_cons]
          rw [pointwise head otherHead (headPlain head (by simp)) (rightPlain otherHead (by simp))]
          cases cmp₂ (f head) (f otherHead) with
          | eq =>
              simpa only [Ordering.eq_then] using
                (ih otherTail (fun a mem => headPlain a (List.mem_cons_of_mem head mem))
                  (fun b mem => rightPlain b (List.mem_cons_of_mem otherHead mem)))
          | lt => rfl
          | gt => rfl

/-- Two-sided version: pointwise agreement `cmp₁ (f₁ a) (f₁ b) = cmp₂ (f₂ a) (f₂ b)` induces
agreement of `List.compareLex` over the two mapped lists. -/
private theorem list_compareLex_congr2_of_forall_mem {α β₁ β₂ : Type*}
    {cmp₁ : β₁ → β₁ → Ordering} {cmp₂ : β₂ → β₂ → Ordering}
    {f₁ : α → β₁} {f₂ : α → β₂} {P : α → Prop}
    (pointwise : ∀ a b, P a → P b → cmp₁ (f₁ a) (f₁ b) = cmp₂ (f₂ a) (f₂ b)) :
    ∀ left right : List α,
      (∀ a, a ∈ left → P a) → (∀ b, b ∈ right → P b) →
        List.compareLex cmp₁ (left.map f₁) (right.map f₁) =
          List.compareLex cmp₂ (left.map f₂) (right.map f₂) := by
  intro left
  induction left with
  | nil =>
      intro right _ _
      cases right <;> rfl
  | cons head tail ih =>
      intro right headPlain rightPlain
      cases right with
      | nil => rfl
      | cons otherHead otherTail =>
          rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons]
          rw [List.compareLex_cons_cons, List.compareLex_cons_cons]
          rw [pointwise head otherHead (headPlain head (by simp)) (rightPlain otherHead (by simp))]
          cases cmp₂ (f₂ head) (f₂ otherHead) with
          | eq =>
              simpa only [Ordering.eq_then] using
                (ih otherTail (fun a mem => headPlain a (List.mem_cons_of_mem head mem))
                  (fun b mem => rightPlain b (List.mem_cons_of_mem otherHead mem)))
          | lt => rfl
          | gt => rfl

/-! ## Rule-1a addressed-layer comparison equality -/

/-- One plain Rule-1a entry compares, in the raw `CIPAtomicLabel` comparator, exactly as its
numerator does in the localized natural-number comparator. -/
private theorem compareSparseCanonicalEntry_plain_eq_compareSparseEntry
    (left right : RawMolecule.CanonicalAtomicEntry)
    (plainLeft : left.2.denominator = 1) (plainRight : right.2.denominator = 1) :
    RawMolecule.compareSparseCanonicalEntry RawMolecule.compareCIPAtomicLabel left right =
      OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat
        (left.1, left.2.numerator) (right.1, right.2.numerator) := by
  unfold RawMolecule.compareSparseCanonicalEntry OfficialRuleMajorKey.compareSparseEntry
  simp only [compareLex, Ordering.byKey]
  rw [compareCanonicalPath_eq_compareNat,
    compareCIPAtomicLabel_of_plain left.2 right.2 plainLeft plainRight]

/-- A plain Rule-1a addressed layer compares, over raw `CIPAtomicLabel` entries, exactly as its
numerator projection compares in the localized vocabulary. -/
theorem compareSparseCanonicalLayers_rule1a_eq_of_plain
    (left right : List (List RawMolecule.CanonicalAtomicEntry))
    (plainLeft : ∀ e, e ∈ left.flatten → e.2.denominator = 1)
    (plainRight : ∀ e, e ∈ right.flatten → e.2.denominator = 1) :
    RawMolecule.compareSparseCanonicalLayers RawMolecule.compareCIPAtomicLabel left right =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (plainRule1aProjection left) (plainRule1aProjection right) := by
  unfold RawMolecule.compareSparseCanonicalLayers OfficialRuleMajorKey.compareSparseLayers
    plainRule1aProjection
  apply list_compareLex_congr_of_forall_mem
    (P := fun layer : List RawMolecule.CanonicalAtomicEntry => ∀ e, e ∈ layer → e.2.denominator = 1)
  · intro leftLayer rightLayer leftLayerPlain rightLayerPlain
    unfold RawMolecule.compareSparseCanonicalLayer OfficialRuleMajorKey.compareSparseLayer
    apply list_compareLex_congr_of_forall_mem
      (P := fun e : RawMolecule.CanonicalAtomicEntry => e.2.denominator = 1)
    · intro leftEntry rightEntry leftPlain rightPlain
      exact compareSparseCanonicalEntry_plain_eq_compareSparseEntry leftEntry rightEntry
        leftPlain rightPlain
    · intro e mem
      exact leftLayerPlain e mem
    · intro e mem
      exact rightLayerPlain e mem
  · intro layer mem e entryMem
    exact plainLeft e (List.mem_flatten.mpr ⟨layer, mem, entryMem⟩)
  · intro layer mem e entryMem
    exact plainRight e (List.mem_flatten.mpr ⟨layer, mem, entryMem⟩)

/-- A plain Rule-1a label's rational value is its numerator as a rational. -/
private theorem canonicalAtomicEntryValue_of_plain (entry : RawMolecule.CanonicalAtomicEntry)
    (plain : entry.2.denominator = 1) :
    RawMolecule.canonicalAtomicEntryValue entry = (entry.1, (entry.2.numerator : ℚ)) := by
  unfold RawMolecule.canonicalAtomicEntryValue RawMolecule.canonicalLabelValue
  have eff : entry.2.effectiveDenominator = 1 := by
    unfold RawMolecule.CIPAtomicLabel.effectiveDenominator
    simp [plain]
  rw [eff]
  simp

/-- One plain Rule-1a entry, projected to its rational value, compares exactly as its numerator in
the localized natural-number comparator. -/
private theorem compareSparseCanonicalEntry_rule1aRational_eq_compareSparseEntry
    (left right : RawMolecule.CanonicalAtomicEntry)
    (plainLeft : left.2.denominator = 1) (plainRight : right.2.denominator = 1) :
    RawMolecule.compareSparseCanonicalEntry RawMolecule.compareRule1aValue
        (RawMolecule.canonicalAtomicEntryValue left)
        (RawMolecule.canonicalAtomicEntryValue right) =
      OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat
        (left.1, left.2.numerator) (right.1, right.2.numerator) := by
  rw [canonicalAtomicEntryValue_of_plain left plainLeft,
    canonicalAtomicEntryValue_of_plain right plainRight]
  unfold RawMolecule.compareSparseCanonicalEntry OfficialRuleMajorKey.compareSparseEntry
  simp only [compareLex, Ordering.byKey]
  rw [compareCanonicalPath_eq_compareNat, compareRule1aValue_ofNat]

/-- The raw rational Rule-1a projection and the localized natural projection compare equally in the
mancude-free case.  This is the Rule-3 observable's Rule-1a column. -/
theorem compareSparseCanonicalLayers_rule1aRational_eq_of_plain
    (left right : List (List RawMolecule.CanonicalAtomicEntry))
    (plainLeft : ∀ e, e ∈ left.flatten → e.2.denominator = 1)
    (plainRight : ∀ e, e ∈ right.flatten → e.2.denominator = 1) :
    RawMolecule.compareSparseCanonicalLayers RawMolecule.compareRule1aValue
        (RawMolecule.mapCanonicalAtomicLayers left)
        (RawMolecule.mapCanonicalAtomicLayers right) =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (plainRule1aProjection left) (plainRule1aProjection right) := by
  unfold RawMolecule.compareSparseCanonicalLayers OfficialRuleMajorKey.compareSparseLayers
    RawMolecule.mapCanonicalAtomicLayers RawMolecule.mapCanonicalAtomicLayer
    plainRule1aProjection
  apply list_compareLex_congr2_of_forall_mem
    (P := fun layer : List RawMolecule.CanonicalAtomicEntry => ∀ e, e ∈ layer → e.2.denominator = 1)
  · intro leftLayer rightLayer leftLayerPlain rightLayerPlain
    unfold RawMolecule.compareSparseCanonicalLayer OfficialRuleMajorKey.compareSparseLayer
    apply list_compareLex_congr2_of_forall_mem
      (P := fun e : RawMolecule.CanonicalAtomicEntry => e.2.denominator = 1)
    · intro leftEntry rightEntry leftPlain rightPlain
      exact compareSparseCanonicalEntry_rule1aRational_eq_compareSparseEntry leftEntry rightEntry
        leftPlain rightPlain
    · intro e mem
      exact leftLayerPlain e mem
    · intro e mem
      exact rightLayerPlain e mem
  · intro layer mem e entryMem
    exact plainLeft e (List.mem_flatten.mpr ⟨layer, mem, entryMem⟩)
  · intro layer mem e entryMem
    exact plainRight e (List.mem_flatten.mpr ⟨layer, mem, entryMem⟩)

/-! ## Key / cursor correspondence -/

/-- A raw canonical branch key and a localized rule-major key carry the same constitutional
comparison projection, in the mancude-free base case.  Rule-1b, Rule-2 and completeness are literal
equalities (the two sides share the `List ℕ × ℕ` sparse vocabulary); Rule-1a is the numerator
projection of the plain raw labels. -/
structure ConstitutionalKeyCorresponds {V : Type*}
    (raw : RawMolecule.CanonicalBranchKey) (loc : OfficialRuleMajorKey V) : Prop where
  plain : ∀ e, e ∈ raw.rule1a.flatten → e.2.denominator = 1
  rule1a : plainRule1aProjection raw.rule1a = loc.rule1a
  rule1b : raw.rule1b = loc.rule1b
  rule2 : raw.rule2 = loc.rule2
  complete : raw.complete = loc.complete

/-- A raw Rules-1a--3 key and a localized recursively-ranked Rule-3 key carry the same
constitutional and Rule-3 comparison projections. -/
structure Rule3KeyCorresponds (input : CertifiedLocalizedCIPInput)
    (raw : RawMolecule.CanonicalRule3Key)
    (loc : input.LocalizedRerootRecursiveRule3SpatialKey) : Prop where
  constitutional : ConstitutionalKeyCorresponds raw.constitutional loc.constitutional
  rule3 : raw.rule3 = loc.rule3

/-! ## Derived comparison equality -/

/-- With the stated correspondence, the raw constitutional comparator computes exactly the localized
rule-major comparator.  Rule 1a is transferred by the plain-label lemma; Rule 1b and Rule 2 are the
shared vocabulary. -/
theorem compareCanonicalBranchKeys_eq_officialRuleMajorKey_compare
    {V : Type*} (leftKey rightKey : RawMolecule.CanonicalBranchKey)
    (leftLoc rightLoc : OfficialRuleMajorKey V)
    (leftCorr : ConstitutionalKeyCorresponds leftKey leftLoc)
    (rightCorr : ConstitutionalKeyCorresponds rightKey rightLoc) :
    RawMolecule.compareCanonicalBranchKeys leftKey rightKey =
      OfficialRuleMajorKey.compare leftLoc rightLoc := by
  rcases leftCorr with ⟨plainLeft, rule1aLeft, rule1bLeft, rule2Left, _⟩
  rcases rightCorr with ⟨plainRight, rule1aRight, rule1bRight, rule2Right, _⟩
  simp only [RawMolecule.compareCanonicalBranchKeys, OfficialRuleMajorKey.compare,
    compareLex, Ordering.byKey]
  rw [compareSparseCanonicalLayers_rule1a_eq_of_plain leftKey.rule1a rightKey.rule1a
        plainLeft plainRight,
      rule1aLeft, rule1aRight,
      rule1bLeft, rule1bRight,
      rule2Left, rule2Right]
  rfl

/-- With the stated correspondence, the raw Rules-1a--3 comparator computes exactly the localized
recursive Rule-3 comparator.  The raw Rule-1a observable is the rational projection; in the
mancude-free case it coincides with the localized natural projection, so the constitutional prefix
and the Rule-3 suffix both agree. -/
theorem compareCanonicalRule3Keys_eq_localizedRule3_compare
    (input : CertifiedLocalizedCIPInput)
    (leftKey rightKey : RawMolecule.CanonicalRule3Key)
    (leftLoc rightLoc : input.LocalizedRerootRecursiveRule3SpatialKey)
    (leftCorr : Rule3KeyCorresponds input leftKey leftLoc)
    (rightCorr : Rule3KeyCorresponds input rightKey rightLoc) :
    RawMolecule.compareCanonicalRule3Keys leftKey rightKey =
      input.compareLocalizedRerootRecursiveRule3SpatialKeys leftLoc rightLoc := by
  rcases leftCorr with ⟨leftConst, leftRule3⟩
  rcases rightCorr with ⟨rightConst, rightRule3⟩
  rw [RawMolecule.compareCanonicalRule3Keys_eq_compareObservable]
  simp only [RawMolecule.compareCanonicalRule3Observable,
    RawMolecule.compareConstitutionalObservable, RawMolecule.canonicalRule3Observable,
    CertifiedLocalizedCIPInput.compareLocalizedRerootRecursiveRule3SpatialKeys,
    compareLex, Ordering.byKey]
  rw [compareSparseCanonicalLayers_rule1aRational_eq_of_plain
        leftKey.constitutional.rule1a rightKey.constitutional.rule1a
        leftConst.plain rightConst.plain,
      leftConst.rule1a, rightConst.rule1a,
      leftConst.rule1b, rightConst.rule1b,
      leftConst.rule2, rightConst.rule2,
      leftRule3, rightRule3]
  rfl

/-! ## Intake atom correspondence -/

/-- The certified localized atom index carrying the same parser index, under structure agreement. -/
def localizedIndexOf (molecule : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : molecule.AuthoritativeStructureAgreement input.certified.input)
    (rawIndex : Fin molecule.atomCount) : input.Atom :=
  ⟨rawIndex.val, by
    have countExact := molecule.toSemanticMolecule?_atomCount
      input.certified.input.molecule agreement.1
    rw [countExact]
    exact rawIndex.isLt⟩

/-- From the existing intake theorem chain, the certified localized graph and the raw source graph
assign the same atomic number and the same source-backed Rule-2 mass at every common parser index.
This is the atom/cursor data correspondence; it does not by itself identify digraph nodes. -/
theorem intakeAtomDataCorresponds
    (molecule : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : molecule.AuthoritativeStructureAgreement input.certified.input)
    (rawIndex : Fin molecule.atomCount) :
    input.moleculeGraph.atomZ (localizedIndexOf molecule input agreement rawIndex) =
        (molecule.atoms.get ⟨rawIndex.val, by simp [RawMolecule.atomCount]⟩).element.atomicNumber ∧
      input.moleculeGraph.atomMass (localizedIndexOf molecule input agreement rawIndex) =
        molecule.atomMassAt rawIndex.val := by
  let rawAtom : AtomSpec := molecule.atoms.get ⟨rawIndex.val, by simp [RawMolecule.atomCount]⟩
  have lookupRaw :
      ∃ sourceAtom : SemanticAtom,
        listGet? input.certified.input.molecule.atoms rawIndex.val = some sourceAtom ∧
          rawAtom.toSemanticAtom? = some sourceAtom := by
    simpa [rawAtom] using
      (molecule.toSemanticMolecule?_atomAtFin input.certified.input.molecule agreement.1 rawIndex)
  obtain ⟨sourceAtom, semanticLookup, rawConverted⟩ := lookupRaw
  have exactAtom := AtomSpec.toSemanticAtom?_exact rawAtom sourceAtom rawConverted
  have rawLookup : molecule.atomAt? rawIndex.val = some rawAtom := by
    simpa [RawMolecule.atomAt?, rawAtom] using
      (listGet?_eq_some_get molecule.atoms ⟨rawIndex.val, by simp [RawMolecule.atomCount]⟩)
  have localizedLookup : listGet? input.certified.input.molecule.atoms rawIndex.val =
      some (input.certified.input.molecule.atoms.get
        (localizedIndexOf molecule input agreement rawIndex)) := by
    simpa [localizedIndexOf] using
      (listGet?_eq_some_get input.certified.input.molecule.atoms
        (localizedIndexOf molecule input agreement rawIndex))
  have localizedEqSource :
      input.certified.input.molecule.atoms.get
        (localizedIndexOf molecule input agreement rawIndex) = sourceAtom := by
    exact Option.some.inj (localizedLookup.symm.trans semanticLookup)
  have z := SemanticMolecule.toLocalizedMoleculeGraph_atomZ
    input.certified.input.molecule (localizedIndexOf molecule input agreement rawIndex)
  have m := SemanticMolecule.toLocalizedMoleculeGraph_atomMass
    input.certified.input.molecule (localizedIndexOf molecule input agreement rawIndex)
  constructor
  · rw [CertifiedLocalizedCIPInput.moleculeGraph, z, localizedEqSource]
    exact exactAtom.1
  · rw [CertifiedLocalizedCIPInput.moleculeGraph, m, localizedEqSource]
    have notWildcard : rawAtom.element ≠ .wildcard := by
      have isSome : rawAtom.toSemanticAtom?.isSome = true := by
        rw [rawConverted]
        rfl
      exact (AtomSpec.toSemanticAtom?_isSome rawAtom).mp isSome
    have sourceMass : sourceAtom.rule2MassPico? =
        RawMolecule.rule2MassPico? rawAtom.element rawAtom.isotope? := by
      unfold SemanticAtom.rule2MassPico? RawMolecule.rule2MassPico?
      rw [exactAtom.1, exactAtom.2.1, if_neg notWildcard]
    have rawMass : molecule.atomMassAt? rawIndex.val =
        RawMolecule.rule2MassPico? rawAtom.element rawAtom.isotope? := by
      simp [RawMolecule.atomMassAt?, rawLookup]
    simp only [RawMolecule.atomMassAt, sourceMass, rawMass]

/- Kernel trust checks for the public theorems of this module. -/
assert_kernel_only compareCanonicalPath_eq_compareNat
assert_kernel_only compareRule1bRootDistance_eq_compareRule1b
assert_kernel_only compareCIPAtomicLabel_of_plain
assert_kernel_only compareSparseCanonicalLayers_rule1a_eq_of_plain
assert_kernel_only compareSparseCanonicalLayers_rule1aRational_eq_of_plain
assert_kernel_only compareCanonicalBranchKeys_eq_officialRuleMajorKey_compare
assert_kernel_only compareCanonicalRule3Keys_eq_localizedRule3_compare
assert_kernel_only intakeAtomDataCorresponds

end TetraStereo.OneCenter
