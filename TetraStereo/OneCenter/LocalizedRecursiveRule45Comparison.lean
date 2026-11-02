import TetraStereo.OneCenter.LocalizedRecursiveDescriptorKey

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Recursive localized Rules 4a, 4b, and 5 comparison

This module compares the recursively re-ranked unary keys after the caller has established ties
through Rules 1a--3.  It covers the fail-closed constitution-only uppercase tetrahedral-source
subdomain.  Its API says `AfterPriorTie` deliberately: Rule 3 and Rule 4c are not converted to
ties by this implementation.
-/

namespace CertifiedLocalizedCIPInput

/-- Compare only the descriptor projection of two already recursively ranked keys.  Their
constitutional components were used at every parent to rank children, but the ligand roots are
assumed tied through the earlier rules at this boundary. -/
def compareLocalizedRecursiveDescriptorProjections
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRecursiveDescriptorKey) : Ordering :=
  OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
    left.descriptor right.descriptor

/-- Rule-4a recursive key for one ligand. -/
def localizedRecursiveRule4aKeyAt? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    Option input.LocalizedRecursiveDescriptorKey :=
  input.localizedRecursiveDescriptorKeyAt? center index
    LocalizedConstitutionalDescriptorStage.rule4a

theorem localizedRecursiveRule4aKeyAt?_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (key : input.LocalizedRecursiveDescriptorKey)
    (computed : input.localizedRecursiveRule4aKeyAt? center index = some key) :
    input.DeclarativeLocalizedRecursiveDescriptorKey
      LocalizedConstitutionalDescriptorStage.rule4a
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index)) key := by
  exact input.localizedRecursiveDescriptorKeyAt?_sound center index
    LocalizedConstitutionalDescriptorStage.rule4a key computed

/-- Recursively compile one complete Rule-4b reading for every selected reference. -/
def buildLocalizedRecursiveRule4bReadingsAt?
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    List RS → Option (List input.LocalizedRecursiveDescriptorKey)
  | [] => some []
  | reference :: references => do
      let key ← input.localizedRecursiveDescriptorKeyAt? center index
        (.rule4b reference)
      let keys ← input.buildLocalizedRecursiveRule4bReadingsAt?
        center index references
      some (key :: keys)

/-- Pointwise declarative derivations for all selected Rule-4b references. -/
inductive DeclarativeLocalizedRecursiveRule4bReadingsAt
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    List RS → List input.LocalizedRecursiveDescriptorKey → Prop
  | nil : DeclarativeLocalizedRecursiveRule4bReadingsAt input center index [] []
  | cons {reference references key keys}
      (head : input.DeclarativeLocalizedRecursiveDescriptorKey (.rule4b reference)
        (input.certified.input.molecule.atomCount + 1)
        (OfficialCIPNode.rootFromEdge center.1
          (input.canonicalLigandAtom center index)) key)
      (tail : DeclarativeLocalizedRecursiveRule4bReadingsAt
        input center index references keys) :
      DeclarativeLocalizedRecursiveRule4bReadingsAt input center index
        (reference :: references) (key :: keys)

theorem buildLocalizedRecursiveRule4bReadingsAt?_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    ∀ references keys,
      input.buildLocalizedRecursiveRule4bReadingsAt? center index references = some keys →
      input.DeclarativeLocalizedRecursiveRule4bReadingsAt center index references keys
  | [], keys, computed => by
      simp [buildLocalizedRecursiveRule4bReadingsAt?] at computed
      subst keys
      exact DeclarativeLocalizedRecursiveRule4bReadingsAt.nil
  | reference :: references, keys, computed => by
      unfold buildLocalizedRecursiveRule4bReadingsAt? at computed
      cases headComputed : input.localizedRecursiveDescriptorKeyAt? center index
          (.rule4b reference) with
      | none => simp [headComputed] at computed
      | some key =>
          cases tailComputed : input.buildLocalizedRecursiveRule4bReadingsAt?
              center index references with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact DeclarativeLocalizedRecursiveRule4bReadingsAt.cons
                (input.localizedRecursiveDescriptorKeyAt?_sound
                  center index (.rule4b reference) key headComputed)
                (input.buildLocalizedRecursiveRule4bReadingsAt?_sound
                  center index references tail tailComputed)

/-- Unary recursive Rule-4b key. -/
structure LocalizedRecursiveRule4bKey (input : CertifiedLocalizedCIPInput) where
  references : List RS
  referenceCountPriority : ℕ
  readings : List input.LocalizedRecursiveDescriptorKey

/-- Build criterion (b)/(c) reference readings from the first descriptor-bearing sphere, then
rank the one or two complete recursive readings within the ligand. -/
def localizedRecursiveRule4bKeyAt? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    Option input.LocalizedRecursiveRule4bKey := do
  let hierarchy ← input.perceiveConstitutionalSeedHierarchyAt? center index
  let references := input.constitutionalRule4bReferences hierarchy
  let readings ← input.buildLocalizedRecursiveRule4bReadingsAt?
    center index references
  some
    { references := references
      referenceCountPriority := constitutionalRule4bReferenceCountPriority references
      readings := input.sortLocalizedRecursiveDescriptorKeys readings }

/-- Independent derivation of a unary recursive Rule-4b key. -/
def DeclarativeLocalizedRecursiveRule4bKeyAt
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (key : input.LocalizedRecursiveRule4bKey) : Prop :=
  ∃ hierarchy readings,
    input.DeclarativeConstitutionalSeedHierarchyAt center index hierarchy ∧
    key.references = input.constitutionalRule4bReferences hierarchy ∧
    input.DeclarativeLocalizedRecursiveRule4bReadingsAt
      center index key.references readings ∧
    key.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority key.references ∧
    key.readings.Perm readings ∧
    input.LocalizedRecursiveDescriptorKeysDescending key.readings

theorem localizedRecursiveRule4bKeyAt?_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (key : input.LocalizedRecursiveRule4bKey)
    (computed : input.localizedRecursiveRule4bKeyAt? center index = some key) :
    input.DeclarativeLocalizedRecursiveRule4bKeyAt center index key := by
  unfold localizedRecursiveRule4bKeyAt? at computed
  cases hierarchyComputed : input.perceiveConstitutionalSeedHierarchyAt? center index with
  | none => simp [hierarchyComputed] at computed
  | some hierarchy =>
      let references := input.constitutionalRule4bReferences hierarchy
      cases readingsComputed : input.buildLocalizedRecursiveRule4bReadingsAt?
          center index references with
      | none => simp [hierarchyComputed, references, readingsComputed] at computed
      | some readings =>
          simp [hierarchyComputed, references, readingsComputed] at computed
          subst key
          exact ⟨hierarchy, readings,
            input.perceiveConstitutionalSeedHierarchyAt?_sound
              center index hierarchy hierarchyComputed,
            rfl,
            input.buildLocalizedRecursiveRule4bReadingsAt?_sound
              center index references readings readingsComputed,
            rfl,
            input.sortLocalizedRecursiveDescriptorKeys_perm readings,
            input.sortLocalizedRecursiveDescriptorKeys_descending readings⟩

/-- Complete recursive Rule-4b comparison.  Criterion (c)(i)'s one-reference-over-two priority
precedes lexicographic comparison of the ranked complete readings. -/
def compareLocalizedRecursiveRule4bKeys (input : CertifiedLocalizedCIPInput) :
    input.LocalizedRecursiveRule4bKey → input.LocalizedRecursiveRule4bKey → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.referenceCountPriority) compare)
    (Ordering.byKey (fun key => key.readings)
      (List.compareLex input.compareLocalizedRecursiveDescriptorProjections))

/-- A recursively compiled Rule-5 comparison under both common reference senses. -/
def localizedRecursiveRule5ComparisonAt?
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4) :
    Option ConstitutionalRule5Comparison := do
  let leftR ← input.localizedRecursiveDescriptorKeyAt? center left (.rule5 RS.R)
  let rightR ← input.localizedRecursiveDescriptorKeyAt? center right (.rule5 RS.R)
  let leftS ← input.localizedRecursiveDescriptorKeyAt? center left (.rule5 RS.S)
  let rightS ← input.localizedRecursiveDescriptorKeyAt? center right (.rule5 RS.S)
  let cmpR := input.compareLocalizedRecursiveDescriptorProjections leftR rightR
  let cmpS := input.compareLocalizedRecursiveDescriptorProjections leftS rightS
  match cmpR with
  | Ordering.lt => some { ordering := Ordering.lt, pseudo := cmpS != Ordering.lt }
  | Ordering.gt => some { ordering := Ordering.gt, pseudo := cmpS != Ordering.gt }
  | Ordering.eq => some { ordering := Ordering.eq, pseudo := false }

/-- Declarative Rule-5 result retaining all four recursive unary-key derivations. -/
def DeclarativeLocalizedRecursiveRule5ComparisonAt
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (result : ConstitutionalRule5Comparison) : Prop :=
  ∃ leftR rightR leftS rightS,
    input.DeclarativeLocalizedRecursiveDescriptorKey (.rule5 RS.R)
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center left)) leftR ∧
    input.DeclarativeLocalizedRecursiveDescriptorKey (.rule5 RS.R)
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center right)) rightR ∧
    input.DeclarativeLocalizedRecursiveDescriptorKey (.rule5 RS.S)
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center left)) leftS ∧
    input.DeclarativeLocalizedRecursiveDescriptorKey (.rule5 RS.S)
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center right)) rightS ∧
    let cmpR := input.compareLocalizedRecursiveDescriptorProjections leftR rightR
    let cmpS := input.compareLocalizedRecursiveDescriptorProjections leftS rightS
    result = match cmpR with
      | Ordering.lt => { ordering := Ordering.lt, pseudo := cmpS != Ordering.lt }
      | Ordering.gt => { ordering := Ordering.gt, pseudo := cmpS != Ordering.gt }
      | Ordering.eq => { ordering := Ordering.eq, pseudo := false }

theorem localizedRecursiveRule5ComparisonAt?_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (result : ConstitutionalRule5Comparison)
    (computed : input.localizedRecursiveRule5ComparisonAt? center left right = some result) :
    input.DeclarativeLocalizedRecursiveRule5ComparisonAt center left right result := by
  unfold localizedRecursiveRule5ComparisonAt? at computed
  cases leftRComputed : input.localizedRecursiveDescriptorKeyAt?
      center left (.rule5 RS.R) with
  | none => simp [leftRComputed] at computed
  | some leftR =>
      cases rightRComputed : input.localizedRecursiveDescriptorKeyAt?
          center right (.rule5 RS.R) with
      | none => simp [leftRComputed, rightRComputed] at computed
      | some rightR =>
          cases leftSComputed : input.localizedRecursiveDescriptorKeyAt?
              center left (.rule5 RS.S) with
          | none => simp [leftRComputed, rightRComputed, leftSComputed] at computed
          | some leftS =>
              cases rightSComputed : input.localizedRecursiveDescriptorKeyAt?
                  center right (.rule5 RS.S) with
              | none =>
                  simp [leftRComputed, rightRComputed, leftSComputed,
                    rightSComputed] at computed
              | some rightS =>
                  refine ⟨leftR, rightR, leftS, rightS,
                    input.localizedRecursiveDescriptorKeyAt?_sound
                      center left (.rule5 RS.R) leftR leftRComputed,
                    input.localizedRecursiveDescriptorKeyAt?_sound
                      center right (.rule5 RS.R) rightR rightRComputed,
                    input.localizedRecursiveDescriptorKeyAt?_sound
                      center left (.rule5 RS.S) leftS leftSComputed,
                    input.localizedRecursiveDescriptorKeyAt?_sound
                      center right (.rule5 RS.S) rightS rightSComputed, ?_⟩
                  generalize cmpREq :
                    input.compareLocalizedRecursiveDescriptorProjections
                      leftR rightR = cmpR at computed ⊢
                  generalize cmpSEq :
                    input.compareLocalizedRecursiveDescriptorProjections
                      leftS rightS = cmpS at computed ⊢
                  cases cmpR <;> cases cmpS <;>
                    simp [leftRComputed, rightRComputed, leftSComputed,
                      rightSComputed, cmpREq, cmpSEq] at computed ⊢ <;>
                    exact computed.symm

/-- Pure 4a → 4b → 5 fallthrough over already compiled recursive unary keys. -/
def assembleLocalizedRecursiveUppercaseRule45
    (input : CertifiedLocalizedCIPInput)
    (left4a right4a : input.LocalizedRecursiveDescriptorKey)
    (left4b right4b : input.LocalizedRecursiveRule4bKey)
    (rule5 : ConstitutionalRule5Comparison) :
    ConstitutionalDescriptorHierarchyComparison :=
  let rule4a := input.compareLocalizedRecursiveDescriptorProjections left4a right4a
  if rule4a != Ordering.eq then
    { ordering := rule4a, decisiveRule? := some CIPRuleFamily.stereogenicUnitKind }
  else
    let rule4b := input.compareLocalizedRecursiveRule4bKeys left4b right4b
    if rule4b != Ordering.eq then
      { ordering := rule4b, decisiveRule? := some CIPRuleFamily.likeUnlikeDescriptorPair }
    else
      { ordering := rule5.ordering
        decisiveRule? := if rule5.ordering = Ordering.eq then none
          else some CIPRuleFamily.pseudoasymmetricTiebreak
        pseudo := rule5.pseudo }

/-- Complete recursive uppercase-seed Rules-4a/4b/5 comparison after an explicit earlier-rule
tie.  All stages are built before assembly, so unresolved evidence fails closed even if an earlier
descriptor stage would appear decisive. -/
def compareLocalizedRecursiveUppercaseRule45AfterPriorTieAt?
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4) :
    Option ConstitutionalDescriptorHierarchyComparison := do
  let left4a ← input.localizedRecursiveRule4aKeyAt? center left
  let right4a ← input.localizedRecursiveRule4aKeyAt? center right
  let left4b ← input.localizedRecursiveRule4bKeyAt? center left
  let right4b ← input.localizedRecursiveRule4bKeyAt? center right
  let rule5 ← input.localizedRecursiveRule5ComparisonAt? center left right
  some (input.assembleLocalizedRecursiveUppercaseRule45
    left4a right4a left4b right4b rule5)

/-- Independent recursive derivation of one assembled later-rule comparison. -/
def DeclarativeLocalizedRecursiveUppercaseRule45AfterPriorTieAt
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (result : ConstitutionalDescriptorHierarchyComparison) : Prop :=
  ∃ left4a right4a left4b right4b rule5,
    input.DeclarativeLocalizedRecursiveDescriptorKey .rule4a
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center left)) left4a ∧
    input.DeclarativeLocalizedRecursiveDescriptorKey .rule4a
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center right)) right4a ∧
    input.DeclarativeLocalizedRecursiveRule4bKeyAt center left left4b ∧
    input.DeclarativeLocalizedRecursiveRule4bKeyAt center right right4b ∧
    input.DeclarativeLocalizedRecursiveRule5ComparisonAt center left right rule5 ∧
    result = input.assembleLocalizedRecursiveUppercaseRule45
      left4a right4a left4b right4b rule5

theorem compareLocalizedRecursiveUppercaseRule45AfterPriorTieAt?_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (result : ConstitutionalDescriptorHierarchyComparison)
    (computed : input.compareLocalizedRecursiveUppercaseRule45AfterPriorTieAt?
      center left right = some result) :
    input.DeclarativeLocalizedRecursiveUppercaseRule45AfterPriorTieAt
      center left right result := by
  unfold compareLocalizedRecursiveUppercaseRule45AfterPriorTieAt? at computed
  cases left4aComputed : input.localizedRecursiveRule4aKeyAt? center left with
  | none => simp [left4aComputed] at computed
  | some left4a =>
      cases right4aComputed : input.localizedRecursiveRule4aKeyAt? center right with
      | none => simp [left4aComputed, right4aComputed] at computed
      | some right4a =>
          cases left4bComputed : input.localizedRecursiveRule4bKeyAt? center left with
          | none =>
              simp [left4aComputed, right4aComputed, left4bComputed] at computed
          | some left4b =>
              cases right4bComputed : input.localizedRecursiveRule4bKeyAt? center right with
              | none =>
                  simp [left4aComputed, right4aComputed, left4bComputed,
                    right4bComputed] at computed
              | some right4b =>
                  cases rule5Computed : input.localizedRecursiveRule5ComparisonAt?
                      center left right with
                  | none =>
                      simp [left4aComputed, right4aComputed, left4bComputed,
                        right4bComputed, rule5Computed] at computed
                  | some rule5 =>
                      simp [left4aComputed, right4aComputed, left4bComputed,
                        right4bComputed, rule5Computed] at computed
                      subst result
                      exact ⟨left4a, right4a, left4b, right4b, rule5,
                        input.localizedRecursiveRule4aKeyAt?_sound
                          center left left4a left4aComputed,
                        input.localizedRecursiveRule4aKeyAt?_sound
                          center right right4a right4aComputed,
                        input.localizedRecursiveRule4bKeyAt?_sound
                          center left left4b left4bComputed,
                        input.localizedRecursiveRule4bKeyAt?_sound
                          center right right4b right4bComputed,
                        input.localizedRecursiveRule5ComparisonAt?_sound
                          center left right rule5 rule5Computed,
                        rfl⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
