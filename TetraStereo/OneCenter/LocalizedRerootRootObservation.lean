import TetraStereo.OneCenter.LocalizedRerootRuleMajorKey
import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Key
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Root observations preserved by localized reroot rule-major compilation

`buildLocalizedRerootRuleMajorKey?` compiles a complete Rules-1a--2 key over the occurrence
zipper.  The cumulative Rules-4a--5 builder `buildLocalizedRerootCumulativeRule45Key?` embeds a
constitutional key of the same shape at every node, and the compound Rules-4b/4c and Rule-5
builders retain those cumulative keys (`rule4aKey`, `commonR`, `commonS`).  This module proves
that every *successful executable* result of these builders retains, at the empty parent address
of its first sphere, exactly the cursor occurrence node's own root observations.

Each statement is independent of the fuel, of whether the cursor is terminal, and of how the
recursively compiled child keys happen to be ordered or ranked: only the root layer of the actual
returned key is inspected.

The proofs unfold the actual definitions and analyse their real outcomes.  A refusal
(`localizedRerootChildren?` returning `none`, or a nonterminal cursor at zero fuel) contradicts
success.  In each success branch the returned key is literally the root key or its `assemble`
join with the sorted child keys, so the first layer is computed rather than assumed.
-/

namespace OfficialRuleMajorKey

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The first Rule-1a layer of a root joined to sorted children is the root's own observation at
the empty parent address. -/
theorem assemble_officialRuleMajorRootKey_rule1a_head
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (complete : Bool)
    (children : List (OfficialRuleMajorKey V)) :
    (assemble (m.officialRuleMajorRootKey node complete) children).rule1a.head? =
      some [([], (ofLex (m.officialNodeAtomLabel node)).1)] := by
  simp [assemble, MoleculeGraph.officialRuleMajorRootKey]

/-- The first Rule-1b layer of a root joined to sorted children is the root's own duplicate
distance at the empty parent address. -/
theorem assemble_officialRuleMajorRootKey_rule1b_head
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (complete : Bool)
    (children : List (OfficialRuleMajorKey V)) :
    (assemble (m.officialRuleMajorRootKey node complete) children).rule1b.head? =
      some [([], node.rule1bRootDistance)] := by
  simp [assemble, MoleculeGraph.officialRuleMajorRootKey]

/-- The first Rule-2 layer of a root joined to sorted children is the root's own mass observation
at the empty parent address. -/
theorem assemble_officialRuleMajorRootKey_rule2_head
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (complete : Bool)
    (children : List (OfficialRuleMajorKey V)) :
    (assemble (m.officialRuleMajorRootKey node complete) children).rule2.head? =
      some [([], (ofLex (m.officialNodeAtomLabel node)).2)] := by
  simp [assemble, MoleculeGraph.officialRuleMajorRootKey]

end OfficialRuleMajorKey

namespace CertifiedLocalizedCIPInput

/-! ## Pure rule-major builder -/

/-- Successful reroot rule-major compilation retains all three root observations of the cursor
node at address `[]` in the first sphere, independently of fuel, recursion and sibling ranking. -/
theorem buildLocalizedRerootRuleMajorKey?_rootObservation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ fuel cursor key,
      input.buildLocalizedRerootRuleMajorKey?
        (carrierFuel := carrierFuel) fuel cursor = some key →
      key.rule1a.head? =
          some [([], (ofLex (input.moleculeGraph.officialNodeAtomLabel
            cursor.occurrence.1.node)).1)] ∧
        key.rule1b.head? =
          some [([], cursor.occurrence.1.node.rule1bRootDistance)] ∧
        key.rule2.head? =
          some [([], (ofLex (input.moleculeGraph.officialNodeAtomLabel
            cursor.occurrence.1.node)).2)]
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootRuleMajorKey? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            simp [MoleculeGraph.officialRuleMajorRootKey]
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootRuleMajorKey? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            simp [MoleculeGraph.officialRuleMajorRootKey]
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedRerootRuleMajorKey? fuel) with
            | none => simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                cases sortedComputed : OfficialRuleMajorKey.sort? childKeys with
                | none =>
                    simp [childrenComputed, terminal, childKeysComputed,
                      sortedComputed] at computed
                | some sorted =>
                    simp [childrenComputed, terminal, childKeysComputed,
                      sortedComputed] at computed
                    subst key
                    simp [OfficialRuleMajorKey.assemble,
                      MoleculeGraph.officialRuleMajorRootKey]

/-- Successful reroot rule-major compilation preserves the cursor node's Rule-1a root observation
as the first layer and empty parent address. -/
theorem buildLocalizedRerootRuleMajorKey?_rule1a_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ fuel cursor key,
      input.buildLocalizedRerootRuleMajorKey?
        (carrierFuel := carrierFuel) fuel cursor = some key →
      key.rule1a.head? =
        some [([], (ofLex (input.moleculeGraph.officialNodeAtomLabel
          cursor.occurrence.1.node)).1)] := by
  intro fuel cursor key computed
  exact (input.buildLocalizedRerootRuleMajorKey?_rootObservation
    (carrierFuel := carrierFuel) fuel cursor key computed).1

/-- Successful reroot rule-major compilation preserves the cursor node's Rule-1b root observation
as the first layer and empty parent address. -/
theorem buildLocalizedRerootRuleMajorKey?_rule1b_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ fuel cursor key,
      input.buildLocalizedRerootRuleMajorKey?
        (carrierFuel := carrierFuel) fuel cursor = some key →
      key.rule1b.head? =
        some [([], cursor.occurrence.1.node.rule1bRootDistance)] := by
  intro fuel cursor key computed
  exact (input.buildLocalizedRerootRuleMajorKey?_rootObservation
    (carrierFuel := carrierFuel) fuel cursor key computed).2.1

/-- Successful reroot rule-major compilation preserves the cursor node's Rule-2 root observation
as the first layer and empty parent address. -/
theorem buildLocalizedRerootRuleMajorKey?_rule2_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ fuel cursor key,
      input.buildLocalizedRerootRuleMajorKey?
        (carrierFuel := carrierFuel) fuel cursor = some key →
      key.rule2.head? =
        some [([], (ofLex (input.moleculeGraph.officialNodeAtomLabel
          cursor.occurrence.1.node)).2)] := by
  intro fuel cursor key computed
  exact (input.buildLocalizedRerootRuleMajorKey?_rootObservation
    (carrierFuel := carrierFuel) fuel cursor key computed).2.2

/-! ## Cumulative Rules-4a--5 builder

`buildLocalizedRerootCumulativeRule45Key?` is the builder that actually supplies the production
Rules-4a--5 keys.  Its `constitutional` field is constructed by the same root-key/`assemble`
discipline, so the same observation is retained for every stage, target occurrence and dependency
view. -/

/-- Successful cumulative Rules-4a--5 compilation retains all three constitutional root
observations of the cursor node at address `[]`, for every stage, target and view. -/
theorem buildLocalizedRerootCumulativeRule45Key?_constitutional_rootObservation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel cursor key,
      input.buildLocalizedRerootCumulativeRule45Key?
        stage target view fuel cursor = some key →
      key.constitutional.rule1a.head? =
          some [([], (ofLex (input.moleculeGraph.officialNodeAtomLabel
            cursor.occurrence.1.node)).1)] ∧
        key.constitutional.rule1b.head? =
          some [([], cursor.occurrence.1.node.rule1bRootDistance)] ∧
        key.constitutional.rule2.head? =
          some [([], (ofLex (input.moleculeGraph.officialNodeAtomLabel
            cursor.occurrence.1.node)).2)]
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            simp [MoleculeGraph.officialRuleMajorRootKey]
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            simp [MoleculeGraph.officialRuleMajorRootKey]
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedRerootCumulativeRule45Key?
                  stage target view fuel) with
            | none => simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
                subst key
                simp [OfficialRuleMajorKey.assemble,
                  MoleculeGraph.officialRuleMajorRootKey]

/-- Successful cumulative Rules-4a--5 compilation preserves the cursor node's Rule-1b
constitutional root observation as the first layer and empty parent address. -/
theorem buildLocalizedRerootCumulativeRule45Key?_constitutional_rule1b_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel cursor key,
      input.buildLocalizedRerootCumulativeRule45Key?
        stage target view fuel cursor = some key →
      key.constitutional.rule1b.head? =
        some [([], cursor.occurrence.1.node.rule1bRootDistance)] := by
  intro fuel cursor key computed
  exact (input.buildLocalizedRerootCumulativeRule45Key?_constitutional_rootObservation
    stage target view fuel cursor key computed).2.1

/-! ## Compound Rules-4b/4c and Rule-5 builders

The compound Rule-4b/4c key's `rule4aKey` is the `.rule4a`-stage cumulative key, and the complete
Rule-5 key retains it as `prior.rule4aKey`. -/

/-- A successful compound Rules-4b/4c key retains the Rule-1b constitutional root observation in
its compiled Rule-4a key. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_rule4aKey_constitutional_rule1b_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel cursor key,
      input.buildLocalizedRerootCompoundRule4bcKey?
        target view fuel cursor = some key →
      key.rule4aKey.constitutional.rule1b.head? =
        some [([], cursor.occurrence.1.node.rule1bRootDistance)] := by
  intro fuel cursor key computed
  unfold buildLocalizedRerootCompoundRule4bcKey? at computed
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45Key?
      .rule4a target view fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
      let alternatives := localizedRule4bcReferenceAlternatives references
      cases readingsComputed : input.buildLocalizedRerootRule4bcReadings?
          target view fuel cursor alternatives with
      | none =>
          simp [rule4aComputed, references, alternatives, readingsComputed] at computed
      | some readings =>
          simp [rule4aComputed, references, alternatives, readingsComputed] at computed
          subst key
          exact input.buildLocalizedRerootCumulativeRule45Key?_constitutional_rule1b_head
            .rule4a target view fuel cursor rule4aKey rule4aComputed

/-- A successful complete Rules-4a--5 key retains the Rule-1b constitutional root observation in
the compiled Rule-4a key carried by its compound prior. -/
theorem buildLocalizedRerootCompoundRule45Key?_constitutional_rule1b_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel cursor key,
      input.buildLocalizedRerootCompoundRule45Key?
        target view fuel cursor = some key →
      key.prior.rule4aKey.constitutional.rule1b.head? =
        some [([], cursor.occurrence.1.node.rule1bRootDistance)] := by
  intro fuel cursor key computed
  unfold buildLocalizedRerootCompoundRule45Key? at computed
  cases priorComputed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor with
  | none => simp [priorComputed] at computed
  | some prior =>
      cases readingsComputed : input.buildLocalizedRerootRule5Readings?
          target view fuel cursor prior.readings with
      | none => simp [priorComputed, readingsComputed] at computed
      | some readings =>
          simp [priorComputed, readingsComputed] at computed
          subst key
          exact input.buildLocalizedRerootCompoundRule4bcKey?_rule4aKey_constitutional_rule1b_head
            target view fuel cursor prior priorComputed

end CertifiedLocalizedCIPInput

assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.assemble_officialRuleMajorRootKey_rule1a_head
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.assemble_officialRuleMajorRootKey_rule1b_head
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.assemble_officialRuleMajorRootKey_rule2_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRuleMajorKey?_rootObservation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRuleMajorKey?_rule1a_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRuleMajorKey?_rule1b_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRuleMajorKey?_rule2_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_constitutional_rootObservation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_constitutional_rule1b_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKey?_rule4aKey_constitutional_rule1b_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45Key?_constitutional_rule1b_head

end TetraStereo.OneCenter
