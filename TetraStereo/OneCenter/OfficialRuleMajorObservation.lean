import TetraStereo.OneCenter.OfficialRuleMajorKey
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Observer-parameterized rule-major observation companion

This module is the extracted companion to `TetraStereo.OneCenter.OfficialRuleMajorKey`.  It adds a
chosen Rule-1b observation `observe : OfficialCIPNode V → ℕ` alongside the existing stored
`rule1bRootDistance`, without changing any constructor, stored field or comparator in the core
module.

The additions are stated as an independent alignment invariant (`SourceAlignedWith`), a fresh
addressed-tree comparison and trace under the chosen observer, the corresponding cached-key
comparison theorems, observer-parameterized root keys and compilers, and the source-alignment,
declarative-expansion, completeness and Rule-1a-head preservation theorems for those compilers.
The legacy definitions are recovered exactly at `OfficialCIPNode.rule1bRootDistance` by `rfl`
theorems.

Only already-proved additions are present here.  The three private structural `mapM` lemmas of the
core module are not exported across modules; local copies are carried under `observation_mapM_*`
names solely to support the proofs below.  No legacy public declaration is redeclared.
-/

namespace TetraStereo.OneCenter

namespace OfficialRuleMajorKey

/-- Projection-refinement invariant with the Rule-1b observation chosen independently. Every other
observation is fixed; only the duplicate-root distance observer is parameterized. -/
def SourceAlignedWith {V : Type*} [Fintype V] [DecidableEq V]
    (observe : OfficialCIPNode V → ℕ) (m : MoleculeGraph V)
    (key : OfficialRuleMajorKey V) : Prop :=
  key.rule1a = mapSourceLayers
      (fun node => (ofLex (m.officialNodeAtomLabel node)).1) key.sourceNodes ∧
    key.rule1b = mapSourceLayers observe key.sourceNodes ∧
    key.rule2 = mapSourceLayers
      (fun node => (ofLex (m.officialNodeAtomLabel node)).2) key.sourceNodes

/-- The legacy alignment is exactly the observer specialization at `rule1bRootDistance`. -/
theorem SourceAlignedWith_eq_rule1bRootDistance {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (key : OfficialRuleMajorKey V) :
    SourceAlignedWith OfficialCIPNode.rule1bRootDistance m key = SourceAligned m key :=
  rfl

/-- Independent rule-major reading with the Rule-1b observation chosen independently. -/
def compareAddressedSourcesWith {V : Type*} [Fintype V] [DecidableEq V]
    (observe : OfficialCIPNode V → ℕ) (m : MoleculeGraph V)
    (left right : AddressedSourceLayers V) : Ordering :=
  compareLex
    (Ordering.byKey
      (mapSourceLayers fun node => (ofLex (m.officialNodeAtomLabel node)).1)
      (compareSparseLayers compareNat))
    (compareLex
      (Ordering.byKey (mapSourceLayers observe) (compareSparseLayers compareRule1b))
      (Ordering.byKey
        (mapSourceLayers fun node => (ofLex (m.officialNodeAtomLabel node)).2)
        (compareSparseLayers compareNat)))
    left right

/-- The legacy addressed comparison is exactly the observer specialization. -/
theorem compareAddressedSourcesWith_eq_rule1bRootDistance {V : Type*} [Fintype V]
    [DecidableEq V] (m : MoleculeGraph V) (left right : AddressedSourceLayers V) :
    compareAddressedSourcesWith OfficialCIPNode.rule1bRootDistance m left right =
      compareAddressedSources m left right :=
  rfl

/-- Rule-tagged constitutional trace read freshly from provenance nodes, with the Rule-1b
observation chosen independently. -/
def compareAddressedSourceTraceWith {V : Type*} [Fintype V] [DecidableEq V]
    (observe : OfficialCIPNode V → ℕ) (m : MoleculeGraph V)
    (left right : AddressedSourceLayers V) :
    List CIPRuleDecision :=
  [ { rule := CIPRuleFamily.atomicNumber
      outcome := compareSparseLayers compareNat
        (mapSourceLayers (fun node => (ofLex (m.officialNodeAtomLabel node)).1) left)
        (mapSourceLayers (fun node => (ofLex (m.officialNodeAtomLabel node)).1) right) }
  , { rule := CIPRuleFamily.duplicateAtom
      outcome := compareSparseLayers compareRule1b
        (mapSourceLayers observe left)
        (mapSourceLayers observe right) }
  , { rule := CIPRuleFamily.isotopeMass
      outcome := compareSparseLayers compareNat
        (mapSourceLayers (fun node => (ofLex (m.officialNodeAtomLabel node)).2) left)
        (mapSourceLayers (fun node => (ofLex (m.officialNodeAtomLabel node)).2) right) }
  ]

/-- The legacy addressed trace is exactly the observer specialization. -/
theorem compareAddressedSourceTraceWith_eq_rule1bRootDistance {V : Type*} [Fintype V]
    [DecidableEq V] (m : MoleculeGraph V) (left right : AddressedSourceLayers V) :
    compareAddressedSourceTraceWith OfficialCIPNode.rule1bRootDistance m left right =
      compareAddressedSourceTrace m left right :=
  rfl

/-- The cached-key trace is exactly the fresh provenance interpretation on observer-aligned keys. -/
theorem compareTrace_eq_compareAddressedSourceTraceWith_of_sourceAlignedWith
    {V : Type*} [Fintype V] [DecidableEq V]
    (observe : OfficialCIPNode V → ℕ)
    (m : MoleculeGraph V) (left right : OfficialRuleMajorKey V)
    (leftAligned : SourceAlignedWith observe m left)
    (rightAligned : SourceAlignedWith observe m right) :
    compareTrace left right =
      compareAddressedSourceTraceWith observe m left.sourceNodes right.sourceNodes := by
  rcases leftAligned with ⟨left1a, left1b, left2⟩
  rcases rightAligned with ⟨right1a, right1b, right2⟩
  simp only [compareTrace, compareAddressedSourceTraceWith]
  rw [left1a, right1a, left1b, right1b, left2, right2]

/-- On observer-aligned keys, cached-key comparison is exactly fresh comparison of the provenance
trees under the chosen observer. -/
theorem compare_eq_compareAddressedSourcesWith_of_sourceAlignedWith
    {V : Type*} [Fintype V] [DecidableEq V]
    (observe : OfficialCIPNode V → ℕ)
    (m : MoleculeGraph V) (left right : OfficialRuleMajorKey V)
    (leftAligned : SourceAlignedWith observe m left)
    (rightAligned : SourceAlignedWith observe m right) :
    OfficialRuleMajorKey.compare left right =
      compareAddressedSourcesWith observe m left.sourceNodes right.sourceNodes := by
  rcases leftAligned with ⟨left1a, left1b, left2⟩
  rcases rightAligned with ⟨right1a, right1b, right2⟩
  unfold OfficialRuleMajorKey.compare compareAddressedSourcesWith
  dsimp only [compareLex, Ordering.byKey]
  rw [left1a, right1a, left1b, right1b, left2, right2]

/-- A descending list of observer-aligned compiler keys induces the same descending order when each
key is forgotten and its provenance tree is freshly interpreted under the chosen observer. -/
theorem sourceNodes_pairwise_of_descending_with
    {V : Type*} [Fintype V] [DecidableEq V]
    (observe : OfficialCIPNode V → ℕ)
    (m : MoleculeGraph V) (keys : List (OfficialRuleMajorKey V))
    (aligned : ∀ key, key ∈ keys → SourceAlignedWith observe m key)
    (descending : Descending keys) :
    (keys.map OfficialRuleMajorKey.sourceNodes).Pairwise fun left right =>
      compareAddressedSourcesWith observe m left right ≠ Ordering.lt := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
      rw [List.map_cons, List.pairwise_cons]
      have keyAligned := aligned key (by simp)
      have tailAligned : ∀ tail, tail ∈ keys → SourceAlignedWith observe m tail := by
        intro tail present
        exact aligned tail (by simp [present])
      have keyOverTail := (List.pairwise_cons.mp descending).1
      have tailDescending := (List.pairwise_cons.mp descending).2
      constructor
      · intro sources present
        rw [List.mem_map] at present
        obtain ⟨tail, tailPresent, rfl⟩ := present
        rw [← compare_eq_compareAddressedSourcesWith_of_sourceAlignedWith observe m key tail
          keyAligned (tailAligned tail tailPresent)]
        exact keyOverTail tail tailPresent
      · exact ih tailAligned tailDescending

/-- Independent recursive addressed-tree semantics with the Rule-1b observation chosen
independently. -/
def DeclarativeAddressedExpansionWith {V : Type*} [Fintype V] [DecidableEq V]
    (observe : OfficialCIPNode V → ℕ)
    (m : MoleculeGraph V) (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ℕ → OfficialCIPNode V → AddressedSourceLayers V → Prop
  | 0, node, sources => sources = [[([], node)]]
  | fuel + 1, node, sources =>
      if children node = [] then sources = [[([], node)]]
      else ∃ rawChildren rankedChildren,
        List.Forall₂ (DeclarativeAddressedExpansionWith observe m children fuel)
          (children node) rawChildren ∧
        rankedChildren.Perm rawChildren ∧
        rankedChildren.Pairwise (fun left right =>
          compareAddressedSourcesWith observe m left right ≠ Ordering.lt) ∧
        sources = [[([], node)]] ++ mergeAddressedChildren rankedChildren

/-- Assembly preserves exact observer-alignment between provenance nodes and all three rule
projections. -/
theorem SourceAlignedWith.assemble {V : Type*} [Fintype V] [DecidableEq V]
    (observe : OfficialCIPNode V → ℕ)
    (m : MoleculeGraph V)
    (root : OfficialRuleMajorKey V) (children : List (OfficialRuleMajorKey V))
    (rootAligned : SourceAlignedWith observe m root)
    (childrenAligned : ∀ child, child ∈ children → SourceAlignedWith observe m child) :
    SourceAlignedWith observe m (assemble root children) := by
  rcases rootAligned with ⟨root1a, root1b, root2⟩
  constructor
  · change root.rule1a ++ mergeChildren children OfficialRuleMajorKey.rule1a =
      mapSourceLayers (fun node => (ofLex (m.officialNodeAtomLabel node)).1)
        (root.sourceNodes ++ mergeChildren children OfficialRuleMajorKey.sourceNodes)
    rw [mapSourceLayers_append, root1a]
    congr 1
    exact mergeChildren_mapSourceLayers children OfficialRuleMajorKey.sourceNodes
      OfficialRuleMajorKey.rule1a _ (fun child present => (childrenAligned child present).1)
  constructor
  · change root.rule1b ++ mergeChildren children OfficialRuleMajorKey.rule1b =
      mapSourceLayers observe
        (root.sourceNodes ++ mergeChildren children OfficialRuleMajorKey.sourceNodes)
    rw [mapSourceLayers_append, root1b]
    congr 1
    exact mergeChildren_mapSourceLayers children OfficialRuleMajorKey.sourceNodes
      OfficialRuleMajorKey.rule1b _
        (fun child present => (childrenAligned child present).2.1)
  · change root.rule2 ++ mergeChildren children OfficialRuleMajorKey.rule2 =
      mapSourceLayers (fun node => (ofLex (m.officialNodeAtomLabel node)).2)
        (root.sourceNodes ++ mergeChildren children OfficialRuleMajorKey.sourceNodes)
    rw [mapSourceLayers_append, root2]
    congr 1
    exact mergeChildren_mapSourceLayers children OfficialRuleMajorKey.sourceNodes
      OfficialRuleMajorKey.rule2 _
        (fun child present => (childrenAligned child present).2.2)

/-- Local private copy of the core helper `mapM_exists_complete`, renamed because the original is
private to the core module. -/
private theorem observation_mapM_exists_complete {α V : Type*}
    (build : α → Option (OfficialRuleMajorKey V)) :
    ∀ values : List α,
      (∀ value, value ∈ values →
        ∃ key, build value = some key ∧ key.complete = true) →
      ∃ keys, values.mapM build = some keys ∧
        ∀ key, key ∈ keys → key.complete = true
  | [], _ => ⟨[], rfl, by simp⟩
  | value :: values, allComplete => by
      obtain ⟨key, keyComputed, keyComplete⟩ := allComplete value (by simp)
      have tailComplete : ∀ tailValue, tailValue ∈ values →
          ∃ key, build tailValue = some key ∧ key.complete = true := by
        intro tailValue present
        exact allComplete tailValue (List.mem_cons_of_mem value present)
      obtain ⟨keys, keysComputed, keysComplete⟩ :=
        observation_mapM_exists_complete build values tailComplete
      refine ⟨key :: keys, ?_, ?_⟩
      · simp [keyComputed, keysComputed]
      · intro observed present
        rcases List.mem_cons.mp present with rfl | tailPresent
        · exact keyComplete
        · exact keysComplete observed tailPresent

end OfficialRuleMajorKey

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One node's exact constitutional observations under a chosen Rule-1b observer. Duplicate and
phantom Rule-2 masses are already zero in `officialNodeAtomLabel`; total Rule 1b is carried by the
chosen observer rather than the stored distance. -/
def officialRuleMajorRootKeyWith (observe : OfficialCIPNode V → ℕ) (m : MoleculeGraph V)
    (node : OfficialCIPNode V) (complete : Bool) : OfficialRuleMajorKey V :=
  let label := m.officialNodeAtomLabel node
  { rule1a := [[([], (ofLex label).1)]]
    rule1b := [[([], observe node)]]
    rule2 := [[([], (ofLex label).2)]]
    sourceNodes := [[([], node)]]
    complete := complete }

/-- The legacy root key is exactly the observer specialization at `rule1bRootDistance`. -/
theorem officialRuleMajorRootKeyWith_eq_rule1bRootDistance (m : MoleculeGraph V)
    (node : OfficialCIPNode V) (complete : Bool) :
    officialRuleMajorRootKeyWith OfficialCIPNode.rule1bRootDistance m node complete =
      m.officialRuleMajorRootKey node complete :=
  rfl

theorem officialRuleMajorRootKeyWith_sourceAlignedWith (observe : OfficialCIPNode V → ℕ)
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (complete : Bool) :
    OfficialRuleMajorKey.SourceAlignedWith observe m
      (officialRuleMajorRootKeyWith observe m node complete) := by
  simp [OfficialRuleMajorKey.SourceAlignedWith, officialRuleMajorRootKeyWith,
    OfficialRuleMajorKey.mapSourceLayers, OfficialRuleMajorKey.mapObservation]

/-- Compile an arbitrary finite child enumeration into a unary rule-major key under a chosen
Rule-1b observer. There is no branch width cap. Fuel bounds only depth; an exhausted nonterminal
prefix is marked incomplete. -/
def buildOfficialRuleMajorKeyWith (observe : OfficialCIPNode V → ℕ) (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ℕ → OfficialCIPNode V → Option (OfficialRuleMajorKey V)
  | 0, node =>
      some (officialRuleMajorRootKeyWith observe m node (children node).isEmpty)
  | fuel + 1, node =>
      let childNodes := children node
      if childNodes.isEmpty then
        some (officialRuleMajorRootKeyWith observe m node true)
      else do
        let childKeys ← childNodes.mapM (buildOfficialRuleMajorKeyWith observe m children fuel)
        let sorted ← OfficialRuleMajorKey.sort? childKeys
        let root := officialRuleMajorRootKeyWith observe m node false
        some (OfficialRuleMajorKey.assemble root sorted)

private theorem mapM_congr_on {α β : Type*} (f g : α → Option β) :
    ∀ (inputs : List α), (∀ a, a ∈ inputs → f a = g a) →
      inputs.mapM f = inputs.mapM g
  | [], _ => rfl
  | a :: as, h => by
      simp only [List.mapM_cons]
      rw [h a (by simp)]
      apply bind_congr
      intro b
      have tail : ∀ c, c ∈ as → f c = g c := by
        intro c present
        exact h c (by simp [present])
      simp only [mapM_congr_on f g as tail]

/-- The legacy compiler is exactly the observer specialization of the generalized compiler at
`rule1bRootDistance`: both produce the same stored Rule-1b distances. -/
theorem buildOfficialRuleMajorKey_eq_rule1bRootDistance (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ fuel node,
      m.buildOfficialRuleMajorKey children fuel node =
        buildOfficialRuleMajorKeyWith OfficialCIPNode.rule1bRootDistance m children fuel node
  | 0, node => by
      unfold buildOfficialRuleMajorKey buildOfficialRuleMajorKeyWith
      rw [officialRuleMajorRootKeyWith_eq_rule1bRootDistance m node (children node).isEmpty]
  | fuel + 1, node => by
      unfold buildOfficialRuleMajorKey buildOfficialRuleMajorKeyWith
      dsimp only
      by_cases terminal : (children node).isEmpty = true
      · simp [terminal, officialRuleMajorRootKeyWith_eq_rule1bRootDistance]
      · simp only [if_neg terminal]
        have hmap : (children node).mapM (m.buildOfficialRuleMajorKey children fuel) =
            (children node).mapM
              (buildOfficialRuleMajorKeyWith OfficialCIPNode.rule1bRootDistance m children fuel) := by
          exact mapM_congr_on (m.buildOfficialRuleMajorKey children fuel)
            (buildOfficialRuleMajorKeyWith OfficialCIPNode.rule1bRootDistance m children fuel)
            (children node) (by
              intro child _present
              exact buildOfficialRuleMajorKey_eq_rule1bRootDistance m children fuel child)
        rw [hmap]
        apply bind_congr
        intro childKeys
        apply bind_congr
        intro sorted
        simp only [officialRuleMajorRootKeyWith_eq_rule1bRootDistance m node false]

/-- Local private copy of the core helper `mapM_mem_source`, renamed because the original is
private to the core module. -/
private theorem observation_mapM_mem_source {α β : Type*} (f : α → Option β) :
    ∀ (inputs : List α) (outputs : List β), inputs.mapM f = some outputs →
      ∀ output, output ∈ outputs → ∃ input, input ∈ inputs ∧ f input = some output
  | [], outputs, computed, output, present => by
      simp at computed
      subst outputs
      simp at present
  | input :: inputs, outputs, computed, output, present => by
      rw [List.mapM_cons] at computed
      cases headComputed : f input with
      | none =>
          rw [headComputed] at computed
          change none = some outputs at computed
          contradiction
      | some head =>
          cases tailComputed : inputs.mapM f with
          | none =>
              rw [headComputed, tailComputed] at computed
              change none = some outputs at computed
              contradiction
          | some tail =>
              rw [headComputed, tailComputed] at computed
              change some (head :: tail) = some outputs at computed
              injection computed with identity
              subst outputs
              rcases List.mem_cons.mp present with rfl | tailPresent
              · exact ⟨input, by simp, headComputed⟩
              · obtain ⟨source, sourcePresent, sourceComputed⟩ :=
                  observation_mapM_mem_source f inputs tail tailComputed output tailPresent
                exact ⟨source, by simp [sourcePresent], sourceComputed⟩

/-- Every successfully compiled key under the chosen observer refines its provenance tree
pointwise: no observation can be fabricated, dropped from one rule only, or attached to a different
sphere/parent-slot address. -/
theorem buildOfficialRuleMajorKeyWith_sourceAlignedWith (observe : OfficialCIPNode V → ℕ)
    (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ fuel node key,
      buildOfficialRuleMajorKeyWith observe m children fuel node = some key →
      OfficialRuleMajorKey.SourceAlignedWith observe m key
  | 0, node, key, computed => by
      simp [buildOfficialRuleMajorKeyWith] at computed
      subst key
      exact officialRuleMajorRootKeyWith_sourceAlignedWith observe m node _
  | fuel + 1, node, key, computed => by
      unfold buildOfficialRuleMajorKeyWith at computed
      dsimp only at computed
      by_cases terminal : (children node).isEmpty = true
      · simp [terminal] at computed
        subst key
        exact officialRuleMajorRootKeyWith_sourceAlignedWith observe m node true
      · rw [if_neg terminal] at computed
        cases childKeysComputed : (children node).mapM
            (buildOfficialRuleMajorKeyWith observe m children fuel) with
        | none => simp [childKeysComputed] at computed
        | some childKeys =>
            cases sortedComputed : OfficialRuleMajorKey.sort? childKeys with
            | none => simp [childKeysComputed, sortedComputed] at computed
            | some sorted =>
                simp [childKeysComputed, sortedComputed] at computed
                subst key
                apply OfficialRuleMajorKey.SourceAlignedWith.assemble observe m
                  (officialRuleMajorRootKeyWith observe m node false) sorted
                  (officialRuleMajorRootKeyWith_sourceAlignedWith observe m node false)
                intro child present
                have permutation := OfficialRuleMajorKey.sort?_perm
                  childKeys sorted sortedComputed
                have childPresent : child ∈ childKeys := (permutation.mem_iff).mp present
                obtain ⟨source, sourcePresent, sourceComputed⟩ :=
                  observation_mapM_mem_source (buildOfficialRuleMajorKeyWith observe m children fuel)
                    (children node) childKeys childKeysComputed child childPresent
                exact buildOfficialRuleMajorKeyWith_sourceAlignedWith observe m children fuel
                  source child sourceComputed

/-- Local private copy of the core helper `mapM_forall₂_map`, renamed because the original is
private to the core module. -/
private theorem observation_mapM_forall₂_map {α β γ : Type*} (f : α → Option β) (g : β → γ)
    (P : α → γ → Prop) :
    ∀ (inputs : List α) (outputs : List β), inputs.mapM f = some outputs →
      (∀ input output, f input = some output → P input (g output)) →
      List.Forall₂ P inputs (outputs.map g)
  | [], outputs, computed, sound => by
      simp at computed
      subst outputs
      exact List.Forall₂.nil
  | input :: inputs, outputs, computed, sound => by
      rw [List.mapM_cons] at computed
      cases headComputed : f input with
      | none =>
          rw [headComputed] at computed
          contradiction
      | some head =>
          cases tailComputed : inputs.mapM f with
          | none =>
              rw [headComputed, tailComputed] at computed
              contradiction
          | some tail =>
              rw [headComputed, tailComputed] at computed
              injection computed with identity
              subst outputs
              exact List.Forall₂.cons (sound input head headComputed)
                (observation_mapM_forall₂_map f g P inputs tail tailComputed sound)

/-- Every successful compiler result under the chosen observer satisfies the independent recursive
addressed-tree semantics. -/
theorem buildOfficialRuleMajorKeyWith_declarativeAddressedExpansionWith
    (observe : OfficialCIPNode V → ℕ)
    (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ fuel node key,
      buildOfficialRuleMajorKeyWith observe m children fuel node = some key →
      OfficialRuleMajorKey.DeclarativeAddressedExpansionWith observe m children
        fuel node key.sourceNodes
  | 0, node, key, computed => by
      simp [buildOfficialRuleMajorKeyWith] at computed
      subst key
      rfl
  | fuel + 1, node, key, computed => by
      by_cases terminal : children node = []
      · simp [buildOfficialRuleMajorKeyWith, terminal] at computed
        subst key
        simp [OfficialRuleMajorKey.DeclarativeAddressedExpansionWith, terminal]
        rfl
      · unfold buildOfficialRuleMajorKeyWith at computed
        dsimp only at computed
        rw [if_neg (by simpa using terminal)] at computed
        cases childKeysComputed : (children node).mapM
            (buildOfficialRuleMajorKeyWith observe m children fuel) with
        | none => simp [childKeysComputed] at computed
        | some childKeys =>
            cases sortedComputed : OfficialRuleMajorKey.sort? childKeys with
            | none => simp [childKeysComputed, sortedComputed] at computed
            | some sorted =>
                simp [childKeysComputed, sortedComputed] at computed
                subst key
                simp only [OfficialRuleMajorKey.DeclarativeAddressedExpansionWith, terminal,
                  ↓reduceIte]
                refine ⟨childKeys.map OfficialRuleMajorKey.sourceNodes,
                  sorted.map OfficialRuleMajorKey.sourceNodes, ?_, ?_, ?_, ?_⟩
                · apply observation_mapM_forall₂_map
                    (buildOfficialRuleMajorKeyWith observe m children fuel)
                    OfficialRuleMajorKey.sourceNodes
                    (fun child sources =>
                      OfficialRuleMajorKey.DeclarativeAddressedExpansionWith observe m children
                        fuel child sources)
                    (children node) childKeys childKeysComputed
                  intro child childKey childComputed
                  exact buildOfficialRuleMajorKeyWith_declarativeAddressedExpansionWith
                    observe m children fuel child childKey childComputed
                · exact (OfficialRuleMajorKey.sort?_perm childKeys sorted sortedComputed).map
                    OfficialRuleMajorKey.sourceNodes
                · apply OfficialRuleMajorKey.sourceNodes_pairwise_of_descending_with observe m sorted
                  · intro child childPresent
                    have permutation := OfficialRuleMajorKey.sort?_perm
                      childKeys sorted sortedComputed
                    have sourcePresent : child ∈ childKeys :=
                      (permutation.mem_iff).mp childPresent
                    obtain ⟨source, sourcePresent, sourceComputed⟩ :=
                      observation_mapM_mem_source (buildOfficialRuleMajorKeyWith observe m children fuel)
                        (children node) childKeys childKeysComputed child sourcePresent
                    exact buildOfficialRuleMajorKeyWith_sourceAlignedWith observe m children fuel
                      source child sourceComputed
                  · exact OfficialRuleMajorKey.sort?_descending childKeys sorted sortedComputed
                · change
                    (officialRuleMajorRootKeyWith observe m node false).sourceNodes ++
                        OfficialRuleMajorKey.mergeChildren sorted
                          OfficialRuleMajorKey.sourceNodes =
                      [[([], node)]] ++
                        OfficialRuleMajorKey.mergeAddressedChildren
                          (sorted.map OfficialRuleMajorKey.sourceNodes)
                  rw [OfficialRuleMajorKey.mergeChildren_sourceNodes_eq_mergeAddressedChildren]
                  rfl

/-- If the supplied expansion is exhausted within the stated fuel, the observer-parameterized
structural compiler returns a key marked complete. -/
theorem buildOfficialRuleMajorKeyWith_complete_of_expansionCompleteWithin
    (observe : OfficialCIPNode V → ℕ)
    (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ fuel node, OfficialExpansionCompleteWithin children fuel node →
      ∃ key, buildOfficialRuleMajorKeyWith observe m children fuel node = some key ∧
        key.complete = true
  | 0, node, complete => by
      change children node = [] at complete
      refine ⟨officialRuleMajorRootKeyWith observe m node true, ?_, rfl⟩
      simp [buildOfficialRuleMajorKeyWith, complete]
  | fuel + 1, node, complete => by
      by_cases terminal : children node = []
      · refine ⟨officialRuleMajorRootKeyWith observe m node true, ?_, rfl⟩
        simp [buildOfficialRuleMajorKeyWith, terminal]
      · have childrenComplete : ∀ child, child ∈ children node →
            ∃ key, buildOfficialRuleMajorKeyWith observe m children fuel child = some key ∧
              key.complete = true := by
          intro child present
          exact buildOfficialRuleMajorKeyWith_complete_of_expansionCompleteWithin
            observe m children fuel child (complete child present)
        obtain ⟨childKeys, childKeysComputed, childKeysComplete⟩ :=
          OfficialRuleMajorKey.observation_mapM_exists_complete
            (buildOfficialRuleMajorKeyWith observe m children fuel) (children node) childrenComplete
        have sortExists := OfficialRuleMajorKey.sort?_isSome_of_complete
          childKeys childKeysComplete
        obtain ⟨sorted, sortedComputed⟩ := Option.isSome_iff_exists.mp sortExists
        have sortedPermutation := OfficialRuleMajorKey.sort?_perm
          childKeys sorted sortedComputed
        have sortedComplete : ∀ key, key ∈ sorted → key.complete = true := by
          intro key present
          exact childKeysComplete key ((sortedPermutation.mem_iff).mp present)
        refine ⟨OfficialRuleMajorKey.assemble
          (officialRuleMajorRootKeyWith observe m node false) sorted, ?_, ?_⟩
        · simp [buildOfficialRuleMajorKeyWith, terminal, childKeysComputed, sortedComputed]
        · change sorted.all OfficialRuleMajorKey.complete = true
          exact List.all_eq_true.mpr sortedComplete

/-- Every successfully compiled key under the chosen observer retains its source node's Rule-1a
observation as the first sphere and first parent address. -/
theorem buildOfficialRuleMajorKeyWith_rule1a_head (observe : OfficialCIPNode V → ℕ)
    (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ fuel node key,
      buildOfficialRuleMajorKeyWith observe m children fuel node = some key →
      key.rule1a.head? = some [([], (ofLex (m.officialNodeAtomLabel node)).1)]
  | 0, node, key, computed => by
      simp [buildOfficialRuleMajorKeyWith] at computed
      subst key
      rfl
  | fuel + 1, node, key, computed => by
      unfold buildOfficialRuleMajorKeyWith at computed
      dsimp only at computed
      by_cases terminal : (children node).isEmpty = true
      · simp [terminal] at computed
        subst key
        rfl
      · rw [if_neg terminal] at computed
        cases childKeysComputed : (children node).mapM
            (buildOfficialRuleMajorKeyWith observe m children fuel) with
        | none => simp [childKeysComputed] at computed
        | some childKeys =>
            cases sortedComputed : OfficialRuleMajorKey.sort? childKeys with
            | none => simp [childKeysComputed, sortedComputed] at computed
            | some sorted =>
                simp [childKeysComputed, sortedComputed] at computed
                subst key
                rfl

@[simp] theorem officialRuleMajorRootKeyWith_rule1a (observe : OfficialCIPNode V → ℕ)
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (complete : Bool) :
    (officialRuleMajorRootKeyWith observe m node complete).rule1a =
      [[([], (ofLex (m.officialNodeAtomLabel node)).1)]] :=
  rfl

@[simp] theorem officialRuleMajorRootKeyWith_rule1b (observe : OfficialCIPNode V → ℕ)
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (complete : Bool) :
    (officialRuleMajorRootKeyWith observe m node complete).rule1b =
      [[([], observe node)]] :=
  rfl

@[simp] theorem officialRuleMajorRootKeyWith_rule2 (observe : OfficialCIPNode V → ℕ)
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (complete : Bool) :
    (officialRuleMajorRootKeyWith observe m node complete).rule2 =
      [[([], (ofLex (m.officialNodeAtomLabel node)).2)]] :=
  rfl

end MoleculeGraph

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.SourceAlignedWith_eq_rule1bRootDistance
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compareAddressedSourcesWith_eq_rule1bRootDistance
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compareAddressedSourceTraceWith_eq_rule1bRootDistance
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compareTrace_eq_compareAddressedSourceTraceWith_of_sourceAlignedWith
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compare_eq_compareAddressedSourcesWith_of_sourceAlignedWith
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.sourceNodes_pairwise_of_descending_with
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.SourceAlignedWith.assemble
assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.officialRuleMajorRootKeyWith_eq_rule1bRootDistance
assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.officialRuleMajorRootKeyWith_sourceAlignedWith
assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.buildOfficialRuleMajorKey_eq_rule1bRootDistance
assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.buildOfficialRuleMajorKeyWith_sourceAlignedWith
assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.buildOfficialRuleMajorKeyWith_declarativeAddressedExpansionWith
assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.buildOfficialRuleMajorKeyWith_complete_of_expansionCompleteWithin
assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.buildOfficialRuleMajorKeyWith_rule1a_head
assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.officialRuleMajorRootKeyWith_rule1a
assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.officialRuleMajorRootKeyWith_rule1b
assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.officialRuleMajorRootKeyWith_rule2
