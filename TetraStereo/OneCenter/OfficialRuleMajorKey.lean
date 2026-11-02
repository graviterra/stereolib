import TetraStereo.OneCenter.OfficialHierarchicalDigraph

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Format-neutral rule-major constitutional CIP keys

`OfficialHierarchicalDigraph` supplies provenance-bearing finite expansion, but its historical
layer comparator applies all three rules to one node before moving to the next node. P-92 instead
requires exhaustive rule-major comparison. This module compiles each branch independently into
sphere- and parent-slot-addressed Rule-1a, Rule-1b, and Rule-2 observations, then compares the
three complete projections in normative order.

The construction is parameterized by the child enumerator. Consequently the proof-facing finite
enumeration and the executable `Fin n` enumeration can share the same key semantics without
identifying either enumeration with chemical authority.
-/

/-- One observation at a parent-preserving positional address. -/
abbrev OfficialSparseEntry (α : Type*) := List ℕ × α

/-- A finite branch compiled into exhaustive rule-major sphere projections. -/
structure OfficialRuleMajorKey (V : Type*) where
  rule1a : List (List (OfficialSparseEntry ℕ))
  rule1b : List (List (OfficialSparseEntry ℕ))
  rule2 : List (List (OfficialSparseEntry ℕ))
  sourceNodes : List (List (OfficialSparseEntry (OfficialCIPNode V)))
  complete : Bool

namespace OfficialRuleMajorKey

/-- Explicitly typed natural-number comparison, avoiding collision with the key comparator below. -/
def compareNat (left right : ℕ) : Ordering :=
  compare left right

/-- Smaller position paths are earlier (higher-priority) sibling slots; the observation resolves
equal addresses. -/
def compareSparseEntry {α : Type*} (compareObservation : α → α → Ordering) :
    OfficialSparseEntry α → OfficialSparseEntry α → Ordering :=
  compareLex
    (Ordering.byKey Prod.fst (flip (List.compareLex compareNat)))
    (Ordering.byKey Prod.snd compareObservation)

def compareSparseLayer {α : Type*} (compareObservation : α → α → Ordering) :
    List (OfficialSparseEntry α) → List (OfficialSparseEntry α) → Ordering :=
  List.compareLex (compareSparseEntry compareObservation)

/-- Spheres compare from the root outward. -/
def compareSparseLayers {α : Type*} (compareObservation : α → α → Ordering) :
    List (List (OfficialSparseEntry α)) →
      List (List (OfficialSparseEntry α)) → Ordering :=
  List.compareLex (compareSparseLayer compareObservation)

/-- A nearer duplicated root has higher Rule-1b priority. -/
def compareRule1b : ℕ → ℕ → Ordering :=
  flip compareNat

/-- Exact P-92 constitutional rule order: exhaust Rule 1a, then Rule 1b, then Rule 2. -/
def compare {V : Type*} (left right : OfficialRuleMajorKey V) : Ordering :=
  compareLex
    (Ordering.byKey OfficialRuleMajorKey.rule1a
      (compareSparseLayers compareNat))
    (compareLex
      (Ordering.byKey OfficialRuleMajorKey.rule1b (compareSparseLayers compareRule1b))
      (Ordering.byKey OfficialRuleMajorKey.rule2
        (compareSparseLayers compareNat)))
    left right

/-- A compact rule-major certificate. Each decision summarizes the entire addressed projection for
that rule; the first non-tie is therefore the first normatively applicable rule. -/
def compareTrace {V : Type*} (left right : OfficialRuleMajorKey V) :
    List CIPRuleDecision :=
  [ { rule := CIPRuleFamily.atomicNumber
      outcome := compareSparseLayers compareNat left.rule1a right.rule1a }
  , { rule := CIPRuleFamily.duplicateAtom
      outcome := compareSparseLayers compareRule1b left.rule1b right.rule1b }
  , { rule := CIPRuleFamily.isotopeMass
      outcome := compareSparseLayers compareNat left.rule2 right.rule2 }
  ]

@[simp] theorem compareTrace_rule_order {V : Type*}
    (left right : OfficialRuleMajorKey V) :
    (compareTrace left right).map CIPRuleDecision.rule =
      [CIPRuleFamily.atomicNumber, CIPRuleFamily.duplicateAtom,
        CIPRuleFamily.isotopeMass] :=
  rfl

/-- Any strict difference anywhere in the complete addressed Rule-1a projection wins before every
Rule-1b and Rule-2 observation. -/
theorem compareTrace_outcome_eq_rule1a_of_decisive {V : Type*}
    (left right : OfficialRuleMajorKey V)
    (decisive : compareSparseLayers compareNat left.rule1a right.rule1a ≠ Ordering.eq) :
    cipTraceOutcome (compareTrace left right) =
      compareSparseLayers compareNat left.rule1a right.rule1a := by
  simp [compareTrace, cipTraceOutcome, decisive]

/-- Rule 1b can decide only after exhaustive Rule 1a equality. -/
theorem compareTrace_outcome_eq_rule1b_of_rule1a_eq {V : Type*}
    (left right : OfficialRuleMajorKey V)
    (rule1aEqual :
      compareSparseLayers compareNat left.rule1a right.rule1a = Ordering.eq)
    (rule1bDecisive :
      compareSparseLayers compareRule1b left.rule1b right.rule1b ≠ Ordering.eq) :
    cipTraceOutcome (compareTrace left right) =
      compareSparseLayers compareRule1b left.rule1b right.rule1b := by
  simp [compareTrace, cipTraceOutcome, rule1aEqual, rule1bDecisive]

/-- Evaluating the rule-tagged trace is exactly the rule-major key comparator. -/
theorem compareTrace_outcome {V : Type*}
    (left right : OfficialRuleMajorKey V) :
    cipTraceOutcome (compareTrace left right) =
      OfficialRuleMajorKey.compare left right := by
  unfold compareTrace OfficialRuleMajorKey.compare
  simp only [cipTraceOutcome]
  generalize atomicComparison :
      compareSparseLayers compareNat left.rule1a right.rule1a = atomicOutcome
  generalize duplicateComparison :
      compareSparseLayers compareRule1b left.rule1b right.rule1b = duplicateOutcome
  generalize massComparison :
      compareSparseLayers compareNat left.rule2 right.rule2 = massOutcome
  cases atomicOutcome <;> cases duplicateOutcome <;> cases massOutcome <;>
    simp_all [compareLex, Ordering.byKey]

/-- The full rule-major key comparator is an oriented transitive comparator. -/
theorem compare_transCmp {V : Type*} :
    Std.TransCmp (@OfficialRuleMajorKey.compare V) := by
  letI : Std.TransCmp compareNat := by
    unfold compareNat
    infer_instance
  letI : Std.TransCmp compareRule1b := by
    unfold compareRule1b
    infer_instance
  unfold OfficialRuleMajorKey.compare compareSparseLayers compareSparseLayer
    compareSparseEntry
  infer_instance

/-- A strict visible Rule-1a difference is safe on a truncated key. A Rule-1a tie may fall through
only after both independently compiled branches are complete. -/
def compare? {V : Type*} (left right : OfficialRuleMajorKey V) : Option Ordering :=
  match compareSparseLayers compareNat left.rule1a right.rule1a with
  | Ordering.lt => some Ordering.lt
  | Ordering.gt => some Ordering.gt
  | Ordering.eq =>
      if left.complete && right.complete then some (OfficialRuleMajorKey.compare left right)
      else none

/-- Every successful safe comparison is the total rule-major key comparison. -/
theorem compare_eq_of_compare?_eq_some {V : Type*}
    (left right : OfficialRuleMajorKey V) (outcome : Ordering)
    (computed : OfficialRuleMajorKey.compare? left right = some outcome) :
    OfficialRuleMajorKey.compare left right = outcome := by
  unfold OfficialRuleMajorKey.compare? at computed
  split at computed <;> cases outcome <;>
    simp_all [OfficialRuleMajorKey.compare, compareLex, Ordering.byKey]

/-- Complete keys always have a total safe comparison. -/
theorem compare?_isSome_of_complete {V : Type*}
    (left right : OfficialRuleMajorKey V)
    (leftComplete : left.complete = true) (rightComplete : right.complete = true) :
    (OfficialRuleMajorKey.compare? left right).isSome = true := by
  unfold OfficialRuleMajorKey.compare?
  split <;> simp [leftComplete, rightComplete]

/-- Structural insertion into descending complete-key order. -/
def insert? {V : Type*} (key : OfficialRuleMajorKey V) :
    List (OfficialRuleMajorKey V) → Option (List (OfficialRuleMajorKey V))
  | [] => some [key]
  | head :: tail =>
      match OfficialRuleMajorKey.compare? key head with
      | none => none
      | some Ordering.gt | some Ordering.eq => some (key :: head :: tail)
      | some Ordering.lt => (insert? key tail).map fun sorted => head :: sorted

/-- Structural descending sort; an unsafe comparison refuses rather than choosing an order. -/
def sort? {V : Type*} :
    List (OfficialRuleMajorKey V) → Option (List (OfficialRuleMajorKey V))
  | [] => some []
  | key :: keys => do
      let sorted ← sort? keys
      insert? key sorted

theorem insert?_perm {V : Type*} (key : OfficialRuleMajorKey V) :
    ∀ keys result, insert? key keys = some result → result.Perm (key :: keys)
  | [], result, computed => by
      simp [insert?] at computed
      subst result
      exact List.Perm.refl _
  | head :: tail, result, computed => by
      unfold insert? at computed
      cases comparison : OfficialRuleMajorKey.compare? key head with
      | none => simp [comparison] at computed
      | some decision =>
          cases decision with
          | gt =>
              simp [comparison] at computed
              subst result
              exact List.Perm.refl _
          | eq =>
              simp [comparison] at computed
              subst result
              exact List.Perm.refl _
          | lt =>
              simp only [comparison, Option.map_eq_some_iff] at computed
              rcases computed with ⟨inserted, insertedComputed, rfl⟩
              exact (List.Perm.cons head (insert?_perm key tail inserted insertedComputed)).trans
                (List.Perm.swap key head tail)

theorem sort?_perm {V : Type*} :
    ∀ (keys result : List (OfficialRuleMajorKey V)),
      OfficialRuleMajorKey.sort? keys = some result → result.Perm keys
  | [], result, computed => by
      simp [sort?] at computed
      subst result
      exact List.Perm.refl _
  | key :: keys, result, computed => by
      unfold sort? at computed
      cases sortedComputed : OfficialRuleMajorKey.sort? keys with
      | none => simp [sortedComputed] at computed
      | some sorted =>
          have tailPermutation := sort?_perm keys sorted sortedComputed
          have insertedPermutation := insert?_perm key sorted result (by
            simpa [sortedComputed] using computed)
          exact insertedPermutation.trans (List.Perm.cons key tailPermutation)

/-- A successful structural sort is not only a permutation: its sibling slots are in descending
rule-major priority. -/
def Descending {V : Type*} (keys : List (OfficialRuleMajorKey V)) : Prop :=
  keys.Pairwise fun left right => OfficialRuleMajorKey.compare left right ≠ Ordering.lt

theorem insert?_descending {V : Type*} (key : OfficialRuleMajorKey V) :
    ∀ keys result,
      Descending keys → insert? key keys = some result → Descending result
  | [], result, sorted, computed => by
      simp [insert?] at computed
      subst result
      simp [Descending]
  | head :: tail, result, sorted, computed => by
      letI : Std.TransCmp (@OfficialRuleMajorKey.compare V) := compare_transCmp
      have headOverTail : ∀ observed ∈ tail,
          OfficialRuleMajorKey.compare head observed ≠ Ordering.lt := by
        exact (List.pairwise_cons.mp sorted).1
      have tailSorted : Descending tail := by
        exact (List.pairwise_cons.mp sorted).2
      unfold insert? at computed
      cases safe : compare? key head with
      | none => simp [safe] at computed
      | some outcome =>
          have total := compare_eq_of_compare?_eq_some key head outcome safe
          cases outcome with
          | gt =>
              simp [safe] at computed
              subst result
              rw [Descending, List.pairwise_cons]
              constructor
              · intro observed present
                rcases List.mem_cons.mp present with rfl | tailPresent
                · simp [total]
                · exact Std.TransCmp.ge_trans (by simp [total])
                    (headOverTail observed tailPresent)
              · exact sorted
          | eq =>
              simp [safe] at computed
              subst result
              rw [Descending, List.pairwise_cons]
              constructor
              · intro observed present
                rcases List.mem_cons.mp present with rfl | tailPresent
                · simp [total]
                · exact Std.TransCmp.ge_trans (by simp [total])
                    (headOverTail observed tailPresent)
              · exact sorted
          | lt =>
              simp only [safe, Option.map_eq_some_iff] at computed
              rcases computed with ⟨inserted, insertedComputed, rfl⟩
              have insertedSorted := insert?_descending key tail inserted
                tailSorted insertedComputed
              rw [Descending, List.pairwise_cons]
              constructor
              · intro observed present
                have permutation := insert?_perm key tail inserted insertedComputed
                have sourcePresent : observed ∈ key :: tail :=
                  (permutation.mem_iff).mp present
                rcases List.mem_cons.mp sourcePresent with same | tailPresent
                · subst observed
                  have reverse : compare head key = Ordering.gt := by
                    rw [Std.OrientedCmp.gt_iff_lt]
                    exact total
                  simp [reverse]
                · exact headOverTail observed tailPresent
              · exact insertedSorted

theorem sort?_descending {V : Type*} :
    ∀ (keys result : List (OfficialRuleMajorKey V)),
      sort? keys = some result → Descending result
  | [], result, computed => by
      simp [sort?] at computed
      subst result
      simp [Descending]
  | key :: keys, result, computed => by
      unfold sort? at computed
      cases sortedComputed : sort? keys with
      | none => simp [sortedComputed] at computed
      | some sorted =>
          exact insert?_descending key sorted result
            (sort?_descending keys sorted sortedComputed)
            (by simpa [sortedComputed] using computed)

/-- Inserting a complete key into complete keys never refuses. -/
theorem insert?_isSome_of_complete {V : Type*}
    (key : OfficialRuleMajorKey V) (keyComplete : key.complete = true) :
    ∀ keys : List (OfficialRuleMajorKey V),
      (∀ child, child ∈ keys → child.complete = true) →
      (insert? key keys).isSome = true
  | [], _ => rfl
  | head :: tail, allComplete => by
      have headComplete : head.complete = true := allComplete head (by simp)
      have tailComplete : ∀ child, child ∈ tail → child.complete = true := by
        intro child present
        exact allComplete child (List.mem_cons_of_mem head present)
      unfold insert?
      have comparable := compare?_isSome_of_complete key head keyComplete headComplete
      cases comparison : OfficialRuleMajorKey.compare? key head with
      | none => simp [comparison] at comparable
      | some outcome =>
          cases outcome <;>
            simp [insert?_isSome_of_complete key keyComplete tail tailComplete]

/-- A list of complete keys always has a successful descending sort. -/
theorem sort?_isSome_of_complete {V : Type*} :
    ∀ keys : List (OfficialRuleMajorKey V),
      (∀ key, key ∈ keys → key.complete = true) →
      (OfficialRuleMajorKey.sort? keys).isSome = true
  | [], _ => rfl
  | key :: keys, allComplete => by
      have keyComplete : key.complete = true := allComplete key (by simp)
      have tailComplete : ∀ child, child ∈ keys → child.complete = true := by
        intro child present
        exact allComplete child (List.mem_cons_of_mem key present)
      unfold OfficialRuleMajorKey.sort?
      have sortedExists := sort?_isSome_of_complete keys tailComplete
      cases sortedComputed : OfficialRuleMajorKey.sort? keys with
      | none => simp [sortedComputed] at sortedExists
      | some sorted =>
          have sortedPermutation := sort?_perm keys sorted sortedComputed
          have sortedComplete : ∀ child, child ∈ sorted → child.complete = true := by
            intro child present
            exact tailComplete child ((sortedPermutation.mem_iff).mp present)
          simpa [sortedComputed] using
            insert?_isSome_of_complete key keyComplete sorted sortedComplete

/-- `mapM` preserves the existence and completeness of independently compiled keys. This is an
internal structural lemma for the fuel-completeness theorem below; it uses no evaluator oracle. -/
private theorem mapM_exists_complete {α V : Type*}
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
        mapM_exists_complete build values tailComplete
      refine ⟨key :: keys, ?_, ?_⟩
      · simp [keyComputed, keysComputed]
      · intro observed present
        rcases List.mem_cons.mp present with rfl | tailPresent
        · exact keyComplete
        · exact keysComplete observed tailPresent

def prefixLayer {α : Type*} (slot : ℕ) (layer : List (OfficialSparseEntry α)) :
    List (OfficialSparseEntry α) :=
  layer.map fun entry => (slot :: entry.1, entry.2)

def childLayerCount {V α : Type*} (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α))) : ℕ :=
  children.foldl (fun longest child => max longest (layers child).length) 0

/-- Merge child spheres while preserving each child's sorted sibling slot in every address. -/
def mergeChildren {V α : Type*} (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α))) :
    List (List (OfficialSparseEntry α)) :=
  let count := childLayerCount children layers
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      prefixLayer child.2 ((layers child.1).getD depth [])

/-- Join a root observation to independently compiled, priority-sorted child branches. -/
def assemble {V : Type*} (root : OfficialRuleMajorKey V)
    (sortedChildren : List (OfficialRuleMajorKey V)) : OfficialRuleMajorKey V where
  rule1a := root.rule1a ++ mergeChildren sortedChildren OfficialRuleMajorKey.rule1a
  rule1b := root.rule1b ++ mergeChildren sortedChildren OfficialRuleMajorKey.rule1b
  rule2 := root.rule2 ++ mergeChildren sortedChildren OfficialRuleMajorKey.rule2
  sourceNodes := root.sourceNodes ++
    mergeChildren sortedChildren OfficialRuleMajorKey.sourceNodes
  complete := sortedChildren.all OfficialRuleMajorKey.complete

/-- Apply an independently chosen observation to one provenance-bearing addressed node. -/
def mapObservation {V α : Type*} (observe : V → α) :
    OfficialSparseEntry V → OfficialSparseEntry α :=
  fun entry => (entry.1, observe entry.2)

/-- Project every addressed source node without changing any sphere or parent-slot address. -/
def mapSourceLayers {V α : Type*} (observe : V → α)
    (layers : List (List (OfficialSparseEntry V))) :
    List (List (OfficialSparseEntry α)) :=
  layers.map fun layer => layer.map (mapObservation observe)

theorem mapSourceLayers_append {V α : Type*} (observe : V → α)
    (left right : List (List (OfficialSparseEntry V))) :
    mapSourceLayers observe (left ++ right) =
      mapSourceLayers observe left ++ mapSourceLayers observe right := by
  simp [mapSourceLayers]

/-- Projection-refinement invariant: all three compiled constitutional rule projections are
exactly the independently observable values of the same provenance-bearing addressed nodes. -/
def SourceAligned {V : Type*} [Fintype V] [DecidableEq V] (m : MoleculeGraph V)
    (key : OfficialRuleMajorKey V) : Prop :=
  key.rule1a = mapSourceLayers
      (fun node => (ofLex (m.officialNodeAtomLabel node)).1) key.sourceNodes ∧
    key.rule1b = mapSourceLayers OfficialCIPNode.rule1bRootDistance key.sourceNodes ∧
    key.rule2 = mapSourceLayers
      (fun node => (ofLex (m.officialNodeAtomLabel node)).2) key.sourceNodes

/-- The provenance tree, before any numeric rule projection is taken. -/
abbrev AddressedSourceLayers (V : Type*) :=
  List (List (OfficialSparseEntry (OfficialCIPNode V)))

/-- Independent rule-major reading of an addressed provenance tree. The three observations are
projected afresh from source nodes, rather than read from the compiler's cached numeric fields. -/
def compareAddressedSources {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (left right : AddressedSourceLayers V) : Ordering :=
  compareLex
    (Ordering.byKey
      (mapSourceLayers fun node => (ofLex (m.officialNodeAtomLabel node)).1)
      (compareSparseLayers compareNat))
    (compareLex
      (Ordering.byKey (mapSourceLayers OfficialCIPNode.rule1bRootDistance)
        (compareSparseLayers compareRule1b))
      (Ordering.byKey
        (mapSourceLayers fun node => (ofLex (m.officialNodeAtomLabel node)).2)
        (compareSparseLayers compareNat)))
    left right

/-- Rule-tagged constitutional trace read freshly from provenance nodes. -/
def compareAddressedSourceTrace {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (left right : AddressedSourceLayers V) :
    List CIPRuleDecision :=
  [ { rule := CIPRuleFamily.atomicNumber
      outcome := compareSparseLayers compareNat
        (mapSourceLayers (fun node => (ofLex (m.officialNodeAtomLabel node)).1) left)
        (mapSourceLayers (fun node => (ofLex (m.officialNodeAtomLabel node)).1) right) }
  , { rule := CIPRuleFamily.duplicateAtom
      outcome := compareSparseLayers compareRule1b
        (mapSourceLayers OfficialCIPNode.rule1bRootDistance left)
        (mapSourceLayers OfficialCIPNode.rule1bRootDistance right) }
  , { rule := CIPRuleFamily.isotopeMass
      outcome := compareSparseLayers compareNat
        (mapSourceLayers (fun node => (ofLex (m.officialNodeAtomLabel node)).2) left)
        (mapSourceLayers (fun node => (ofLex (m.officialNodeAtomLabel node)).2) right) }
  ]

/-- The cached-key trace is exactly the fresh provenance interpretation on aligned keys. -/
theorem compareTrace_eq_compareAddressedSourceTrace_of_sourceAligned
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (left right : OfficialRuleMajorKey V)
    (leftAligned : SourceAligned m left) (rightAligned : SourceAligned m right) :
    compareTrace left right =
      compareAddressedSourceTrace m left.sourceNodes right.sourceNodes := by
  rcases leftAligned with ⟨left1a, left1b, left2⟩
  rcases rightAligned with ⟨right1a, right1b, right2⟩
  simp only [compareTrace, compareAddressedSourceTrace]
  rw [left1a, right1a, left1b, right1b, left2, right2]

/-- On aligned keys, cached-key comparison is exactly fresh comparison of the provenance trees. -/
theorem compare_eq_compareAddressedSources_of_sourceAligned
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (left right : OfficialRuleMajorKey V)
    (leftAligned : SourceAligned m left) (rightAligned : SourceAligned m right) :
    OfficialRuleMajorKey.compare left right =
      compareAddressedSources m left.sourceNodes right.sourceNodes := by
  rcases leftAligned with ⟨left1a, left1b, left2⟩
  rcases rightAligned with ⟨right1a, right1b, right2⟩
  unfold OfficialRuleMajorKey.compare compareAddressedSources
  dsimp only [compareLex, Ordering.byKey]
  rw [left1a, right1a, left1b, right1b, left2, right2]

/-- A descending list of aligned compiler keys induces the same descending order when each key is
forgotten and its provenance tree is freshly interpreted. -/
theorem sourceNodes_pairwise_of_descending
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (keys : List (OfficialRuleMajorKey V))
    (aligned : ∀ key, key ∈ keys → SourceAligned m key)
    (descending : Descending keys) :
    (keys.map OfficialRuleMajorKey.sourceNodes).Pairwise fun left right =>
      compareAddressedSources m left right ≠ Ordering.lt := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
      rw [List.map_cons, List.pairwise_cons]
      have keyAligned := aligned key (by simp)
      have tailAligned : ∀ tail, tail ∈ keys → SourceAligned m tail := by
        intro tail present
        exact aligned tail (by simp [present])
      have keyOverTail := (List.pairwise_cons.mp descending).1
      have tailDescending := (List.pairwise_cons.mp descending).2
      constructor
      · intro sources present
        rw [List.mem_map] at present
        obtain ⟨tail, tailPresent, rfl⟩ := present
        rw [← compare_eq_compareAddressedSources_of_sourceAligned m key tail
          keyAligned (tailAligned tail tailPresent)]
        exact keyOverTail tail tailPresent
      · exact ih tailAligned tailDescending

theorem prefixLayer_mapObservation {V α : Type*} (observe : V → α)
    (slot : ℕ) (layer : List (OfficialSparseEntry V)) :
    prefixLayer slot (layer.map (mapObservation observe)) =
      (prefixLayer slot layer).map (mapObservation observe) := by
  simp [prefixLayer, mapObservation, List.map_map, Function.comp_def]

theorem mapSourceLayers_getD {V α : Type*} (observe : V → α)
    (layers : List (List (OfficialSparseEntry V))) (depth : ℕ) :
    (mapSourceLayers observe layers).getD depth [] =
      (layers.getD depth []).map (mapObservation observe) := by
  unfold mapSourceLayers List.getD
  rw [List.getElem?_map]
  cases layers[depth]? <;> rfl

theorem childLayerCount_mapSourceLayers {V α W : Type*}
    (children : List (OfficialRuleMajorKey V))
    (sources : OfficialRuleMajorKey V → List (List (OfficialSparseEntry W)))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α)))
    (observe : W → α)
    (aligned : ∀ child, child ∈ children →
      layers child = mapSourceLayers observe (sources child)) :
    childLayerCount children layers = childLayerCount children sources := by
  unfold childLayerCount
  have generalized : ∀ initial,
      List.foldl (fun longest child => max longest (layers child).length)
          initial children =
        List.foldl (fun longest child => max longest (sources child).length)
          initial children := by
    induction children with
    | nil => intro initial; rfl
    | cons child children ih =>
        intro initial
        simp only [List.foldl_cons]
        have childAligned := aligned child (by simp)
        have tailAligned : ∀ tail, tail ∈ children →
            layers tail = mapSourceLayers observe (sources tail) := by
          intro tail present
          exact aligned tail (by simp [present])
        rw [childAligned]
        simp only [mapSourceLayers, List.length_map]
        exact ih tailAligned _
  exact generalized 0

/-- Maximum sphere count of already provenance-only child trees. -/
def addressedChildLayerCount {V : Type*} (children : List (AddressedSourceLayers V)) : ℕ :=
  children.foldl (fun longest child => max longest child.length) 0

/-- Parent-slot-addressed merge stated solely over provenance trees, independently of compiler
keys and their cached rule projections. -/
def mergeAddressedChildren {V : Type*} (children : List (AddressedSourceLayers V)) :
    AddressedSourceLayers V :=
  let count := addressedChildLayerCount children
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      prefixLayer child.2 (child.1.getD depth [])

theorem childLayerCount_sourceNodes {V : Type*}
    (keys : List (OfficialRuleMajorKey V)) :
    childLayerCount keys OfficialRuleMajorKey.sourceNodes =
      addressedChildLayerCount (keys.map OfficialRuleMajorKey.sourceNodes) := by
  unfold childLayerCount addressedChildLayerCount
  have generalized : ∀ initial,
      List.foldl (fun longest child => max longest child.sourceNodes.length) initial keys =
        List.foldl (fun longest child => max longest child.length) initial
          (keys.map OfficialRuleMajorKey.sourceNodes) := by
    induction keys with
    | nil => intro initial; rfl
    | cons key keys ih =>
        intro initial
        simp only [List.foldl_cons, List.map_cons]
        exact ih _
  exact generalized 0

/-- The compiler-key merge is exactly the provenance-only addressed merge after cached fields are
forgotten. -/
theorem mergeChildren_sourceNodes_eq_mergeAddressedChildren {V : Type*}
    (keys : List (OfficialRuleMajorKey V)) :
    mergeChildren keys OfficialRuleMajorKey.sourceNodes =
      mergeAddressedChildren (keys.map OfficialRuleMajorKey.sourceNodes) := by
  unfold mergeChildren mergeAddressedChildren
  rw [← childLayerCount_sourceNodes keys]
  apply List.map_congr_left
  intro depth _present
  rw [List.zipIdx_map]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro child _childPresent
  cases child
  rfl

/-- Independent recursive addressed-tree semantics. At each nonterminal node, every raw child is
expanded; the resulting provenance trees are permuted into descending freshly interpreted
rule-major priority; and their spheres are merged beneath the ranked parent slots. -/
def DeclarativeAddressedExpansion {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ℕ → OfficialCIPNode V → AddressedSourceLayers V → Prop
  | 0, node, sources => sources = [[([], node)]]
  | fuel + 1, node, sources =>
      if children node = [] then sources = [[([], node)]]
      else ∃ rawChildren rankedChildren,
        List.Forall₂ (DeclarativeAddressedExpansion m children fuel)
          (children node) rawChildren ∧
        rankedChildren.Perm rawChildren ∧
        rankedChildren.Pairwise (fun left right =>
          compareAddressedSources m left right ≠ Ordering.lt) ∧
        sources = [[([], node)]] ++ mergeAddressedChildren rankedChildren

/-- Merging sibling branches commutes with every observation projection, including empty padding
at depths shorter than the longest child. -/
theorem mergeChildren_mapSourceLayers {V α W : Type*}
    (children : List (OfficialRuleMajorKey V))
    (sources : OfficialRuleMajorKey V → List (List (OfficialSparseEntry W)))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α)))
    (observe : W → α)
    (aligned : ∀ child, child ∈ children →
      layers child = mapSourceLayers observe (sources child)) :
    mergeChildren children layers =
      mapSourceLayers observe (mergeChildren children sources) := by
  unfold mergeChildren mapSourceLayers
  rw [childLayerCount_mapSourceLayers children sources layers observe aligned]
  rw [List.map_map]
  apply List.map_congr_left
  intro depth present
  simp only [Function.comp_apply]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro child childPresent
  have keyPresent : child.1 ∈ children := List.fst_mem_of_mem_zipIdx childPresent
  rw [aligned child.1 keyPresent]
  rw [mapSourceLayers_getD]
  rw [prefixLayer_mapObservation]

/-- Assembly preserves exact alignment between provenance nodes and all three rule projections. -/
theorem SourceAligned.assemble {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    (root : OfficialRuleMajorKey V) (children : List (OfficialRuleMajorKey V))
    (rootAligned : SourceAligned m root)
    (childrenAligned : ∀ child, child ∈ children → SourceAligned m child) :
    SourceAligned m (assemble root children) := by
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
      mapSourceLayers OfficialCIPNode.rule1bRootDistance
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

end OfficialRuleMajorKey

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One node's exact constitutional observations. Duplicate and phantom Rule-2 masses are already
zero in `officialNodeAtomLabel`; total Rule 1b is carried by every node. -/
def officialRuleMajorRootKey (m : MoleculeGraph V) (node : OfficialCIPNode V)
    (complete : Bool) : OfficialRuleMajorKey V :=
  let label := m.officialNodeAtomLabel node
  { rule1a := [[([], (ofLex label).1)]]
    rule1b := [[([], node.rule1bRootDistance)]]
    rule2 := [[([], (ofLex label).2)]]
    sourceNodes := [[([], node)]]
    complete := complete }

theorem officialRuleMajorRootKey_sourceAligned (m : MoleculeGraph V)
    (node : OfficialCIPNode V) (complete : Bool) :
    OfficialRuleMajorKey.SourceAligned m (m.officialRuleMajorRootKey node complete) := by
  simp [OfficialRuleMajorKey.SourceAligned, officialRuleMajorRootKey,
    OfficialRuleMajorKey.mapSourceLayers, OfficialRuleMajorKey.mapObservation]

/-- Compile an arbitrary finite child enumeration into a unary rule-major key. There is no branch
width cap. Fuel bounds only depth; an exhausted nonterminal prefix is marked incomplete. -/
def buildOfficialRuleMajorKey (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ℕ → OfficialCIPNode V → Option (OfficialRuleMajorKey V)
  | 0, node =>
      some (m.officialRuleMajorRootKey node (children node).isEmpty)
  | fuel + 1, node =>
      let childNodes := children node
      if childNodes.isEmpty then
        some (m.officialRuleMajorRootKey node true)
      else do
        let childKeys ← childNodes.mapM (m.buildOfficialRuleMajorKey children fuel)
        let sorted ← OfficialRuleMajorKey.sort? childKeys
        let root := m.officialRuleMajorRootKey node false
        some (OfficialRuleMajorKey.assemble root sorted)

private theorem mapM_mem_source {α β : Type*} (f : α → Option β) :
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
                  mapM_mem_source f inputs tail tailComputed output tailPresent
                exact ⟨source, by simp [sourcePresent], sourceComputed⟩

/-- Every successfully compiled key refines its provenance tree pointwise: no observation can be
fabricated, dropped from one rule only, or attached to a different sphere/parent-slot address. -/
theorem buildOfficialRuleMajorKey_sourceAligned (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ fuel node key,
      m.buildOfficialRuleMajorKey children fuel node = some key →
      OfficialRuleMajorKey.SourceAligned m key
  | 0, node, key, computed => by
      simp [buildOfficialRuleMajorKey] at computed
      subst key
      exact m.officialRuleMajorRootKey_sourceAligned node _
  | fuel + 1, node, key, computed => by
      unfold buildOfficialRuleMajorKey at computed
      dsimp only at computed
      by_cases terminal : (children node).isEmpty = true
      · simp [terminal] at computed
        subst key
        exact m.officialRuleMajorRootKey_sourceAligned node true
      · rw [if_neg terminal] at computed
        cases childKeysComputed : (children node).mapM
            (m.buildOfficialRuleMajorKey children fuel) with
        | none => simp [childKeysComputed] at computed
        | some childKeys =>
            cases sortedComputed : OfficialRuleMajorKey.sort? childKeys with
            | none => simp [childKeysComputed, sortedComputed] at computed
            | some sorted =>
                simp [childKeysComputed, sortedComputed] at computed
                subst key
                apply OfficialRuleMajorKey.SourceAligned.assemble m
                  (m.officialRuleMajorRootKey node false) sorted
                  (m.officialRuleMajorRootKey_sourceAligned node false)
                intro child present
                have permutation := OfficialRuleMajorKey.sort?_perm
                  childKeys sorted sortedComputed
                have childPresent : child ∈ childKeys := (permutation.mem_iff).mp present
                obtain ⟨source, sourcePresent, sourceComputed⟩ :=
                  mapM_mem_source (m.buildOfficialRuleMajorKey children fuel)
                    (children node) childKeys childKeysComputed child childPresent
                exact buildOfficialRuleMajorKey_sourceAligned m children fuel
                  source child sourceComputed

private theorem mapM_forall₂_map {α β γ : Type*} (f : α → Option β) (g : β → γ)
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
                (mapM_forall₂_map f g P inputs tail tailComputed sound)

/-- Every successful compiler result satisfies the independent recursive addressed-tree
semantics. Thus neither input enumeration, cached projections, nor structural sorting is being
treated as its own specification. -/
theorem buildOfficialRuleMajorKey_declarativeAddressedExpansion
    (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ fuel node key,
      m.buildOfficialRuleMajorKey children fuel node = some key →
      OfficialRuleMajorKey.DeclarativeAddressedExpansion m children
        fuel node key.sourceNodes
  | 0, node, key, computed => by
      simp [buildOfficialRuleMajorKey] at computed
      subst key
      rfl
  | fuel + 1, node, key, computed => by
      by_cases terminal : children node = []
      · simp [buildOfficialRuleMajorKey, terminal] at computed
        subst key
        simp [OfficialRuleMajorKey.DeclarativeAddressedExpansion, terminal]
        rfl
      · unfold buildOfficialRuleMajorKey at computed
        dsimp only at computed
        rw [if_neg (by simpa using terminal)] at computed
        cases childKeysComputed : (children node).mapM
            (m.buildOfficialRuleMajorKey children fuel) with
        | none => simp [childKeysComputed] at computed
        | some childKeys =>
            cases sortedComputed : OfficialRuleMajorKey.sort? childKeys with
            | none => simp [childKeysComputed, sortedComputed] at computed
            | some sorted =>
                simp [childKeysComputed, sortedComputed] at computed
                subst key
                simp only [OfficialRuleMajorKey.DeclarativeAddressedExpansion, terminal,
                  ↓reduceIte]
                refine ⟨childKeys.map OfficialRuleMajorKey.sourceNodes,
                  sorted.map OfficialRuleMajorKey.sourceNodes, ?_, ?_, ?_, ?_⟩
                · apply mapM_forall₂_map
                    (m.buildOfficialRuleMajorKey children fuel)
                    OfficialRuleMajorKey.sourceNodes
                    (fun child sources =>
                      OfficialRuleMajorKey.DeclarativeAddressedExpansion m children
                        fuel child sources)
                    (children node) childKeys childKeysComputed
                  intro child childKey childComputed
                  exact buildOfficialRuleMajorKey_declarativeAddressedExpansion
                    m children fuel child childKey childComputed
                · exact (OfficialRuleMajorKey.sort?_perm childKeys sorted sortedComputed).map
                    OfficialRuleMajorKey.sourceNodes
                · apply OfficialRuleMajorKey.sourceNodes_pairwise_of_descending m sorted
                  · intro child childPresent
                    have permutation := OfficialRuleMajorKey.sort?_perm
                      childKeys sorted sortedComputed
                    have sourcePresent : child ∈ childKeys :=
                      (permutation.mem_iff).mp childPresent
                    obtain ⟨source, sourcePresent, sourceComputed⟩ :=
                      mapM_mem_source (m.buildOfficialRuleMajorKey children fuel)
                        (children node) childKeys childKeysComputed child sourcePresent
                    exact m.buildOfficialRuleMajorKey_sourceAligned children fuel
                      source child sourceComputed
                  · exact OfficialRuleMajorKey.sort?_descending childKeys sorted sortedComputed
                · change
                    (m.officialRuleMajorRootKey node false).sourceNodes ++
                        OfficialRuleMajorKey.mergeChildren sorted
                          OfficialRuleMajorKey.sourceNodes =
                      [[([], node)]] ++
                        OfficialRuleMajorKey.mergeAddressedChildren
                          (sorted.map OfficialRuleMajorKey.sourceNodes)
                  rw [OfficialRuleMajorKey.mergeChildren_sourceNodes_eq_mergeAddressedChildren]
                  rfl

/-- A child expansion is complete within zero remaining steps exactly when the current node is
terminal; with one more step, every enumerated child must be complete within the smaller bound. -/
def OfficialExpansionCompleteWithin
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ℕ → OfficialCIPNode V → Prop
  | 0, node => children node = []
  | fuel + 1, node =>
      ∀ child, child ∈ children node →
        OfficialExpansionCompleteWithin children fuel child

omit [Fintype V] [DecidableEq V] in
/-- Completeness within a depth bound depends only on the child multiset, not its enumeration. -/
theorem officialExpansionCompleteWithin_iff_of_children_perm
    (children replacement : OfficialCIPNode V → List (OfficialCIPNode V))
    (same : ∀ node, (children node).Perm (replacement node)) :
    ∀ fuel node,
      OfficialExpansionCompleteWithin children fuel node ↔
        OfficialExpansionCompleteWithin replacement fuel node
  | 0, node => by
      simp only [OfficialExpansionCompleteWithin]
      constructor
      · intro empty
        have permutation := same node
        rw [empty] at permutation
        exact permutation.symm.eq_nil
      · intro empty
        have permutation := same node
        rw [empty] at permutation
        exact permutation.eq_nil
  | fuel + 1, node => by
      simp only [OfficialExpansionCompleteWithin]
      constructor
      · intro complete child present
        exact (officialExpansionCompleteWithin_iff_of_children_perm
          children replacement same fuel child).mp
            (complete child ((same node).mem_iff.mpr present))
      · intro complete child present
        exact (officialExpansionCompleteWithin_iff_of_children_perm
          children replacement same fuel child).mpr
            (complete child ((same node).mem_iff.mp present))

/-- If the supplied expansion is exhausted within the stated fuel, the structural compiler
returns a key marked complete. This is an ordinary inductive proof checked by the Lean kernel;
it does not rely on native evaluation or compiler-trust axioms. -/
theorem buildOfficialRuleMajorKey_complete_of_expansionCompleteWithin
    (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ fuel node, OfficialExpansionCompleteWithin children fuel node →
      ∃ key, m.buildOfficialRuleMajorKey children fuel node = some key ∧
        key.complete = true
  | 0, node, complete => by
      change children node = [] at complete
      refine ⟨m.officialRuleMajorRootKey node true, ?_, rfl⟩
      simp [buildOfficialRuleMajorKey, complete]
  | fuel + 1, node, complete => by
      by_cases terminal : children node = []
      · refine ⟨m.officialRuleMajorRootKey node true, ?_, rfl⟩
        simp [buildOfficialRuleMajorKey, terminal]
      · have childrenComplete : ∀ child, child ∈ children node →
            ∃ key, m.buildOfficialRuleMajorKey children fuel child = some key ∧
              key.complete = true := by
          intro child present
          exact buildOfficialRuleMajorKey_complete_of_expansionCompleteWithin
            m children fuel child (complete child present)
        obtain ⟨childKeys, childKeysComputed, childKeysComplete⟩ :=
          OfficialRuleMajorKey.mapM_exists_complete
            (m.buildOfficialRuleMajorKey children fuel) (children node) childrenComplete
        have sortExists := OfficialRuleMajorKey.sort?_isSome_of_complete
          childKeys childKeysComplete
        obtain ⟨sorted, sortedComputed⟩ := Option.isSome_iff_exists.mp sortExists
        have sortedPermutation := OfficialRuleMajorKey.sort?_perm
          childKeys sorted sortedComputed
        have sortedComplete : ∀ key, key ∈ sorted → key.complete = true := by
          intro key present
          exact childKeysComplete key ((sortedPermutation.mem_iff).mp present)
        refine ⟨OfficialRuleMajorKey.assemble
          (m.officialRuleMajorRootKey node false) sorted, ?_, ?_⟩
        · simp [buildOfficialRuleMajorKey, terminal, childKeysComputed, sortedComputed]
        · change sorted.all OfficialRuleMajorKey.complete = true
          exact List.all_eq_true.mpr sortedComplete

/-- Every successfully compiled key retains its source node's Rule-1a observation as the first
sphere and first parent address, independently of fuel and child ordering. -/
theorem buildOfficialRuleMajorKey_rule1a_head (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ fuel node key,
      m.buildOfficialRuleMajorKey children fuel node = some key →
      key.rule1a.head? = some [([], (ofLex (m.officialNodeAtomLabel node)).1)]
  | 0, node, key, computed => by
      simp [buildOfficialRuleMajorKey] at computed
      subst key
      rfl
  | fuel + 1, node, key, computed => by
      unfold buildOfficialRuleMajorKey at computed
      dsimp only at computed
      by_cases terminal : (children node).isEmpty = true
      · simp [terminal] at computed
        subst key
        rfl
      · rw [if_neg terminal] at computed
        cases childKeysComputed : (children node).mapM
            (m.buildOfficialRuleMajorKey children fuel) with
        | none => simp [childKeysComputed] at computed
        | some childKeys =>
            cases sortedComputed : OfficialRuleMajorKey.sort? childKeys with
            | none => simp [childKeysComputed, sortedComputed] at computed
            | some sorted =>
                simp [childKeysComputed, sortedComputed] at computed
                subst key
                rfl

omit [Fintype V] [DecidableEq V] in
/-- A strict difference between the retained real-root atomic-number observations decides the
entire addressed Rule-1a projections before any later sphere can be inspected. -/
theorem officialRuleMajorKey_compare_rule1a_lt_of_heads_lt
    {left right : OfficialRuleMajorKey V} {leftZ rightZ : ℕ}
    (leftHead : left.rule1a.head? = some [([], leftZ)])
    (rightHead : right.rule1a.head? = some [([], rightZ)])
    (lower : leftZ < rightZ) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule1a right.rule1a = Ordering.lt := by
  cases leftRule : left.rule1a with
  | nil => simp [leftRule] at leftHead
  | cons leftFirst leftRest =>
      cases rightRule : right.rule1a with
      | nil => simp [rightRule] at rightHead
      | cons rightFirst rightRest =>
          simp [leftRule, rightRule] at leftHead rightHead
          subst leftFirst
          subst rightFirst
          have compared : OfficialRuleMajorKey.compareNat leftZ rightZ = Ordering.lt := by
            exact compare_lt_iff_lt.mpr lower
          simp [OfficialRuleMajorKey.compareSparseLayers,
            OfficialRuleMajorKey.compareSparseLayer,
            OfficialRuleMajorKey.compareSparseEntry,
            List.compareLex, compareLex, Ordering.byKey, flip, compared]

omit [Fintype V] [DecidableEq V] in
/-- The symmetric strict root case: a larger retained real-root atomic number decides Rule 1a
before any deeper sphere or later rule can be inspected. -/
theorem officialRuleMajorKey_compare_rule1a_gt_of_heads_gt
    {left right : OfficialRuleMajorKey V} {leftZ rightZ : ℕ}
    (leftHead : left.rule1a.head? = some [([], leftZ)])
    (rightHead : right.rule1a.head? = some [([], rightZ)])
    (higher : rightZ < leftZ) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule1a right.rule1a = Ordering.gt := by
  cases leftRule : left.rule1a with
  | nil => simp [leftRule] at leftHead
  | cons leftFirst leftRest =>
      cases rightRule : right.rule1a with
      | nil => simp [rightRule] at rightHead
      | cons rightFirst rightRest =>
          simp [leftRule, rightRule] at leftHead rightHead
          subst leftFirst
          subst rightFirst
          have compared : OfficialRuleMajorKey.compareNat leftZ rightZ = Ordering.gt := by
            exact compare_gt_iff_gt.mpr higher
          simp [OfficialRuleMajorKey.compareSparseLayers,
            OfficialRuleMajorKey.compareSparseLayer,
            OfficialRuleMajorKey.compareSparseEntry,
            List.compareLex, compareLex, Ordering.byKey, flip, compared]

/-- Iterating the official breadth-first frontier distributes over independent branch roots. -/
theorem officialCIPFrontier_flatMap (m : MoleculeGraph V) :
    ∀ fuel (frontier : List (OfficialCIPNode V)),
      m.officialCIPFrontier fuel frontier =
        frontier.flatMap fun node => m.officialCIPFrontier fuel [node]
  | 0, frontier => by simp [officialCIPFrontier]
  | fuel + 1, frontier => by
      rw [officialCIPFrontier]
      rw [officialCIPFrontier_flatMap m fuel]
      simp only [officialCIPNextFrontier, List.flatMap_assoc]
      apply List.flatMap_congr
      intro node _present
      rw [officialCIPFrontier]
      rw [officialCIPFrontier_flatMap m fuel]
      simp [officialCIPNextFrontier]

/-- Recursive expansion completeness is exactly emptiness of the next breadth-first frontier. -/
theorem officialExpansionCompleteWithin_iff_frontier_succ_nil (m : MoleculeGraph V) :
    ∀ fuel node,
      OfficialExpansionCompleteWithin m.officialCIPChildren fuel node ↔
        m.officialCIPFrontier (fuel + 1) [node] = []
  | 0, node => by
      simp [OfficialExpansionCompleteWithin, officialCIPFrontier,
        officialCIPNextFrontier]
  | fuel + 1, node => by
      rw [show (fuel + 1) + 1 = (fuel + 1) + 1 by rfl]
      simp only [OfficialExpansionCompleteWithin]
      rw [officialCIPFrontier]
      simp only [officialCIPNextFrontier, List.flatMap_singleton]
      rw [officialCIPFrontier_flatMap m (fuel + 1)]
      simp only [List.flatMap_eq_nil_iff]
      constructor
      · intro complete child present
        exact (officialExpansionCompleteWithin_iff_frontier_succ_nil m fuel child).mp
          (complete child present)
      · intro empty child present
        exact (officialExpansionCompleteWithin_iff_frontier_succ_nil m fuel child).mpr
          (empty child present)

/-- The established finite-atom frontier bound supplies the exact completeness premise needed by
the rule-major compiler for every ordinary ligand root. -/
theorem officialExpansionCompleteWithin_rootFromEdge_default (m : MoleculeGraph V)
    {center ligand : V} (different : ligand ≠ center) :
    OfficialExpansionCompleteWithin m.officialCIPChildren (Fintype.card V + 1)
      (OfficialCIPNode.rootFromEdge center ligand) := by
  apply (officialExpansionCompleteWithin_iff_frontier_succ_nil m _ _).mpr
  have exhausted := m.officialCIPFrontier_rootFromEdge_eq_nil_card_add_one different
  rw [show Fintype.card V + 1 + 1 = 1 + (Fintype.card V + 1) by omega]
  rw [m.officialCIPFrontier_add 1 (Fintype.card V + 1)]
  rw [exhausted]
  rfl

/-- Proof-facing specialization using the generic official child expansion. -/
noncomputable def buildReferenceOfficialRuleMajorKey (m : MoleculeGraph V)
    (fuel : ℕ) (node : OfficialCIPNode V) : Option (OfficialRuleMajorKey V) :=
  m.buildOfficialRuleMajorKey m.officialCIPChildren fuel node

@[simp] theorem officialRuleMajorRootKey_rule1a (m : MoleculeGraph V)
    (node : OfficialCIPNode V) (complete : Bool) :
    (m.officialRuleMajorRootKey node complete).rule1a =
      [[([], (ofLex (m.officialNodeAtomLabel node)).1)]] :=
  rfl

@[simp] theorem officialRuleMajorRootKey_rule1b (m : MoleculeGraph V)
    (node : OfficialCIPNode V) (complete : Bool) :
    (m.officialRuleMajorRootKey node complete).rule1b =
      [[([], node.rule1bRootDistance)]] :=
  rfl

@[simp] theorem officialRuleMajorRootKey_rule2 (m : MoleculeGraph V)
    (node : OfficialCIPNode V) (complete : Bool) :
    (m.officialRuleMajorRootKey node complete).rule2 =
      [[([], (ofLex (m.officialNodeAtomLabel node)).2)]] :=
  rfl

end MoleculeGraph

end TetraStereo.OneCenter
