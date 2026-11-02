import TetraStereo.OneCenter.DeclarativeCIPStereochemical
import TetraStereo.OneCenter.DeclarativeCIPConstitutionalOrderLaws
import TetraStereo.OneCenter.DeclarativeCIPPreorder
import Mathlib.Data.List.Lex
import Mathlib.Order.WithBot

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

open scoped Classical

universe u

/-!
# One evidence-aware canonical addressing family for the eight ordinary rules

`StereochemicalProblemData` shares one `admissibleAddressing` among Rules 1a, 1b, 2, 3, 4a, 4b, 4c
and 5.  The three-rule canonical family ranks siblings only by their constitutional keys, so
constitutionally tied siblings carrying different Rule-3--5 evidence may be listed in either order,
and the stereochemical hierarchy outcome then depends on that choice.

This module ranks siblings by a lexicographic pair: the existing constitutional vector key, then a
five-component stereochemical vector key read from the semantic evidence.  Every component is laid
out over the same recursive sibling order.

* The first component of the new key *is* the existing `ruleKey` (`ordinaryKey_fst`), so every
  ordinary-canonical addressing is canonical for the three-rule family
  (`ordinaryCanonical_canonical`).  Later evidence only refines constitutional ties.
* Stereochemical observations are compared in genuine Mathlib orders: addressed hierarchies are
  encoded as `List (List ((List ℕ)ᵒᵈ ×ₗ ℕ))`, which reproduces `compareAddressedHierarchy`, including
  its reversed address order, exactly (`compareAddressedHierarchy_outcome_iff`).

`RootedDigraph.Addressing.EvidencePreserved` is an explicit semantic input of the specification
(`StereochemicalProblemData.evidence_invariant`); graph isomorphism alone does not imply it.
-/

/-! ## From core lexicographic comparison to Mathlib list order -/

/-- Relational reading of a three-valued comparison against a linear order. -/
theorem orderedKeyOutcome_iff_compare {V : Type*} [LinearOrder V] (left right : V)
    (outcome : Ordering) : OrderedKeyOutcome left right outcome ↔ compare left right = outcome := by
  cases outcome
  · rw [compare_lt_iff_lt]
    exact ⟨fun h => by cases h; assumption, fun h => .lt h⟩
  · rw [compare_eq_iff_eq]
    exact ⟨fun h => by cases h; assumption, fun h => .eq h⟩
  · rw [compare_gt_iff_gt]
    exact ⟨fun h => by cases h; assumption, fun h => .gt h⟩

theorem orderedKeyOutcome_of_lt {V : Type*} [LinearOrder V] {a b : V} (h : a < b)
    (outcome : Ordering) : OrderedKeyOutcome a b outcome ↔ Ordering.lt = outcome := by
  constructor
  · intro hout
    cases hout with
    | lt _ => rfl
    | eq heq => exact absurd (heq ▸ h) (lt_irrefl _)
    | gt hgt => exact absurd (lt_trans h hgt) (lt_irrefl _)
  · rintro rfl
    exact .lt h

theorem orderedKeyOutcome_of_eq {V : Type*} [LinearOrder V] {a b : V} (h : a = b)
    (outcome : Ordering) : OrderedKeyOutcome a b outcome ↔ Ordering.eq = outcome := by
  subst h
  constructor
  · intro hout
    cases hout with
    | lt hlt => exact absurd hlt (lt_irrefl _)
    | eq _ => rfl
    | gt hgt => exact absurd hgt (lt_irrefl _)
  · rintro rfl
    exact .eq rfl

theorem orderedKeyOutcome_of_gt {V : Type*} [LinearOrder V] {a b : V} (h : b < a)
    (outcome : Ordering) : OrderedKeyOutcome a b outcome ↔ Ordering.gt = outcome := by
  constructor
  · intro hout
    cases hout with
    | lt hlt => exact absurd (lt_trans h hlt) (lt_irrefl _)
    | eq heq => exact absurd (heq ▸ h) (lt_irrefl _)
    | gt _ => rfl
  · rintro rfl
    exact .gt h

/-- A comparator represented by a map into a linear order. -/
def RepresentedBy {α β : Type*} [LinearOrder β] (cmp : α → α → Ordering) (f : α → β) : Prop :=
  ∀ a b outcome, cmp a b = outcome ↔ OrderedKeyOutcome (f a) (f b) outcome

theorem RepresentedBy.cmp_eq {α β : Type*} [LinearOrder β] {cmp : α → α → Ordering}
    {f : α → β} (h : RepresentedBy cmp f) {a b : α} :
    (f a < f b → cmp a b = Ordering.lt) ∧ (f a = f b → cmp a b = Ordering.eq) ∧
      (f b < f a → cmp a b = Ordering.gt) :=
  ⟨fun hlt => (h a b _).2 (.lt hlt), fun heq => (h a b _).2 (.eq heq),
    fun hgt => (h a b _).2 (.gt hgt)⟩

theorem orderedKeyOutcome_cons_same {β : Type*} [LinearOrder β] (head : β) (l m : List β)
    (outcome : Ordering) :
    OrderedKeyOutcome (head :: l) (head :: m) outcome ↔ OrderedKeyOutcome l m outcome := by
  rcases lt_trichotomy l m with h | h | h
  · rw [orderedKeyOutcome_of_lt h, orderedKeyOutcome_of_lt (List.Lex.cons h)]
  · rw [orderedKeyOutcome_of_eq h, orderedKeyOutcome_of_eq (by rw [h])]
  · rw [orderedKeyOutcome_of_gt h, orderedKeyOutcome_of_gt (List.Lex.cons h)]

theorem representedBy_compareLex {α β : Type*} [LinearOrder β] {cmp : α → α → Ordering}
    {f : α → β} (h : RepresentedBy cmp f) :
    RepresentedBy (List.compareLex cmp) (fun l => l.map f) := by
  intro l m outcome
  induction l generalizing m outcome with
  | nil =>
      cases m with
      | nil => exact (orderedKeyOutcome_of_eq rfl outcome).symm
      | cons y ys =>
          show Ordering.lt = outcome ↔ _
          exact (orderedKeyOutcome_of_lt (List.nil_lt_cons _ _) outcome).symm
  | cons x xs ih =>
      cases m with
      | nil =>
          show Ordering.gt = outcome ↔ _
          exact (orderedKeyOutcome_of_gt (List.nil_lt_cons _ _) outcome).symm
      | cons y ys =>
          rw [List.compareLex_cons_cons]
          show _ ↔ OrderedKeyOutcome (f x :: xs.map f) (f y :: ys.map f) outcome
          obtain ⟨hlt, heq, hgt⟩ := h.cmp_eq (a := x) (b := y)
          rcases lt_trichotomy (f x) (f y) with hxy | hxy | hxy
          · rw [hlt hxy, orderedKeyOutcome_of_lt (List.Lex.rel hxy)]
            rfl
          · rw [heq hxy, hxy, orderedKeyOutcome_cons_same]
            exact ih ys outcome
          · rw [hgt hxy, orderedKeyOutcome_of_gt (List.Lex.rel hxy)]
            rfl

theorem toLex_lt_of_fst {β γ : Type*} [LinearOrder β] [LinearOrder γ] {a₁ a₂ : β} {b₁ b₂ : γ}
    (h : a₁ < a₂) : (toLex (a₁, b₁) : β ×ₗ γ) < toLex (a₂, b₂) :=
  Prod.Lex.lt_iff.2 (Or.inl h)

theorem toLex_lt_of_snd {β γ : Type*} [LinearOrder β] [LinearOrder γ] {a₁ a₂ : β} {b₁ b₂ : γ}
    (ha : a₁ = a₂) (h : b₁ < b₂) : (toLex (a₁, b₁) : β ×ₗ γ) < toLex (a₂, b₂) :=
  Prod.Lex.lt_iff.2 (Or.inr ⟨ha, h⟩)

/-- Lexicographic combination of two represented comparators is represented by the lexicographic
pair of their representations. -/
theorem representedBy_then {α β γ : Type*} [LinearOrder β] [LinearOrder γ]
    {first second : α → α → Ordering} {f : α → β} {g : α → γ}
    (hfirst : RepresentedBy first f) (hsecond : RepresentedBy second g) :
    RepresentedBy (fun a b => (first a b).then (second a b)) (fun a => toLex (f a, g a)) := by
  intro a b outcome
  dsimp only
  obtain ⟨hlt, heq, hgt⟩ := hfirst.cmp_eq (a := a) (b := b)
  rcases lt_trichotomy (f a) (f b) with h | h | h
  · rw [hlt h, orderedKeyOutcome_of_lt (toLex_lt_of_fst h)]
    rfl
  · rw [heq h]
    show second a b = outcome ↔ _
    rw [hsecond a b outcome]
    rcases lt_trichotomy (g a) (g b) with h' | h' | h'
    · rw [orderedKeyOutcome_of_lt h', orderedKeyOutcome_of_lt (toLex_lt_of_snd h h')]
    · rw [orderedKeyOutcome_of_eq h', orderedKeyOutcome_of_eq (by rw [h, h'])]
    · rw [orderedKeyOutcome_of_gt h', orderedKeyOutcome_of_gt (toLex_lt_of_snd h.symm h')]
  · rw [hgt h, orderedKeyOutcome_of_gt (toLex_lt_of_fst h)]
    rfl

/-! ## Encoding addressed hierarchies -/

/-- One addressed observation: addresses in reversed order, then the observed priority. -/
abbrev StereoEntry := Lex ((List ℕ)ᵒᵈ × ℕ)

/-- An encoded complete addressed observation hierarchy. -/
abbrev StereoCode := List (List StereoEntry)

def encodeEntry {α : Type*} (priority : α → ℕ) (entry : List ℕ × α) : StereoEntry :=
  toLex (OrderDual.toDual entry.1, priority entry.2)

def encodeHierarchy {α : Type*} (priority : α → ℕ) (hierarchy : AddressedHierarchy α) :
    StereoCode :=
  hierarchy.map fun layer => layer.map (encodeEntry priority)

theorem representedBy_compare_nat : RepresentedBy (compare : ℕ → ℕ → Ordering) id := by
  intro a b outcome
  show compare a b = outcome ↔ OrderedKeyOutcome a b outcome
  rcases lt_trichotomy a b with h | h | h
  · rw [orderedKeyOutcome_of_lt h, Nat.compare_eq_lt.2 h]
  · rw [orderedKeyOutcome_of_eq h, h, Nat.compare_eq_eq.2 rfl]
  · rw [orderedKeyOutcome_of_gt h, Nat.compare_eq_gt.2 h]

theorem representedBy_compareSemanticAddress :
    RepresentedBy compareSemanticAddress (fun address : List ℕ => address) := by
  intro a b outcome
  have h := representedBy_compareLex representedBy_compare_nat a b outcome
  simpa [compareSemanticAddress] using h

theorem representedBy_reversedAddress :
    RepresentedBy (fun a b : List ℕ => compareSemanticAddress b a)
      (fun address : List ℕ => OrderDual.toDual address) := by
  intro a b outcome
  dsimp only
  rw [representedBy_compareSemanticAddress b a outcome]
  rcases lt_trichotomy a b with h | h | h
  · rw [orderedKeyOutcome_of_gt h, orderedKeyOutcome_of_gt
      (show OrderDual.toDual b < OrderDual.toDual a from h)]
  · rw [orderedKeyOutcome_of_eq h.symm, orderedKeyOutcome_of_eq (by rw [h])]
  · rw [orderedKeyOutcome_of_lt h, orderedKeyOutcome_of_lt
      (show OrderDual.toDual a < OrderDual.toDual b from h)]

theorem representedBy_priority {α : Type*} (priority : α → ℕ) :
    RepresentedBy (fun a b : α => compare (priority a) (priority b)) priority :=
  fun a b outcome => representedBy_compare_nat (priority a) (priority b) outcome

theorem representedBy_compareAddressedEntry {α : Type*} (priority : α → ℕ) :
    RepresentedBy (compareAddressedEntry priority) (encodeEntry priority) := by
  have h := representedBy_then
    (first := fun a b : List ℕ × α => compareSemanticAddress b.1 a.1)
    (f := fun a : List ℕ × α => OrderDual.toDual a.1)
    (second := fun a b : List ℕ × α => compare (priority a.2) (priority b.2))
    (g := fun a : List ℕ × α => priority a.2)
    (fun a b o => representedBy_reversedAddress a.1 b.1 o)
    (fun a b o => representedBy_priority priority a.2 b.2 o)
  exact h

theorem representedBy_compareAddressedHierarchy {α : Type*} (priority : α → ℕ) :
    RepresentedBy (compareAddressedHierarchy priority) (encodeHierarchy priority) :=
  representedBy_compareLex (representedBy_compareLex (representedBy_compareAddressedEntry priority))

/-- Rule-4b readings embed into the same carrier, every entry at the empty address. -/
def encodeReadings (readings : List (List ℕ)) : StereoCode :=
  readings.map fun reading => reading.map fun value => toLex (OrderDual.toDual [], value)

theorem representedBy_rule4b :
    RepresentedBy (compare : List (List ℕ) → List (List ℕ) → Ordering) encodeReadings := by
  have hentry : RepresentedBy (fun a b : ℕ => (Ordering.eq).then (compare a b))
      (fun value : ℕ => (toLex (OrderDual.toDual ([] : List ℕ), value) : StereoEntry)) :=
    representedBy_then (first := fun _ _ => Ordering.eq)
      (f := fun _ : ℕ => OrderDual.toDual ([] : List ℕ))
      (fun _ _ o => (orderedKeyOutcome_of_eq rfl o).symm) representedBy_compare_nat
  exact representedBy_compareLex (representedBy_compareLex hentry)

/-! ## Optional rule observations -/

/-- Lift an optional encoded observation: absence is the least value. -/
def liftObservation {α : Type*} (encode : α → StereoCode) : Option α → WithBot StereoCode
  | none => ⊥
  | some value => (encode value : WithBot StereoCode)

theorem optionalOutcome_iff {α : Type*} {relation : α → α → Ordering → Prop}
    {encode : α → StereoCode}
    (h : ∀ a b outcome, relation a b outcome ↔ OrderedKeyOutcome (encode a) (encode b) outcome)
    (left right : Option α) (outcome : Ordering) :
    OptionalOutcome relation left right outcome ↔
      OrderedKeyOutcome (liftObservation encode left) (liftObservation encode right) outcome := by
  constructor
  · intro hout
    cases hout with
    | both hrel =>
        cases (h _ _ _).1 hrel with
        | gt hlt => exact .gt (WithBot.coe_lt_coe.2 hlt)
        | lt hlt => exact .lt (WithBot.coe_lt_coe.2 hlt)
        | eq heq => exact .eq (congrArg (fun x : StereoCode => (x : WithBot StereoCode)) heq)
    | leftOnly => exact .gt (WithBot.bot_lt_coe _)
    | rightOnly => exact .lt (WithBot.bot_lt_coe _)
    | neither => exact .eq rfl
  · intro hout
    cases left with
    | none =>
        cases right with
        | none =>
            cases hout with
            | eq _ => exact .neither
            | gt hlt => exact absurd hlt (not_lt_bot)
            | lt hlt => exact absurd hlt (not_lt_bot)
        | some b =>
            cases hout with
            | lt _ => exact .rightOnly
            | eq heq => exact absurd heq.symm (WithBot.coe_ne_bot)
            | gt hlt => exact absurd hlt (not_lt_bot)
    | some a =>
        cases right with
        | none =>
            cases hout with
            | gt _ => exact .leftOnly
            | eq heq => exact absurd heq (WithBot.coe_ne_bot)
            | lt hlt => exact absurd hlt (not_lt_bot)
        | some b =>
            apply OptionalOutcome.both
            apply (h a b outcome).2
            cases hout with
            | gt hlt => exact .gt (WithBot.coe_lt_coe.1 hlt)
            | lt hlt => exact .lt (WithBot.coe_lt_coe.1 hlt)
            | eq heq => exact .eq (WithBot.coe_injective heq)

/-- The encoded value of one stereochemical rule in an optional node observation. -/
def stereoValue : StereochemicalRule → Option StereochemicalObservation → WithBot StereoCode
  | .rule3DoubleBondGeometry, observation =>
      liftObservation (fun s : Rule3Signature => encodeHierarchy Rule3Geometry.priority s.layers)
        (observation.bind (·.rule3))
  | .rule4aStereogenicUnitKind, observation =>
      liftObservation (fun s : Rule4aSignature =>
        encodeHierarchy StereogenicUnitKind.priority s.layers) (observation.bind (·.rule4a))
  | .rule4bLikeUnlikeDescriptorPairs, observation =>
      liftObservation (fun s : Rule4bSignature => encodeReadings s.readings)
        (observation.bind (·.rule4b))
  | .rule4cPseudoasymmetricDescriptor, observation =>
      liftObservation (fun s : Rule4cSignature => encodeHierarchy id s.layers)
        (observation.bind (·.rule4c))
  | .rule5EnantiomorphicDescriptor, observation =>
      liftObservation (fun s : Rule5Signature => encodeHierarchy id s.layers)
        (observation.bind (·.rule5))

/-- **Unary characterization of every stereochemical node comparison.** -/
theorem stereochemicalNodeOutcome_iff (rule : StereochemicalRule)
    (left right : Option StereochemicalObservation) (outcome : Ordering) :
    StereochemicalNodeOutcome rule left right outcome ↔
      OrderedKeyOutcome (stereoValue rule left) (stereoValue rule right) outcome := by
  cases rule
  · exact optionalOutcome_iff (fun a b o => representedBy_compareAddressedHierarchy _ a.layers
      b.layers o) _ _ _
  · exact optionalOutcome_iff (fun a b o => representedBy_compareAddressedHierarchy _ a.layers
      b.layers o) _ _ _
  · exact optionalOutcome_iff (fun a b o => representedBy_rule4b a.readings b.readings o) _ _ _
  · exact optionalOutcome_iff (fun a b o => representedBy_compareAddressedHierarchy _ a.layers
      b.layers o) _ _ _
  · exact optionalOutcome_iff (fun a b o => representedBy_compareAddressedHierarchy _ a.layers
      b.layers o) _ _ _

/-! ## The ordinary vector key -/

open Certificate.CanonicalSphereKey (Key assemble sortDesc keyObservation slotOf WellShaped pad)
open RootedDigraph

/-- Position of a stereochemical rule in the stereochemical vector. -/
def stereoIndex : StereochemicalRule → ℕ
  | .rule3DoubleBondGeometry => 0
  | .rule4aStereogenicUnitKind => 1
  | .rule4bLikeUnlikeDescriptorPairs => 2
  | .rule4cPseudoasymmetricDescriptor => 3
  | .rule5EnantiomorphicDescriptor => 4

/-- Labels of the stereochemical layouts. -/
abbrev StereoLabel := WithBot StereoCode

/-- The ordinary key: the constitutional vector key, then the stereochemical vector key. -/
abbrev OrdinaryKey := Lex (List (Key ℤ) × List (Key StereoLabel))

section OrdinaryKeys

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  (graph : RootedDigraph Atom) (evidence : StereochemicalEvidence graph)

local instance ordinaryNodeFintype1 : Fintype graph.Node := graph.nodeFintype

/-- The encoded evidence of one stereochemical rule at a node. -/
def stereoLabel (rule : StereochemicalRule) (node : graph.Node) : StereoLabel :=
  stereoValue rule (some (evidence node))

/-- One stereochemical component, laid out over ranked ordinary keys of the children. -/
def stereoComponent (W D : ℕ) (rule : StereochemicalRule) (node : graph.Node)
    (ranked : List OrdinaryKey) : Key StereoLabel :=
  assemble W D (stereoLabel graph evidence rule node)
    (ranked.map fun key => (ofLex key).2.getD (stereoIndex rule) [])

/-- The constitutional projection of ranked ordinary keys. -/
def constitutionalProjection (ranked : List OrdinaryKey) : List (List (Key ℤ)) :=
  ranked.map fun key => (ofLex key).1

/-- **The ordinary key.**  Children are ranked by their ordinary keys in descending lexicographic
order: first by the constitutional vector, then by the stereochemical vector.  All eight
components are laid out over that one ranking. -/
def ordinaryKey (W D : ℕ) (node : graph.Node) : OrdinaryKey :=
  let ranked := sortDesc ((graph.childList node).attach.map fun child => ordinaryKey W D child.1)
  toLex
    ([ruleComponent molecule graph W D .rule1aAtomicNumber node (constitutionalProjection ranked),
      ruleComponent molecule graph W D .rule1bDuplicateNodeProximity node
        (constitutionalProjection ranked),
      ruleComponent molecule graph W D .rule2AtomicMass node (constitutionalProjection ranked)],
     [stereoComponent graph evidence W D .rule3DoubleBondGeometry node ranked,
      stereoComponent graph evidence W D .rule4aStereogenicUnitKind node ranked,
      stereoComponent graph evidence W D .rule4bLikeUnlikeDescriptorPairs node ranked,
      stereoComponent graph evidence W D .rule4cPseudoasymmetricDescriptor node ranked,
      stereoComponent graph evidence W D .rule5EnantiomorphicDescriptor node ranked])
termination_by graph.height + 1 - graph.depth node
decreasing_by
  have hchild := (graph.mem_childList).1 child.2
  have hdepth := graph.child_depth hchild
  have hle := graph.depth_le_height child.1
  omega

/-- The ranked ordinary keys of the children of a node. -/
def rankedOrdinaryKeys (W D : ℕ) (node : graph.Node) : List OrdinaryKey :=
  sortDesc ((graph.childList node).map (ordinaryKey molecule graph evidence W D))

theorem ordinaryKey_eq (W D : ℕ) (node : graph.Node) :
    ordinaryKey molecule graph evidence W D node =
      toLex
        ([ruleComponent molecule graph W D .rule1aAtomicNumber node
            (constitutionalProjection (rankedOrdinaryKeys molecule graph evidence W D node)),
          ruleComponent molecule graph W D .rule1bDuplicateNodeProximity node
            (constitutionalProjection (rankedOrdinaryKeys molecule graph evidence W D node)),
          ruleComponent molecule graph W D .rule2AtomicMass node
            (constitutionalProjection (rankedOrdinaryKeys molecule graph evidence W D node))],
         [stereoComponent graph evidence W D .rule3DoubleBondGeometry node
            (rankedOrdinaryKeys molecule graph evidence W D node),
          stereoComponent graph evidence W D .rule4aStereogenicUnitKind node
            (rankedOrdinaryKeys molecule graph evidence W D node),
          stereoComponent graph evidence W D .rule4bLikeUnlikeDescriptorPairs node
            (rankedOrdinaryKeys molecule graph evidence W D node),
          stereoComponent graph evidence W D .rule4cPseudoasymmetricDescriptor node
            (rankedOrdinaryKeys molecule graph evidence W D node),
          stereoComponent graph evidence W D .rule5EnantiomorphicDescriptor node
            (rankedOrdinaryKeys molecule graph evidence W D node)]) := by
  rw [ordinaryKey]
  simp only [List.attach_map_val, rankedOrdinaryKeys]

theorem ordinaryKey_stereo_getD (W D : ℕ) (rule : StereochemicalRule) (node : graph.Node) :
    (ofLex (ordinaryKey molecule graph evidence W D node)).2.getD (stereoIndex rule) [] =
      stereoComponent graph evidence W D rule node
        (rankedOrdinaryKeys molecule graph evidence W D node) := by
  rw [ordinaryKey_eq]
  cases rule <;> rfl

theorem fst_le_of_le {x y : OrdinaryKey} (h : x ≤ y) : (ofLex x).1 ≤ (ofLex y).1 := by
  rcases Prod.Lex.le_iff.1 h with h | h
  · exact h.le
  · exact h.1.le

/-- **Compatibility.**  The constitutional half of the ordinary key is the existing three-rule
vector key: later evidence only refines constitutional ties. -/
theorem ordinaryKey_fst (W D : ℕ) :
    ∀ node, (ofLex (ordinaryKey molecule graph evidence W D node)).1 =
      ruleKey molecule graph W D node := by
  intro node
  refine node_induction graph (motive := fun node =>
    (ofLex (ordinaryKey molecule graph evidence W D node)).1 = ruleKey molecule graph W D node)
    ?_ node
  intro node ih
  have hproj : constitutionalProjection (rankedOrdinaryKeys molecule graph evidence W D node) =
      sortDesc ((graph.childList node).map (ruleKey molecule graph W D)) := by
    have hperm : (constitutionalProjection (rankedOrdinaryKeys molecule graph evidence W D node)).Perm
        ((graph.childList node).map (ruleKey molecule graph W D)) := by
      unfold constitutionalProjection rankedOrdinaryKeys
      refine ((Certificate.CanonicalSphereKey.sortDesc_perm _).map _).trans ?_
      rw [List.map_map]
      exact List.Perm.of_eq (List.map_congr_left fun child hchild =>
        ih child ((graph.mem_childList).1 hchild))
    have hsorted : (constitutionalProjection
        (rankedOrdinaryKeys molecule graph evidence W D node)).Pairwise fun x y => y ≤ x := by
      unfold constitutionalProjection
      rw [List.pairwise_map]
      exact (Certificate.CanonicalSphereKey.sortDesc_pairwise _).imp fun h => fst_le_of_le h
    rw [Certificate.CanonicalSphereKey.sortDesc_eq_of_perm hperm.symm,
      Certificate.CanonicalSphereKey.sortDesc_of_pairwise hsorted]
  rw [ordinaryKey_eq, ruleKey_eq, ofLex_toLex, hproj]

theorem ordinaryKey_stereo_wellShaped (W D : ℕ) (rule : StereochemicalRule) :
    ∀ node, WellShaped W D
      ((ofLex (ordinaryKey molecule graph evidence W D node)).2.getD (stereoIndex rule) []) := by
  intro node
  revert rule
  refine node_induction graph (motive := fun node => ∀ rule, WellShaped W D
    ((ofLex (ordinaryKey molecule graph evidence W D node)).2.getD (stereoIndex rule) [])) ?_ node
  intro node ih rule
  rw [ordinaryKey_stereo_getD]
  apply Certificate.CanonicalSphereKey.assemble_wellShaped
  intro key hkey
  obtain ⟨vector, hvector, rfl⟩ := List.mem_map.1 hkey
  obtain ⟨child, hchild, rfl⟩ :=
    List.mem_map.1 (Certificate.CanonicalSphereKey.sortDesc_mem hvector)
  exact ih child ((graph.mem_childList).1 hchild) rule

end OrdinaryKeys

/-! ## The ordinary canonical family -/

section Family

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  {graph : RootedDigraph Atom} (evidence : StereochemicalEvidence graph)

local instance ordinaryNodeFintype2 : Fintype graph.Node := graph.nodeFintype

/-- **The ordinary canonical addressings**: dense slots, siblings in descending ordinary-key order. -/
def OrdinaryCanonicalAddressing (addressing : graph.Addressing) : Prop :=
  Dense addressing ∧
    KeySorted (ordinaryKey molecule graph evidence graph.width graph.height) addressing

/-- Every ordinary canonical addressing is canonical for the three-rule family. -/
theorem ordinaryCanonical_canonical {addressing : graph.Addressing}
    (h : OrdinaryCanonicalAddressing molecule evidence addressing) :
    CanonicalAddressing molecule addressing := by
  refine ⟨h.1, fun parent first second firstSlot secondSlot hfirst hsecond hlt => ?_⟩
  have := fst_le_of_le (h.2 parent first second firstSlot secondSlot hfirst hsecond hlt)
  rwa [ordinaryKey_fst, ordinaryKey_fst] at this

/-- The value of one stereochemical rule at an address, `⊥` if unoccupied. -/
def stereoAddressValue (addressing : graph.Addressing) (rule : StereochemicalRule)
    (position : List ℕ) : WithBot StereoLabel :=
  if h : ∃ node, addressing.address node = position then
    (stereoLabel graph evidence rule (Classical.choose h) : WithBot StereoLabel)
  else ⊥

theorem stereoAddressValue_of_address (addressing : graph.Addressing) (rule : StereochemicalRule)
    (node : graph.Node) :
    stereoAddressValue evidence addressing rule (addressing.address node) =
      (stereoLabel graph evidence rule node : WithBot StereoLabel) := by
  have h : ∃ found, addressing.address found = addressing.address node := ⟨node, rfl⟩
  unfold stereoAddressValue
  rw [dif_pos h]
  congr 2
  exact addressing.address_injective (Classical.choose_spec h)

theorem stereoAddressValue_of_unoccupied (addressing : graph.Addressing)
    (rule : StereochemicalRule) {position : List ℕ}
    (h : ∀ node, addressing.address node ≠ position) :
    stereoAddressValue evidence addressing rule position = ⊥ := by
  unfold stereoAddressValue
  rw [dif_neg (by simpa using h)]

/-- **Stereochemical observation theorem.**  Under a dense addressing sorted by ordinary keys, the
stereochemical value at `address node ++ path` is the canonical key observation. -/
theorem stereoAddressValue_eq_keyObservation (W D : ℕ) {addressing : graph.Addressing}
    (hdense : Dense addressing)
    (hsorted : KeySorted (ordinaryKey molecule graph evidence W D) addressing)
    (rule : StereochemicalRule) :
    ∀ (path : List ℕ) (node : graph.Node), (∀ slot ∈ path, slot < W) → path.length ≤ D →
      keyObservation ((ofLex (ordinaryKey molecule graph evidence W D node)).2.getD
          (stereoIndex rule) []) path.length (slotOf W path) =
        stereoAddressValue evidence addressing rule (addressing.address node ++ path)
  | [], node, _, _ => by
      rw [List.append_nil, stereoAddressValue_of_address, ordinaryKey_stereo_getD]
      simp [keyObservation, stereoComponent, assemble, slotOf]
  | slot :: path, node, hdigits, hlength => by
      have hs : slot < W := hdigits slot (by simp)
      have hpath : ∀ i ∈ path, i < W := fun i hi => hdigits i (by simp [hi])
      have hpl : path.length < D := by simp at hlength; omega
      have hbound := Certificate.CanonicalSphereKey.slotOf_lt hpath
      obtain ⟨count, hcount⟩ := hdense node
      have hranked := sortDesc_childKeys_eq_slotOrder
        (ordinaryKey molecule graph evidence W D) hcount hsorted
      have hkeys : ∀ key ∈
          ((slotList addressing node count).map (ordinaryKey molecule graph evidence W D)).map
            (fun key => (ofLex key).2.getD (stereoIndex rule) []), WellShaped W D key := by
        intro key hkey
        obtain ⟨vector, hvector, rfl⟩ := List.mem_map.1 hkey
        obtain ⟨child, _, rfl⟩ := List.mem_map.1 hvector
        exact ordinaryKey_stereo_wellShaped molecule graph evidence W D rule child
      rw [ordinaryKey_stereo_getD, rankedOrdinaryKeys, hranked]
      simp only [keyObservation, stereoComponent, assemble, List.length_cons, slotOf,
        List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map,
        List.getElem?_range hpl, Option.map_some, Option.getD_some,
        Certificate.CanonicalSphereKey.getD_flatMap_range _ _ W
          (fun i _ => Certificate.CanonicalSphereKey.slotLevel_length hkeys hpl i) hs hbound]
      by_cases hocc : slot < count
      · obtain ⟨child, hchild, haddr⟩ := slotList_getD_of_lt hcount hocc
        have ih := stereoAddressValue_eq_keyObservation W D hdense hsorted rule path child hpath
          (by omega)
        have hpos : addressing.address node ++ slot :: path =
            addressing.address child ++ path := by
          rw [haddr]; simp
        rw [hpos, ← ih]
        have hk : path.length < ((ofLex (ordinaryKey molecule graph evidence W D child)).2.getD
            (stereoIndex rule) []).length := by
          rw [(ordinaryKey_stereo_wellShaped molecule graph evidence W D rule child).1]
          omega
        have hk' : path.length <
            ((ofLex (ordinaryKey molecule graph evidence W D child)).2[stereoIndex rule]?.getD
              []).length := by
          simpa [List.getD_eq_getElem?_getD] using hk
        simp [keyObservation, List.getD_eq_getElem?_getD, List.getElem?_map, hchild,
          List.getElem?_eq_getElem hk']
      · have hnone : ((slotList addressing node count).map
            (ordinaryKey molecule graph evidence W D))[slot]? = none := by
          simp [slotList]
          omega
        have hunocc : ∀ found,
            addressing.address found ≠ addressing.address node ++ slot :: path := by
          intro found hfound
          obtain ⟨ancestor, hancestor⟩ := addressing.prefix_occupied found
            (addressing.address node ++ [slot]) path (by rw [hfound]; simp)
          exact hocc ((hcount slot).1 ⟨ancestor, hancestor⟩)
        rw [stereoAddressValue_of_unoccupied evidence addressing rule hunocc]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hnone, Option.map_none,
          Option.getD_none, List.getElem?_nil, pad, List.getElem?_replicate]
        split <;> rfl

/-- Two ordinary canonical addressings of one hierarchy read the same stereochemical values. -/
theorem stereoAddressValue_ordinaryCanonical_eq {first second : graph.Addressing}
    (hfirst : OrdinaryCanonicalAddressing molecule evidence first)
    (hsecond : OrdinaryCanonicalAddressing molecule evidence second)
    (rule : StereochemicalRule) (position : List ℕ) :
    stereoAddressValue evidence first rule position =
      stereoAddressValue evidence second rule position := by
  by_cases hin : (∀ slot ∈ position, slot < graph.width) ∧ position.length ≤ graph.height
  · have h₁ := stereoAddressValue_eq_keyObservation molecule evidence graph.width graph.height
      hfirst.1 hfirst.2 rule position graph.root hin.1 hin.2
    have h₂ := stereoAddressValue_eq_keyObservation molecule evidence graph.width graph.height
      hsecond.1 hsecond.2 rule position graph.root hin.1 hin.2
    rw [first.root_address, List.nil_append] at h₁
    rw [second.root_address, List.nil_append] at h₂
    rw [← h₁, ← h₂]
  · have hout : ∀ addressing : graph.Addressing, Dense addressing →
        ∀ node, addressing.address node ≠ position := by
      intro addressing hdense node hnode
      exact hin ⟨hnode ▸ address_slots_lt_width hdense node,
        hnode ▸ address_length_le_height addressing node⟩
    rw [stereoAddressValue_of_unoccupied evidence first rule (hout first hfirst.1),
      stereoAddressValue_of_unoccupied evidence second rule (hout second hsecond.1)]

end Family

/-! ## Existence of sorted dense addressings for any key -/

section GenericExistence

variable {Atom : Type u} {graph : RootedDigraph Atom} (base : graph.Addressing)
  {K : Type*} [LinearOrder K] (key : graph.Node → K)

local instance ordinaryNodeFintype3 : Fintype graph.Node := graph.nodeFintype

/-- Children ranked in descending key order. -/
def rankedChildrenBy (parent : graph.Node) : List graph.Node :=
  (graph.childList parent).insertionSort (KeyDesc key)

theorem mem_rankedChildrenBy {parent child : graph.Node} :
    child ∈ rankedChildrenBy key parent ↔ graph.child parent child := by
  rw [rankedChildrenBy, List.mem_insertionSort, graph.mem_childList]

theorem rankedChildrenBy_nodup (parent : graph.Node) : (rankedChildrenBy key parent).Nodup :=
  (List.perm_insertionSort _ _).nodup_iff.2 (graph.childList_nodup parent)

/-- Address by rank in key order along the parents of `base`. -/
def keyAddress (node : graph.Node) : List ℕ :=
  if _hroot : node = graph.root then []
  else keyAddress (parentOf base node) ++
    [(rankedChildrenBy key (parentOf base node)).idxOf node]
termination_by graph.depth node
decreasing_by
  have := graph.child_depth (parentOf_child base _hroot)
  omega

theorem keyAddress_root : keyAddress base key graph.root = [] := by
  rw [keyAddress, dif_pos rfl]

theorem keyAddress_child {parent node : graph.Node} (h : graph.child parent node) :
    keyAddress base key node =
      keyAddress base key parent ++ [(rankedChildrenBy key parent).idxOf node] := by
  rw [keyAddress, dif_neg (ne_root_of_child base h), parentOf_eq base h]

theorem keyAddress_eq_nil_iff (node : graph.Node) :
    keyAddress base key node = [] ↔ node = graph.root := by
  constructor
  · intro h
    by_contra hne
    rw [keyAddress_child base key (parentOf_child base hne)] at h
    simp at h
  · rintro rfl
    exact keyAddress_root base key

theorem keyAddress_injective : Function.Injective (keyAddress base key) := by
  intro first
  have hreachable := graph.reachable first
  induction hreachable with
  | refl =>
      intro second h
      rw [keyAddress_root] at h
      exact ((keyAddress_eq_nil_iff base key second).1 h.symm).symm
  | @tail parent node _ hedge ih =>
      intro second h
      have hsecond : second ≠ graph.root := by
        rintro rfl
        rw [keyAddress_root, keyAddress_child base key hedge] at h
        simp at h
      have hsecondEdge := parentOf_child base hsecond
      rw [keyAddress_child base key hedge, keyAddress_child base key hsecondEdge] at h
      obtain ⟨hprefix, hlast⟩ := List.append_inj' h rfl
      have hparent : parent = parentOf base second := ih hprefix
      rw [← hparent] at hlast
      have hidx : (rankedChildrenBy key parent).idxOf node =
          (rankedChildrenBy key parent).idxOf second := by
        simpa using hlast
      exact (List.idxOf_inj ((mem_rankedChildrenBy key).2 hedge)).1 hidx

/-- The addressing by rank in key order. -/
def keyAddressing : graph.Addressing where
  address := keyAddress base key
  address_injective := keyAddress_injective base key
  root_address := keyAddress_root base key
  child_iff := by
    intro parent node
    constructor
    · intro h
      exact ⟨_, keyAddress_child base key h⟩
    · rintro ⟨slot, hslot⟩
      have hne : node ≠ graph.root := by
        rintro rfl
        rw [keyAddress_root] at hslot
        simp at hslot
      have hedge := parentOf_child base hne
      rw [keyAddress_child base key hedge] at hslot
      obtain ⟨hprefix, _⟩ := List.append_inj' hslot rfl
      rw [← keyAddress_injective base key hprefix]
      exact hedge

theorem keyAddressing_slot {parent child : graph.Node} {slot : ℕ}
    (h : (keyAddressing base key).address child =
      (keyAddressing base key).address parent ++ [slot]) :
    graph.child parent child ∧ slot = (rankedChildrenBy key parent).idxOf child := by
  have hedge := ((keyAddressing base key).child_iff parent child).2 ⟨slot, h⟩
  refine ⟨hedge, ?_⟩
  change keyAddress base key child = keyAddress base key parent ++ [slot] at h
  rw [keyAddress_child base key hedge] at h
  simpa using (List.append_inj' h rfl).2.symm

/-- **Existence** of a dense addressing sorted by any key. -/
theorem keyAddressing_dense_sorted :
    Dense (keyAddressing base key) ∧ KeySorted key (keyAddressing base key) := by
  constructor
  · intro parent
    refine ⟨(rankedChildrenBy key parent).length, fun slot => ?_⟩
    constructor
    · rintro ⟨child, hchild⟩
      obtain ⟨hedge, rfl⟩ := keyAddressing_slot base key hchild
      exact List.idxOf_lt_length_of_mem ((mem_rankedChildrenBy key).2 hedge)
    · intro hslot
      refine ⟨(rankedChildrenBy key parent)[slot], ?_⟩
      have hedge := (mem_rankedChildrenBy key).1 (List.getElem_mem hslot)
      change keyAddress base key _ = keyAddress base key parent ++ [slot]
      rw [keyAddress_child base key hedge,
        (rankedChildrenBy_nodup key parent).idxOf_getElem slot hslot]
  · intro parent first second firstSlot secondSlot hfirst hsecond hlt
    obtain ⟨hfirstEdge, rfl⟩ := keyAddressing_slot base key hfirst
    obtain ⟨hsecondEdge, rfl⟩ := keyAddressing_slot base key hsecond
    have hpair : (rankedChildrenBy key parent).Pairwise (KeyDesc key) :=
      List.pairwise_insertionSort _ _
    have hfl := List.idxOf_lt_length_of_mem ((mem_rankedChildrenBy key).2 hfirstEdge)
    have hsl := List.idxOf_lt_length_of_mem ((mem_rankedChildrenBy key).2 hsecondEdge)
    have h := List.pairwise_iff_getElem.1 hpair _ _ hfl hsl hlt
    rw [List.getElem_idxOf hfl, List.getElem_idxOf hsl] at h
    exact h

end GenericExistence

theorem exists_ordinaryCanonicalAddressing {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) {graph : RootedDigraph Atom}
    (evidence : StereochemicalEvidence graph) (base : graph.Addressing) :
    ∃ addressing : graph.Addressing, OrdinaryCanonicalAddressing molecule evidence addressing :=
  ⟨keyAddressing base _, keyAddressing_dense_sorted base _⟩

/-! ## Stereochemical outcomes read only address values -/

section Outcomes

variable {Atom : Type u}

/-- The observation at an address, if occupied. -/
def addressEvidence {graph : RootedDigraph Atom} (addressing : graph.Addressing)
    (evidence : StereochemicalEvidence graph) (position : List ℕ) :
    Option StereochemicalObservation :=
  if h : ∃ node, addressing.address node = position then
    some (evidence (Classical.choose h))
  else none

theorem observationAt_iff_eq_addressEvidence {graph : RootedDigraph Atom}
    (addressing : graph.Addressing) (evidence : StereochemicalEvidence graph)
    (position : List ℕ) (observation : Option StereochemicalObservation) :
    RootedDigraph.Addressing.ObservationAt graph addressing evidence position observation ↔
      observation = addressEvidence addressing evidence position := by
  unfold addressEvidence
  cases observation with
  | some observation =>
      constructor
      · rintro ⟨node, hnode, rfl⟩
        have h : ∃ found, addressing.address found = position := ⟨node, hnode⟩
        rw [dif_pos h]
        congr 2
        exact addressing.address_injective (hnode.trans (Classical.choose_spec h).symm)
      · intro h
        split at h
        · rename_i hocc
          exact ⟨Classical.choose hocc, Classical.choose_spec hocc, (Option.some.inj h).symm⟩
        · exact absurd h (by simp)
  | none =>
      constructor
      · intro hempty
        rw [dif_neg (by simpa using hempty)]
      · intro h node hnode
        rw [dif_pos ⟨node, hnode⟩] at h
        exact absurd h (by simp)

theorem stereochemicalOutcomeAt_iff (rule : StereochemicalRule)
    {left right : RootedDigraph Atom} (leftAddressing : left.Addressing)
    (leftEvidence : StereochemicalEvidence left) (rightAddressing : right.Addressing)
    (rightEvidence : StereochemicalEvidence right) (position : List ℕ) (outcome : Ordering) :
    StereochemicalOutcomeAt rule left leftAddressing leftEvidence right rightAddressing
        rightEvidence position outcome ↔
      OrderedKeyOutcome (stereoValue rule (addressEvidence leftAddressing leftEvidence position))
        (stereoValue rule (addressEvidence rightAddressing rightEvidence position)) outcome := by
  unfold StereochemicalOutcomeAt
  simp only [observationAt_iff_eq_addressEvidence, stereochemicalNodeOutcome_iff]
  constructor
  · rintro ⟨_, _, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, _, rfl, rfl, h⟩

/-- Merge the absent-node and absent-field readings. -/
def flattenBot {α : Type*} : WithBot (WithBot α) → WithBot α
  | none => none
  | some value => value

theorem stereoValue_addressEvidence {graph : RootedDigraph Atom}
    (addressing : graph.Addressing) (evidence : StereochemicalEvidence graph)
    (rule : StereochemicalRule) (position : List ℕ) :
    stereoValue rule (addressEvidence addressing evidence position) =
      flattenBot (stereoAddressValue evidence addressing rule position) := by
  unfold addressEvidence stereoAddressValue
  split
  · rfl
  · cases rule <;> rfl

variable [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)

/-- **Stereochemical addressing independence.**  Rules 3--5 hierarchy outcomes coincide for every
choice of ordinary canonical addressings. -/
theorem stereochemicalHierarchyOutcome_ordinaryCanonical_iff (rule : StereochemicalRule)
    {left right : RootedDigraph Atom} {leftEvidence : StereochemicalEvidence left}
    {rightEvidence : StereochemicalEvidence right}
    {leftFirst leftSecond : left.Addressing} {rightFirst rightSecond : right.Addressing}
    (hleftFirst : OrdinaryCanonicalAddressing molecule leftEvidence leftFirst)
    (hleftSecond : OrdinaryCanonicalAddressing molecule leftEvidence leftSecond)
    (hrightFirst : OrdinaryCanonicalAddressing molecule rightEvidence rightFirst)
    (hrightSecond : OrdinaryCanonicalAddressing molecule rightEvidence rightSecond)
    (outcome : Ordering) :
    StereochemicalHierarchyOutcome rule left leftFirst leftEvidence right rightFirst
        rightEvidence outcome ↔
      StereochemicalHierarchyOutcome rule left leftSecond leftEvidence right rightSecond
        rightEvidence outcome := by
  apply FirstDifferenceOutcome.congr
  intro position outcome
  rw [stereochemicalOutcomeAt_iff, stereochemicalOutcomeAt_iff, stereoValue_addressEvidence,
    stereoValue_addressEvidence, stereoValue_addressEvidence, stereoValue_addressEvidence,
    stereoAddressValue_ordinaryCanonical_eq molecule leftEvidence hleftFirst hleftSecond rule
      position,
    stereoAddressValue_ordinaryCanonical_eq molecule rightEvidence hrightFirst hrightSecond rule
      position]

end Outcomes

/-! ## Representation invariance under preserved evidence -/

section Transport

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  {left right : RootedDigraph Atom} (iso : RootedDigraph.Iso left right)
  {leftEvidence : StereochemicalEvidence left} {rightEvidence : StereochemicalEvidence right}
  (hpreserved : RootedDigraph.Addressing.EvidencePreserved iso leftEvidence rightEvidence)

local instance ordinaryNodeFintype4 (graph : RootedDigraph Atom) : Fintype graph.Node := graph.nodeFintype

include hpreserved in
theorem stereoLabel_iso (rule : StereochemicalRule) (node : left.Node) :
    stereoLabel right rightEvidence rule (iso.toEquiv node) =
      stereoLabel left leftEvidence rule node := by
  unfold stereoLabel
  rw [← hpreserved node]

include hpreserved in
/-- Ordinary keys are invariant under isomorphisms that preserve the supplied evidence. -/
theorem ordinaryKey_iso (W D : ℕ) :
    ∀ node : left.Node,
      ordinaryKey molecule right rightEvidence W D (iso.toEquiv node) =
        ordinaryKey molecule left leftEvidence W D node := by
  refine node_induction left ?_
  intro node ih
  have hranked : rankedOrdinaryKeys molecule right rightEvidence W D (iso.toEquiv node) =
      rankedOrdinaryKeys molecule left leftEvidence W D node := by
    unfold rankedOrdinaryKeys
    rw [Certificate.CanonicalSphereKey.sortDesc_eq_of_perm
      ((childList_iso_perm iso node).map (ordinaryKey molecule right rightEvidence W D)),
      List.map_map]
    congr 1
    exact List.map_congr_left fun child hchild => ih child ((left.mem_childList).1 hchild)
  rw [ordinaryKey_eq, ordinaryKey_eq, hranked]
  simp only [ruleComponent, stereoComponent, nodeObservation_iso molecule iso,
    stereoLabel_iso iso hpreserved]

include hpreserved in
theorem ordinaryCanonical_transport {addressing : left.Addressing}
    (h : OrdinaryCanonicalAddressing molecule leftEvidence addressing) :
    OrdinaryCanonicalAddressing molecule rightEvidence (addressing.transport iso) := by
  obtain ⟨hdense, hsorted⟩ := h
  constructor
  · intro parent
    obtain ⟨count, hcount⟩ := hdense (iso.toEquiv.symm parent)
    refine ⟨count, fun slot => ?_⟩
    rw [← hcount slot]
    simp only [RootedDigraph.Addressing.transport_address]
    constructor
    · rintro ⟨child, hchild⟩
      exact ⟨iso.toEquiv.symm child, hchild⟩
    · rintro ⟨child, hchild⟩
      exact ⟨iso.toEquiv child, by simpa using hchild⟩
  · intro parent first second firstSlot secondSlot hfirst hsecond hlt
    simp only [RootedDigraph.Addressing.transport_address] at hfirst hsecond
    have h := hsorted _ _ _ firstSlot secondSlot hfirst hsecond hlt
    rw [← width_eq_of_iso iso, ← height_eq_of_iso iso]
    rw [← ordinaryKey_iso molecule iso hpreserved, ← ordinaryKey_iso molecule iso hpreserved] at h
    simpa using h

include hpreserved in
theorem evidencePreserved_symm :
    RootedDigraph.Addressing.EvidencePreserved iso.symm rightEvidence leftEvidence := by
  intro node
  have := hpreserved (iso.toEquiv.symm node)
  simp only [Equiv.apply_symm_apply] at this
  exact this.symm

include hpreserved in
theorem ordinaryCanonical_transport_iff (addressing : left.Addressing) :
    OrdinaryCanonicalAddressing molecule leftEvidence addressing ↔
      OrdinaryCanonicalAddressing molecule rightEvidence (addressing.transport iso) := by
  constructor
  · exact ordinaryCanonical_transport molecule iso hpreserved
  · intro h
    have := ordinaryCanonical_transport molecule iso.symm
      (evidencePreserved_symm iso hpreserved) h
    rwa [RootedDigraph.Addressing.transport_symm_transport] at this

end Transport

/-! ## Installing the family for all eight ordinary rules -/

namespace StereochemicalProblemData

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

/-- Replace the shared admissible addressing family by the ordinary canonical family.  The
supplied evidence and its naturality law are retained unchanged. -/
def withOrdinaryCanonicalAddressing (data : StereochemicalProblemData Atom Unit) :
    StereochemicalProblemData Atom Unit :=
  { data with
    admissibleAddressing := fun descriptorMap unit graph addressing =>
      OrdinaryCanonicalAddressing data.molecule (data.evidence descriptorMap unit graph) addressing
    addressing_invariant := fun descriptorMap unit _ _ iso addressing =>
      ordinaryCanonical_transport_iff data.molecule iso
        (data.evidence_invariant descriptorMap unit iso) addressing
    hierarchy_compatible := by
      intro _ _ rule _ _ _ _ _ _ _ _ _ _ _
      cases rule <;> trivial }

/-- **Constitutional addressing independence** for the eight-rule family. -/
theorem withOrdinaryCanonicalAddressing_constitutionalIndependent
    (data : StereochemicalProblemData Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (rule : ConstitutionalRule) (left right : RootedDigraph Atom) :
    data.withOrdinaryCanonicalAddressing.toConstitutionalProblemData.AddressingIndependent
      descriptorMap unit rule left right := by
  intro firstLeft firstRight secondLeft secondRight firstOutcome secondOutcome
    hfirstLeft hfirstRight hsecondLeft hsecondRight hfirst hsecond
  have hmoved := (hierarchyOutcome_canonical_iff data.molecule
    (ordinaryCanonical_canonical _ _ hsecondLeft) (ordinaryCanonical_canonical _ _ hfirstLeft)
    (ordinaryCanonical_canonical _ _ hsecondRight) (ordinaryCanonical_canonical _ _ hfirstRight)
    rule secondOutcome).1 hsecond
  exact constitutionalHierarchyOutcome_functional data.molecule rule left firstLeft right
    firstRight hfirst hmoved

/-- **Stereochemical addressing independence** for the same family. -/
theorem withOrdinaryCanonicalAddressing_stereochemicalIndependent
    (data : StereochemicalProblemData Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (rule : StereochemicalRule) (left right : RootedDigraph Atom) :
    data.withOrdinaryCanonicalAddressing.AddressingIndependent descriptorMap unit rule left right := by
  intro firstLeft firstRight secondLeft secondRight firstOutcome secondOutcome
    hfirstLeft hfirstRight hsecondLeft hsecondRight hfirst hsecond
  have hmoved := (stereochemicalHierarchyOutcome_ordinaryCanonical_iff data.molecule rule
    hsecondLeft hfirstLeft hsecondRight hfirstRight secondOutcome).1 hsecond
  exact stereochemicalHierarchyOutcome_functional rule left firstLeft _ right firstRight _
    hfirst hmoved

/-- The family is inhabited on every addressed hierarchy. -/
theorem withOrdinaryCanonicalAddressing_exists (data : StereochemicalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) {graph : RootedDigraph Atom}
    (base : graph.Addressing) :
    ∃ addressing, data.withOrdinaryCanonicalAddressing.admissibleAddressing descriptorMap unit
      graph addressing :=
  exists_ordinaryCanonicalAddressing data.molecule _ base

end StereochemicalProblemData

end
end DeclarativeCIP
end OneCenter
end TetraStereo
