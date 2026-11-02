import TetraStereo.OneCenter.DeclarativeCIPRule1aExact
import TetraStereo.OneCenter.OfficialRuleMajorKey

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

/-!
# Exact-rational official rule-major keys

The historical `OfficialRuleMajorKey` stores Rule-1a observations as natural numbers.  That is
adequate for ordinary atoms, but cannot represent the exact rational mean required for a
multiple-bond duplicate in a localized mancude system.  This module keeps the same finite,
parent-addressed provenance tree while reading Rule 1a directly from the independent
maximum-matching semantics in `DeclarativeCIPRule1aExact`.

No cached numeric projection is authoritative here: the comparator projects every observation
afresh from the provenance-bearing source nodes.
-/

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact Rule-1a observation carried by an official finite-provenance node. -/
def exactOfficialRule1aObservation (m : MoleculeGraph V) (node : OfficialCIPNode V) :
    DeclarativeCIP.ExactAtomicNumber :=
  match node.current? with
  | none => .zero
  | some atom =>
      match node.provenance with
      | .multipleBondDuplicate _ =>
          match node.parent? with
          | none => .ofNat (m.atomZ atom)
          | some attached => m.exactRule1aMultipleBond attached atom
      | _ => .ofNat (m.atomZ atom)

@[simp] theorem exactOfficialRule1aObservation_rootFromEdge
    (m : MoleculeGraph V) (parent current : V) :
    m.exactOfficialRule1aObservation (OfficialCIPNode.rootFromEdge parent current) =
      .ofNat (m.atomZ current) :=
  rfl

/-- Exact official node observations depend only on atomic numbers and the independent localized
mancude edge relation. -/
theorem exactOfficialRule1aObservation_eq_of_atomZ_eq_of_localizedMancudeEdge_iff
    (leftGraph rightGraph : MoleculeGraph V)
    (atomZ : ∀ atom, leftGraph.atomZ atom = rightGraph.atomZ atom)
    (localized : ∀ left right,
      leftGraph.LocalizedMancudeEdge left right ↔
        rightGraph.LocalizedMancudeEdge left right)
    (node : OfficialCIPNode V) :
    leftGraph.exactOfficialRule1aObservation node =
      rightGraph.exactOfficialRule1aObservation node := by
  unfold exactOfficialRule1aObservation
  cases currentObserved : node.current? with
  | none => rfl
  | some current =>
      cases provenanceObserved : node.provenance with
      | realAtom => simp [atomZ]
      | ringDuplicate distance => simp [atomZ]
      | placeholder kind distance => simp [atomZ]
      | multipleBondDuplicate distance =>
          cases parentObserved : node.parent? with
          | none => simp [atomZ]
          | some attached =>
              simp only
              unfold exactRule1aMultipleBond
              by_cases leftLocalized : leftGraph.LocalizedMancudeEdge attached current
              · have rightLocalized := (localized attached current).mp leftLocalized
                simp [leftLocalized, rightLocalized,
                  leftGraph.exactMancudeAverage_eq_of_atomZ_eq_of_localizedMancudeEdge_iff
                    rightGraph atomZ localized attached]
              · have rightNotLocalized :
                    ¬ rightGraph.LocalizedMancudeEdge attached current := by
                  exact fun rightLocalized =>
                    leftLocalized ((localized attached current).mpr rightLocalized)
                simp [leftLocalized, rightNotLocalized, atomZ]

end MoleculeGraph

/-- A finite official provenance tree compiled for exact Rule 1a. -/
structure ExactOfficialRuleMajorKey (V : Type*) where
  sourceNodes : OfficialRuleMajorKey.AddressedSourceLayers V
  complete : Bool

namespace ExactOfficialRuleMajorKey

/-- Exact rational comparison for revised Rule 1a. -/
def compareExactAtomicNumber :
    DeclarativeCIP.ExactAtomicNumber → DeclarativeCIP.ExactAtomicNumber → Ordering :=
  Ordering.byKey DeclarativeCIP.ExactAtomicNumber.value compare

theorem compareExactAtomicNumber_ofNat_lt {left right : Nat} (lower : left < right) :
    compareExactAtomicNumber (.ofNat left) (.ofNat right) = Ordering.lt := by
  unfold compareExactAtomicNumber Ordering.byKey
  simp only [DeclarativeCIP.ExactAtomicNumber.value,
    DeclarativeCIP.ExactAtomicNumber.ofNat]
  norm_num only [Nat.cast_one, div_one]
  have rationalLower : (left : Rat) < (right : Rat) := by exact_mod_cast lower
  change (if (left : Rat) ≤ (right : Rat) then
      if (right : Rat) ≤ (left : Rat) then Ordering.eq else Ordering.lt
    else Ordering.gt) = Ordering.lt
  simp [rationalLower.le, not_le_of_gt rationalLower]

theorem compareExactAtomicNumber_ofNat_gt {left right : Nat} (higher : right < left) :
    compareExactAtomicNumber (.ofNat left) (.ofNat right) = Ordering.gt := by
  unfold compareExactAtomicNumber Ordering.byKey
  simp only [DeclarativeCIP.ExactAtomicNumber.value,
    DeclarativeCIP.ExactAtomicNumber.ofNat]
  norm_num only [Nat.cast_one, div_one]
  have rationalHigher : (right : Rat) < (left : Rat) := by exact_mod_cast higher
  change (if (left : Rat) ≤ (right : Rat) then
      if (right : Rat) ≤ (left : Rat) then Ordering.eq else Ordering.lt
    else Ordering.gt) = Ordering.gt
  simp [not_le_of_gt rationalHigher]

theorem compareExactAtomicNumber_transCmp :
    Std.TransCmp compareExactAtomicNumber := by
  unfold compareExactAtomicNumber
  infer_instance

/-- Exact Rule-1a projection of a finite addressed provenance tree. -/
def exactRule1aLayers {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (sources : OfficialRuleMajorKey.AddressedSourceLayers V) :=
  OfficialRuleMajorKey.mapSourceLayers m.exactOfficialRule1aObservation sources

theorem exactRule1aLayers_head_of_sourceNodes_head
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (sources : OfficialRuleMajorKey.AddressedSourceLayers V)
    (node : OfficialCIPNode V)
    (head : sources.head? = some [([], node)]) :
    (exactRule1aLayers m sources).head? =
      some [([], m.exactOfficialRule1aObservation node)] := by
  cases sources with
  | nil => simp at head
  | cons first rest =>
      simp at head
      subst first
      rfl

theorem compareSparseExactRule1a_lt_of_heads_lt
    {left right : List (List (OfficialSparseEntry DeclarativeCIP.ExactAtomicNumber))}
    {leftZ rightZ : Nat}
    (leftHead : left.head? = some [([], .ofNat leftZ)])
    (rightHead : right.head? = some [([], .ofNat rightZ)])
    (lower : leftZ < rightZ) :
    OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber left right =
      Ordering.lt := by
  cases leftRule : left with
  | nil => simp [leftRule] at leftHead
  | cons leftFirst leftRest =>
      cases rightRule : right with
      | nil => simp [rightRule] at rightHead
      | cons rightFirst rightRest =>
          simp [leftRule, rightRule] at leftHead rightHead
          subst leftFirst
          subst rightFirst
          have compared := compareExactAtomicNumber_ofNat_lt lower
          simp [OfficialRuleMajorKey.compareSparseLayers,
            OfficialRuleMajorKey.compareSparseLayer,
            OfficialRuleMajorKey.compareSparseEntry,
            List.compareLex, compareLex, Ordering.byKey, flip, compared]

theorem compareSparseExactRule1a_gt_of_heads_gt
    {left right : List (List (OfficialSparseEntry DeclarativeCIP.ExactAtomicNumber))}
    {leftZ rightZ : Nat}
    (leftHead : left.head? = some [([], .ofNat leftZ)])
    (rightHead : right.head? = some [([], .ofNat rightZ)])
    (higher : rightZ < leftZ) :
    OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber left right =
      Ordering.gt := by
  cases leftRule : left with
  | nil => simp [leftRule] at leftHead
  | cons leftFirst leftRest =>
      cases rightRule : right with
      | nil => simp [rightRule] at rightHead
      | cons rightFirst rightRest =>
          simp [leftRule, rightRule] at leftHead rightHead
          subst leftFirst
          subst rightFirst
          have compared := compareExactAtomicNumber_ofNat_gt higher
          simp [OfficialRuleMajorKey.compareSparseLayers,
            OfficialRuleMajorKey.compareSparseLayer,
            OfficialRuleMajorKey.compareSparseEntry,
            List.compareLex, compareLex, Ordering.byKey, flip, compared]

/-- Rule-1b projection of the same provenance tree. -/
def rule1bLayers {V : Type*}
    (sources : OfficialRuleMajorKey.AddressedSourceLayers V) :=
  OfficialRuleMajorKey.mapSourceLayers OfficialCIPNode.rule1bRootDistance sources

/-- Rule-2 projection of the same provenance tree. -/
def rule2Layers {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (sources : OfficialRuleMajorKey.AddressedSourceLayers V) :=
  OfficialRuleMajorKey.mapSourceLayers
    (fun node => (ofLex (m.officialNodeAtomLabel node)).2) sources

/-- Exact constitutional comparison read freshly from two provenance trees. -/
def compareAddressedSources {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (left right : OfficialRuleMajorKey.AddressedSourceLayers V) :
    Ordering :=
  compareLex
    (Ordering.byKey (exactRule1aLayers m)
      (OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber))
    (compareLex
      (Ordering.byKey rule1bLayers
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b))
      (Ordering.byKey (rule2Layers m)
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat)))
    left right

/-- Total exact constitutional comparison of compiled keys. -/
def compare {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) : ExactOfficialRuleMajorKey V → ExactOfficialRuleMajorKey V → Ordering :=
  Ordering.byKey ExactOfficialRuleMajorKey.sourceNodes (compareAddressedSources m)

/-- Rule-tagged constitutional trace read directly from two addressed provenance trees. -/
def compareAddressedSourceTrace {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (left right : OfficialRuleMajorKey.AddressedSourceLayers V) :
    List CIPRuleDecision :=
  [ { rule := CIPRuleFamily.atomicNumber
      outcome := OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber
        (exactRule1aLayers m left) (exactRule1aLayers m right) }
  , { rule := CIPRuleFamily.duplicateAtom
      outcome := OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
        (rule1bLayers left) (rule1bLayers right) }
  , { rule := CIPRuleFamily.isotopeMass
      outcome := OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (rule2Layers m left) (rule2Layers m right) }
  ]

/-- Rule-tagged trace in exact Rule 1a, Rule 1b, Rule 2 order. -/
def compareTrace {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (left right : ExactOfficialRuleMajorKey V) :
    List CIPRuleDecision :=
  compareAddressedSourceTrace m left.sourceNodes right.sourceNodes

@[simp] theorem compareTrace_rule_order {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (left right : ExactOfficialRuleMajorKey V) :
    (compareTrace m left right).map CIPRuleDecision.rule =
      [CIPRuleFamily.atomicNumber, CIPRuleFamily.duplicateAtom,
        CIPRuleFamily.isotopeMass] :=
  rfl

@[simp] theorem compareTrace_eq_compareAddressedSourceTrace
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (left right : ExactOfficialRuleMajorKey V) :
    compareTrace m left right =
      compareAddressedSourceTrace m left.sourceNodes right.sourceNodes :=
  rfl

theorem compareTrace_outcome {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (left right : ExactOfficialRuleMajorKey V) :
    cipTraceOutcome (compareTrace m left right) = compare m left right := by
  unfold compareTrace compareAddressedSourceTrace ExactOfficialRuleMajorKey.compare
    compareAddressedSources
  unfold Ordering.byKey
  simp only [cipTraceOutcome]
  generalize atomicComparison :
      OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber
        (exactRule1aLayers m left.sourceNodes)
        (exactRule1aLayers m right.sourceNodes) = atomicOutcome
  generalize duplicateComparison :
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
        (rule1bLayers left.sourceNodes) (rule1bLayers right.sourceNodes) = duplicateOutcome
  generalize massComparison :
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (rule2Layers m left.sourceNodes) (rule2Layers m right.sourceNodes) = massOutcome
  cases atomicOutcome <;> cases duplicateOutcome <;> cases massOutcome <;>
    simp_all [compareLex]

theorem compare_transCmp {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) : Std.TransCmp (compare m) := by
  letI : Std.TransCmp compareExactAtomicNumber := compareExactAtomicNumber_transCmp
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  letI : Std.TransCmp OfficialRuleMajorKey.compareRule1b := by
    unfold OfficialRuleMajorKey.compareRule1b
    infer_instance
  unfold ExactOfficialRuleMajorKey.compare compareAddressedSources exactRule1aLayers
    rule1bLayers rule2Layers OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareSparseEntry
  infer_instance

/-- Incomplete prefixes are safe exactly when exact Rule 1a has already decided. -/
def compare? {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (left right : ExactOfficialRuleMajorKey V) : Option Ordering :=
  match OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber
      (exactRule1aLayers m left.sourceNodes) (exactRule1aLayers m right.sourceNodes) with
  | .lt => some .lt
  | .gt => some .gt
  | .eq => if left.complete && right.complete then some (compare m left right) else none

theorem compare_eq_of_compare?_eq_some {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (left right : ExactOfficialRuleMajorKey V) (outcome : Ordering)
    (computed : compare? m left right = some outcome) :
    compare m left right = outcome := by
  unfold compare? at computed
  split at computed <;> cases outcome <;>
    simp_all [ExactOfficialRuleMajorKey.compare, compareAddressedSources,
      compareLex, Ordering.byKey]

theorem compare?_isSome_of_complete {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (left right : ExactOfficialRuleMajorKey V)
    (leftComplete : left.complete = true) (rightComplete : right.complete = true) :
    (compare? m left right).isSome = true := by
  unfold compare?
  split <;> simp [leftComplete, rightComplete]

def insert? {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (key : ExactOfficialRuleMajorKey V) :
    List (ExactOfficialRuleMajorKey V) → Option (List (ExactOfficialRuleMajorKey V))
  | [] => some [key]
  | head :: tail =>
      match compare? m key head with
      | none => none
      | some .gt | some .eq => some (key :: head :: tail)
      | some .lt => (insert? m key tail).map fun sorted => head :: sorted

def sort? {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) :
    List (ExactOfficialRuleMajorKey V) → Option (List (ExactOfficialRuleMajorKey V))
  | [] => some []
  | key :: keys => do
      let sorted ← sort? m keys
      insert? m key sorted

theorem insert?_perm {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (key : ExactOfficialRuleMajorKey V) :
    ∀ keys result, insert? m key keys = some result → result.Perm (key :: keys)
  | [], result, computed => by
      simp [insert?] at computed
      subst result
      exact List.Perm.refl _
  | head :: tail, result, computed => by
      unfold insert? at computed
      cases comparison : compare? m key head with
      | none => simp [comparison] at computed
      | some decision =>
          cases decision with
          | gt => simp [comparison] at computed; subst result; exact List.Perm.refl _
          | eq => simp [comparison] at computed; subst result; exact List.Perm.refl _
          | lt =>
              simp only [comparison, Option.map_eq_some_iff] at computed
              rcases computed with ⟨inserted, insertedComputed, rfl⟩
              exact (List.Perm.cons head
                (insert?_perm m key tail inserted insertedComputed)).trans
                  (List.Perm.swap key head tail)

theorem sort?_perm {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) :
    ∀ keys result, sort? m keys = some result → result.Perm keys
  | [], result, computed => by
      simp [sort?] at computed
      subst result
      exact List.Perm.refl _
  | key :: keys, result, computed => by
      unfold sort? at computed
      cases sortedComputed : sort? m keys with
      | none => simp [sortedComputed] at computed
      | some sorted =>
          have tailPermutation := sort?_perm m keys sorted sortedComputed
          have insertedPermutation := insert?_perm m key sorted result (by
            simpa [sortedComputed] using computed)
          exact insertedPermutation.trans (List.Perm.cons key tailPermutation)

def Descending {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (keys : List (ExactOfficialRuleMajorKey V)) : Prop :=
  keys.Pairwise fun left right => compare m left right ≠ Ordering.lt

theorem insert?_descending {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (key : ExactOfficialRuleMajorKey V) :
    ∀ keys result, Descending m keys → insert? m key keys = some result → Descending m result
  | [], result, sorted, computed => by
      simp [insert?] at computed
      subst result
      simp [Descending]
  | head :: tail, result, sorted, computed => by
      letI : Std.TransCmp (compare m) := compare_transCmp m
      have headOverTail : ∀ observed ∈ tail, compare m head observed ≠ Ordering.lt :=
        (List.pairwise_cons.mp sorted).1
      have tailSorted : Descending m tail := (List.pairwise_cons.mp sorted).2
      unfold insert? at computed
      cases safe : compare? m key head with
      | none => simp [safe] at computed
      | some outcome =>
          have total := compare_eq_of_compare?_eq_some m key head outcome safe
          cases outcome with
          | gt =>
              simp [safe] at computed
              subst result
              rw [Descending, List.pairwise_cons]
              exact ⟨fun observed present => by
                rcases List.mem_cons.mp present with rfl | tailPresent
                · simp [total]
                · exact Std.TransCmp.ge_trans (by simp [total])
                    (headOverTail observed tailPresent), sorted⟩
          | eq =>
              simp [safe] at computed
              subst result
              rw [Descending, List.pairwise_cons]
              exact ⟨fun observed present => by
                rcases List.mem_cons.mp present with rfl | tailPresent
                · simp [total]
                · exact Std.TransCmp.ge_trans (by simp [total])
                    (headOverTail observed tailPresent), sorted⟩
          | lt =>
              simp only [safe, Option.map_eq_some_iff] at computed
              rcases computed with ⟨inserted, insertedComputed, rfl⟩
              have insertedSorted := insert?_descending m key tail inserted
                tailSorted insertedComputed
              rw [Descending, List.pairwise_cons]
              constructor
              · intro observed present
                have permutation := insert?_perm m key tail inserted insertedComputed
                have sourcePresent : observed ∈ key :: tail :=
                  (permutation.mem_iff).mp present
                rcases List.mem_cons.mp sourcePresent with same | tailPresent
                · subst observed
                  have reverse : compare m head key = Ordering.gt := by
                    rw [Std.OrientedCmp.gt_iff_lt]
                    exact total
                  simp [reverse]
                · exact headOverTail observed tailPresent
              · exact insertedSorted

theorem sort?_descending {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) :
    ∀ keys result, sort? m keys = some result → Descending m result
  | [], result, computed => by
      simp [sort?] at computed
      subst result
      simp [Descending]
  | key :: keys, result, computed => by
      unfold sort? at computed
      cases sortedComputed : sort? m keys with
      | none => simp [sortedComputed] at computed
      | some sorted =>
          exact insert?_descending m key sorted result
            (sort?_descending m keys sorted sortedComputed)
            (by simpa [sortedComputed] using computed)

theorem insert?_isSome_of_complete {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (key : ExactOfficialRuleMajorKey V)
    (keyComplete : key.complete = true) :
    ∀ keys, (∀ child, child ∈ keys → child.complete = true) →
      (insert? m key keys).isSome = true
  | [], _ => rfl
  | head :: tail, allComplete => by
      have headComplete := allComplete head (by simp)
      have tailComplete : ∀ child, child ∈ tail → child.complete = true := by
        intro child present
        exact allComplete child (List.mem_cons_of_mem head present)
      unfold insert?
      have comparable := compare?_isSome_of_complete m key head keyComplete headComplete
      cases comparison : compare? m key head with
      | none => simp [comparison] at comparable
      | some outcome =>
          cases outcome <;> simp [insert?_isSome_of_complete m key keyComplete tail tailComplete]

theorem sort?_isSome_of_complete {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) :
    ∀ keys, (∀ key, key ∈ keys → key.complete = true) → (sort? m keys).isSome = true
  | [], _ => rfl
  | key :: keys, allComplete => by
      have keyComplete := allComplete key (by simp)
      have tailComplete : ∀ child, child ∈ keys → child.complete = true := by
        intro child present
        exact allComplete child (List.mem_cons_of_mem key present)
      unfold sort?
      have sortedExists := sort?_isSome_of_complete m keys tailComplete
      cases sortedComputed : sort? m keys with
      | none => simp [sortedComputed] at sortedExists
      | some sorted =>
          have sortedPermutation := sort?_perm m keys sorted sortedComputed
          have sortedComplete : ∀ child, child ∈ sorted → child.complete = true := by
            intro child present
            exact tailComplete child ((sortedPermutation.mem_iff).mp present)
          simpa [sortedComputed] using
            insert?_isSome_of_complete m key keyComplete sorted sortedComplete

/-- Join a root node to exact-priority-sorted child provenance trees. -/
def assemble {V : Type*} (root : ExactOfficialRuleMajorKey V)
    (sortedChildren : List (ExactOfficialRuleMajorKey V)) : ExactOfficialRuleMajorKey V where
  sourceNodes := root.sourceNodes ++ OfficialRuleMajorKey.mergeAddressedChildren
    (sortedChildren.map ExactOfficialRuleMajorKey.sourceNodes)
  complete := sortedChildren.all ExactOfficialRuleMajorKey.complete

def DeclarativeAddressedExpansion {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    Nat → OfficialCIPNode V → OfficialRuleMajorKey.AddressedSourceLayers V → Prop
  | 0, node, sources => sources = [[([], node)]]
  | fuel + 1, node, sources =>
      if children node = [] then sources = [[([], node)]]
      else ∃ rawChildren rankedChildren,
        List.Forall₂ (DeclarativeAddressedExpansion m children fuel)
          (children node) rawChildren ∧
        rankedChildren.Perm rawChildren ∧
        rankedChildren.Pairwise (fun left right =>
          compareAddressedSources m left right ≠ Ordering.lt) ∧
        sources = [[([], node)]] ++ OfficialRuleMajorKey.mergeAddressedChildren rankedChildren

end ExactOfficialRuleMajorKey

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def exactOfficialRuleMajorRootKey (node : OfficialCIPNode V) (complete : Bool) :
    ExactOfficialRuleMajorKey V where
  sourceNodes := [[([], node)]]
  complete := complete

def buildExactOfficialRuleMajorKey (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    Nat → OfficialCIPNode V → Option (ExactOfficialRuleMajorKey V)
  | 0, node => some (exactOfficialRuleMajorRootKey node (children node).isEmpty)
  | fuel + 1, node =>
      let childNodes := children node
      if childNodes.isEmpty then
        some (exactOfficialRuleMajorRootKey node true)
      else do
        let childKeys ← childNodes.mapM (m.buildExactOfficialRuleMajorKey children fuel)
        let sorted ← ExactOfficialRuleMajorKey.sort? m childKeys
        some (ExactOfficialRuleMajorKey.assemble
          (exactOfficialRuleMajorRootKey node false) sorted)

private theorem exact_mapM_mem_source {α β : Type*} (f : α → Option β) :
    ∀ (inputs : List α) (outputs : List β), inputs.mapM f = some outputs →
      ∀ output, output ∈ outputs → ∃ input, input ∈ inputs ∧ f input = some output
  | [], outputs, computed, output, present => by simp at computed; subst outputs; simp at present
  | input :: inputs, outputs, computed, output, present => by
      rw [List.mapM_cons] at computed
      cases headComputed : f input with
      | none => rw [headComputed] at computed; contradiction
      | some head =>
          cases tailComputed : inputs.mapM f with
          | none => rw [headComputed, tailComputed] at computed; contradiction
          | some tail =>
              rw [headComputed, tailComputed] at computed
              injection computed with identity
              subst outputs
              rcases List.mem_cons.mp present with rfl | tailPresent
              · exact ⟨input, by simp, headComputed⟩
              · obtain ⟨source, sourcePresent, sourceComputed⟩ :=
                  exact_mapM_mem_source f inputs tail tailComputed output tailPresent
                exact ⟨source, by simp [sourcePresent], sourceComputed⟩

private theorem exact_mapM_forall₂_map {α β γ : Type*} (f : α → Option β) (g : β → γ)
    (P : α → γ → Prop) :
    ∀ (inputs : List α) (outputs : List β), inputs.mapM f = some outputs →
      (∀ input output, f input = some output → P input (g output)) →
      List.Forall₂ P inputs (outputs.map g)
  | [], outputs, computed, sound => by simp at computed; subst outputs; exact .nil
  | input :: inputs, outputs, computed, sound => by
      rw [List.mapM_cons] at computed
      cases headComputed : f input with
      | none => rw [headComputed] at computed; contradiction
      | some head =>
          cases tailComputed : inputs.mapM f with
          | none => rw [headComputed, tailComputed] at computed; contradiction
          | some tail =>
              rw [headComputed, tailComputed] at computed
              injection computed with identity
              subst outputs
              exact List.Forall₂.cons (sound input head headComputed)
                (exact_mapM_forall₂_map f g P inputs tail tailComputed sound)

private theorem exact_mapM_exists_complete {α V : Type*}
    (build : α → Option (ExactOfficialRuleMajorKey V)) :
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
        exact_mapM_exists_complete build values tailComplete
      refine ⟨key :: keys, by simp [keyComputed, keysComputed], ?_⟩
      intro observed present
      rcases List.mem_cons.mp present with rfl | tailPresent
      · exact keyComplete
      · exact keysComplete observed tailPresent

theorem buildExactOfficialRuleMajorKey_complete_of_expansionCompleteWithin
    (m : MoleculeGraph V) (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ fuel node, OfficialExpansionCompleteWithin children fuel node →
      ∃ key, m.buildExactOfficialRuleMajorKey children fuel node = some key ∧
        key.complete = true
  | 0, node, complete => by
      change children node = [] at complete
      refine ⟨exactOfficialRuleMajorRootKey node true, ?_, rfl⟩
      simp [buildExactOfficialRuleMajorKey, complete]
  | fuel + 1, node, complete => by
      by_cases terminal : children node = []
      · refine ⟨exactOfficialRuleMajorRootKey node true, ?_, rfl⟩
        simp [buildExactOfficialRuleMajorKey, terminal]
      · have childrenComplete : ∀ child, child ∈ children node →
            ∃ key, m.buildExactOfficialRuleMajorKey children fuel child = some key ∧
              key.complete = true := by
          intro child present
          exact buildExactOfficialRuleMajorKey_complete_of_expansionCompleteWithin
            m children fuel child (complete child present)
        obtain ⟨childKeys, childKeysComputed, childKeysComplete⟩ :=
          exact_mapM_exists_complete
            (m.buildExactOfficialRuleMajorKey children fuel) (children node) childrenComplete
        have sortExists := ExactOfficialRuleMajorKey.sort?_isSome_of_complete
          m childKeys childKeysComplete
        obtain ⟨sorted, sortedComputed⟩ := Option.isSome_iff_exists.mp sortExists
        have sortedPermutation := ExactOfficialRuleMajorKey.sort?_perm
          m childKeys sorted sortedComputed
        have sortedComplete : ∀ key, key ∈ sorted → key.complete = true := by
          intro key present
          exact childKeysComplete key ((sortedPermutation.mem_iff).mp present)
        refine ⟨ExactOfficialRuleMajorKey.assemble
          (exactOfficialRuleMajorRootKey node false) sorted, ?_, ?_⟩
        · simp [buildExactOfficialRuleMajorKey, terminal, childKeysComputed, sortedComputed]
        · change sorted.all ExactOfficialRuleMajorKey.complete = true
          exact List.all_eq_true.mpr sortedComplete

theorem buildExactOfficialRuleMajorKey_sourceNodes_head
    (m : MoleculeGraph V) (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ fuel node key,
      m.buildExactOfficialRuleMajorKey children fuel node = some key →
      key.sourceNodes.head? = some [([], node)]
  | 0, node, key, computed => by
      simp [buildExactOfficialRuleMajorKey] at computed
      subst key
      rfl
  | fuel + 1, node, key, computed => by
      unfold buildExactOfficialRuleMajorKey at computed
      dsimp only at computed
      by_cases terminal : (children node).isEmpty = true
      · simp [terminal] at computed
        subst key
        rfl
      · rw [if_neg terminal] at computed
        cases childKeysComputed : (children node).mapM
            (m.buildExactOfficialRuleMajorKey children fuel) with
        | none => simp [childKeysComputed] at computed
        | some childKeys =>
            cases sortedComputed : ExactOfficialRuleMajorKey.sort? m childKeys with
            | none => simp [childKeysComputed, sortedComputed] at computed
            | some sorted =>
                simp [childKeysComputed, sortedComputed] at computed
                subst key
                rfl

private theorem exact_sourceNodes_pairwise_of_descending
    (m : MoleculeGraph V) (keys : List (ExactOfficialRuleMajorKey V))
    (descending : ExactOfficialRuleMajorKey.Descending m keys) :
    (keys.map ExactOfficialRuleMajorKey.sourceNodes).Pairwise fun left right =>
      ExactOfficialRuleMajorKey.compareAddressedSources m left right ≠ Ordering.lt := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
      rw [List.map_cons, List.pairwise_cons]
      constructor
      · intro sources present
        rw [List.mem_map] at present
        obtain ⟨tail, tailPresent, rfl⟩ := present
        exact (List.pairwise_cons.mp descending).1 tail tailPresent
      · exact ih (List.pairwise_cons.mp descending).2

theorem buildExactOfficialRuleMajorKey_declarativeAddressedExpansion
    (m : MoleculeGraph V) (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ fuel node key,
      m.buildExactOfficialRuleMajorKey children fuel node = some key →
      ExactOfficialRuleMajorKey.DeclarativeAddressedExpansion m children
        fuel node key.sourceNodes
  | 0, node, key, computed => by
      simp [buildExactOfficialRuleMajorKey] at computed
      subst key
      rfl
  | fuel + 1, node, key, computed => by
      by_cases terminal : children node = []
      · simp [buildExactOfficialRuleMajorKey, terminal] at computed
        subst key
        simp [ExactOfficialRuleMajorKey.DeclarativeAddressedExpansion, terminal]
        rfl
      · unfold buildExactOfficialRuleMajorKey at computed
        dsimp only at computed
        rw [if_neg (by simpa using terminal)] at computed
        cases childKeysComputed : (children node).mapM
            (m.buildExactOfficialRuleMajorKey children fuel) with
        | none => simp [childKeysComputed] at computed
        | some childKeys =>
            cases sortedComputed : ExactOfficialRuleMajorKey.sort? m childKeys with
            | none => simp [childKeysComputed, sortedComputed] at computed
            | some sorted =>
                simp [childKeysComputed, sortedComputed] at computed
                subst key
                simp only [ExactOfficialRuleMajorKey.DeclarativeAddressedExpansion,
                  terminal, ↓reduceIte]
                refine ⟨childKeys.map ExactOfficialRuleMajorKey.sourceNodes,
                  sorted.map ExactOfficialRuleMajorKey.sourceNodes, ?_, ?_, ?_, rfl⟩
                · apply exact_mapM_forall₂_map
                    (m.buildExactOfficialRuleMajorKey children fuel)
                    ExactOfficialRuleMajorKey.sourceNodes
                    (fun child sources =>
                      ExactOfficialRuleMajorKey.DeclarativeAddressedExpansion
                        m children fuel child sources)
                    (children node) childKeys childKeysComputed
                  intro child childKey childComputed
                  exact buildExactOfficialRuleMajorKey_declarativeAddressedExpansion
                    m children fuel child childKey childComputed
                · exact (ExactOfficialRuleMajorKey.sort?_perm
                    m childKeys sorted sortedComputed).map ExactOfficialRuleMajorKey.sourceNodes
                · exact exact_sourceNodes_pairwise_of_descending m sorted
                    (ExactOfficialRuleMajorKey.sort?_descending
                      m childKeys sorted sortedComputed)

/-! ## Executable observation-parametric compiler -/

end MoleculeGraph

namespace ExactOfficialRuleMajorKey

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Rule-1a projection through an explicitly executable observation function. -/
def observedRule1aLayers (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (sources : OfficialRuleMajorKey.AddressedSourceLayers V) :=
  OfficialRuleMajorKey.mapSourceLayers observe sources

def compareAddressedSourcesObserved (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (left right : OfficialRuleMajorKey.AddressedSourceLayers V) : Ordering :=
  compareLex
    (Ordering.byKey (observedRule1aLayers observe)
      (OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber))
    (compareLex
      (Ordering.byKey rule1bLayers
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b))
      (Ordering.byKey (rule2Layers m)
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat)))
    left right

def compareObserved (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber) :
    ExactOfficialRuleMajorKey V → ExactOfficialRuleMajorKey V → Ordering :=
  Ordering.byKey ExactOfficialRuleMajorKey.sourceNodes
    (compareAddressedSourcesObserved m observe)

def compareAddressedSourceTraceObserved (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (left right : OfficialRuleMajorKey.AddressedSourceLayers V) :
    List CIPRuleDecision :=
  [ { rule := CIPRuleFamily.atomicNumber
      outcome := OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber
        (observedRule1aLayers observe left) (observedRule1aLayers observe right) }
  , { rule := CIPRuleFamily.duplicateAtom
      outcome := OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
        (rule1bLayers left) (rule1bLayers right) }
  , { rule := CIPRuleFamily.isotopeMass
      outcome := OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (rule2Layers m left) (rule2Layers m right) }
  ]

def compareTraceObserved (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (left right : ExactOfficialRuleMajorKey V) : List CIPRuleDecision :=
  compareAddressedSourceTraceObserved m observe left.sourceNodes right.sourceNodes

def compareObserved? (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (left right : ExactOfficialRuleMajorKey V) : Option Ordering :=
  match OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber
      (observedRule1aLayers observe left.sourceNodes)
      (observedRule1aLayers observe right.sourceNodes) with
  | .lt => some .lt
  | .gt => some .gt
  | .eq => if left.complete && right.complete then
      some (compareObserved m observe left right) else none

def insertObserved? (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (key : ExactOfficialRuleMajorKey V) :
    List (ExactOfficialRuleMajorKey V) → Option (List (ExactOfficialRuleMajorKey V))
  | [] => some [key]
  | head :: tail =>
      match compareObserved? m observe key head with
      | none => none
      | some .gt | some .eq => some (key :: head :: tail)
      | some .lt => (insertObserved? m observe key tail).map fun sorted => head :: sorted

def sortObserved? (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber) :
    List (ExactOfficialRuleMajorKey V) → Option (List (ExactOfficialRuleMajorKey V))
  | [] => some []
  | key :: keys => do
      let sorted ← sortObserved? m observe keys
      insertObserved? m observe key sorted

theorem observedRule1aLayers_eq_exact (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (correct : ∀ node, observe node = m.exactOfficialRule1aObservation node)
    (sources : OfficialRuleMajorKey.AddressedSourceLayers V) :
    observedRule1aLayers observe sources = exactRule1aLayers m sources := by
  have functionIdentity : observe = m.exactOfficialRule1aObservation := funext correct
  subst observe
  rfl

theorem compareAddressedSourcesObserved_eq_exact (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (correct : ∀ node, observe node = m.exactOfficialRule1aObservation node)
    (left right : OfficialRuleMajorKey.AddressedSourceLayers V) :
    compareAddressedSourcesObserved m observe left right =
      compareAddressedSources m left right := by
  unfold compareAddressedSourcesObserved compareAddressedSources
  have functionIdentity : observedRule1aLayers observe = exactRule1aLayers m := by
    funext sources
    exact observedRule1aLayers_eq_exact m observe correct sources
  rw [functionIdentity]

theorem compareObserved_eq_exact (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (correct : ∀ node, observe node = m.exactOfficialRule1aObservation node)
    (left right : ExactOfficialRuleMajorKey V) :
    compareObserved m observe left right = compare m left right := by
  unfold compareObserved compare
  rw [show compareAddressedSourcesObserved m observe = compareAddressedSources m by
    funext first second
    exact compareAddressedSourcesObserved_eq_exact m observe correct first second]

theorem compareAddressedSourceTraceObserved_eq_exact (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (correct : ∀ node, observe node = m.exactOfficialRule1aObservation node)
    (left right : OfficialRuleMajorKey.AddressedSourceLayers V) :
    compareAddressedSourceTraceObserved m observe left right =
      compareAddressedSourceTrace m left right := by
  unfold compareAddressedSourceTraceObserved compareAddressedSourceTrace
  have functionIdentity : observedRule1aLayers observe = exactRule1aLayers m := by
    funext sources
    exact observedRule1aLayers_eq_exact m observe correct sources
  rw [functionIdentity]

theorem compareTraceObserved_eq_exact (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (correct : ∀ node, observe node = m.exactOfficialRule1aObservation node)
    (left right : ExactOfficialRuleMajorKey V) :
    compareTraceObserved m observe left right = compareTrace m left right :=
  compareAddressedSourceTraceObserved_eq_exact m observe correct _ _

theorem compareObserved?_eq_exact (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (correct : ∀ node, observe node = m.exactOfficialRule1aObservation node)
    (left right : ExactOfficialRuleMajorKey V) :
    compareObserved? m observe left right = compare? m left right := by
  unfold compareObserved? compare?
  rw [show observedRule1aLayers observe = exactRule1aLayers m by
    funext sources
    exact observedRule1aLayers_eq_exact m observe correct sources]
  split <;> simp [compareObserved_eq_exact m observe correct]

theorem insertObserved?_eq_exact (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (correct : ∀ node, observe node = m.exactOfficialRule1aObservation node)
    (key : ExactOfficialRuleMajorKey V) : ∀ keys,
    insertObserved? m observe key keys = insert? m key keys
  | [] => rfl
  | head :: tail => by
      unfold insertObserved? insert?
      rw [compareObserved?_eq_exact m observe correct]
      cases compared : compare? m key head <;>
        simp [insertObserved?_eq_exact m observe correct key tail]

theorem sortObserved?_eq_exact (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (correct : ∀ node, observe node = m.exactOfficialRule1aObservation node) : ∀ keys,
    sortObserved? m observe keys = sort? m keys
  | [] => rfl
  | key :: keys => by
      unfold sortObserved? sort?
      rw [sortObserved?_eq_exact m observe correct keys]
      cases sorted : sort? m keys <;>
        simp [insertObserved?_eq_exact m observe correct]

end ExactOfficialRuleMajorKey

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Executable exact-key compiler parameterized by a proved-correct finite observation function. -/
def buildObservedExactOfficialRuleMajorKey (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    Nat → OfficialCIPNode V → Option (ExactOfficialRuleMajorKey V)
  | 0, node => some (exactOfficialRuleMajorRootKey node (children node).isEmpty)
  | fuel + 1, node =>
      let childNodes := children node
      if childNodes.isEmpty then
        some (exactOfficialRuleMajorRootKey node true)
      else do
        let childKeys ← childNodes.mapM
          (m.buildObservedExactOfficialRuleMajorKey observe children fuel)
        let sorted ← ExactOfficialRuleMajorKey.sortObserved? m observe childKeys
        some (ExactOfficialRuleMajorKey.assemble
          (exactOfficialRuleMajorRootKey node false) sorted)

/-- Replacing the independent observation by an extensionally equal executable observation leaves
the complete recursive compiler unchanged. -/
theorem buildObservedExactOfficialRuleMajorKey_eq_exact
    (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    (correct : ∀ node, observe node = m.exactOfficialRule1aObservation node)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) : ∀ fuel node,
    m.buildObservedExactOfficialRuleMajorKey observe children fuel node =
      m.buildExactOfficialRuleMajorKey children fuel node
  | 0, node => rfl
  | fuel + 1, node => by
      unfold buildObservedExactOfficialRuleMajorKey buildExactOfficialRuleMajorKey
      dsimp only
      split <;> rename_i terminal
      · rfl
      · have childBuilderIdentity :
            m.buildObservedExactOfficialRuleMajorKey observe children fuel =
              m.buildExactOfficialRuleMajorKey children fuel := by
          funext child
          exact buildObservedExactOfficialRuleMajorKey_eq_exact
            m observe correct children fuel child
        rw [childBuilderIdentity]
        cases childKeysComputed : (children node).mapM
            (m.buildExactOfficialRuleMajorKey children fuel) with
        | none => rfl
        | some childKeys =>
            change (do
              let sorted ← ExactOfficialRuleMajorKey.sortObserved? m observe childKeys
              some (ExactOfficialRuleMajorKey.assemble
                (exactOfficialRuleMajorRootKey node false) sorted)) =
              (do
                let sorted ← ExactOfficialRuleMajorKey.sort? m childKeys
                some (ExactOfficialRuleMajorKey.assemble
                  (exactOfficialRuleMajorRootKey node false) sorted))
            rw [ExactOfficialRuleMajorKey.sortObserved?_eq_exact
              m observe correct childKeys]


end MoleculeGraph

end

end TetraStereo.OneCenter
