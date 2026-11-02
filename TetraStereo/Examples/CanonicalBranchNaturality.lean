import TetraStereo.OneCenter.BranchSphereKey

set_option autoImplicit false

namespace TetraStereo.Examples.CanonicalBranchNaturality

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule

private def carbonLabel : CIPAtomicLabel :=
  { numerator := 6, denominator := 1 }

/-- Mathematical value represented by a totalized constitutional atomic label. -/
def atomicLabelValue (label : CIPAtomicLabel) : ℚ :=
  (label.numerator : ℚ) / (label.effectiveDenominator : ℚ)

/-- Canonical mathematical comparator for atomic-label values. -/
def compareAtomicLabelValue (left right : CIPAtomicLabel) : Ordering :=
  Ordering.byKey atomicLabelValue (fun left right => compareOfLessAndEq left right) left right

/-- The executable cross-product comparison agrees with rational-number comparison. -/
theorem compareCIPAtomicLabel_eq_compare_value (left right : CIPAtomicLabel) :
    compareCIPAtomicLabel left right = compareAtomicLabelValue left right := by
  unfold compareCIPAtomicLabel compareAtomicLabelValue Ordering.byKey atomicLabelValue
  rw [LinearOrder.compare_eq_compareOfLessAndEq]
  unfold compareOfLessAndEq
  have leftPositive : (0 : ℚ) < left.effectiveDenominator := by
    have : 0 < left.effectiveDenominator := by
      simp [CIPAtomicLabel.effectiveDenominator]
    exact_mod_cast this
  have rightPositive : (0 : ℚ) < right.effectiveDenominator := by
    have : 0 < right.effectiveDenominator := by
      simp [CIPAtomicLabel.effectiveDenominator]
    exact_mod_cast this
  simp only [div_lt_div_iff₀ leftPositive rightPositive,
    div_eq_div_iff leftPositive.ne' rightPositive.ne']
  norm_cast

private local instance rationalCompareTrans :
    Std.TransCmp (fun left right : ℚ => compareOfLessAndEq left right) :=
  Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm
    (fun value => lt_irrefl value)
    (fun {_ _ _} leftMiddle middleRight => lt_trans leftMiddle middleRight)
    (fun notLeftRight notRightLeft =>
      le_antisymm (le_of_not_gt notRightLeft) (le_of_not_gt notLeftRight))

private local instance atomicValueCompareTrans : Std.TransCmp compareAtomicLabelValue := by
  unfold compareAtomicLabelValue
  infer_instance

/-- Exact rational atomic-label comparison is a transitive oriented comparator. -/
theorem compareCIPAtomicLabel_transCmp : Std.TransCmp compareCIPAtomicLabel where
  eq_swap {left right} := by
    rw [compareCIPAtomicLabel_eq_compare_value,
      compareCIPAtomicLabel_eq_compare_value]
    exact Std.OrientedCmp.eq_swap
  isLE_trans {left middle right} leftMiddle middleRight := by
    rw [compareCIPAtomicLabel_eq_compare_value] at leftMiddle middleRight ⊢
    exact Std.TransCmp.isLE_trans leftMiddle middleRight

private local instance canonicalPathTrans : Std.TransCmp compareCanonicalPath := by
  unfold compareCanonicalPath
  infer_instance

private local instance sparseEntryTrans {alpha : Type*} (compareLabel : alpha → alpha → Ordering)
    [Std.TransCmp compareLabel] : Std.TransCmp (compareSparseCanonicalEntry compareLabel) := by
  unfold compareSparseCanonicalEntry
  infer_instance

private local instance sparseLayerTrans {alpha : Type*} (compareLabel : alpha → alpha → Ordering)
    [Std.TransCmp compareLabel] : Std.TransCmp (compareSparseCanonicalLayer compareLabel) := by
  unfold compareSparseCanonicalLayer
  infer_instance

private local instance sparseLayersTrans {alpha : Type*} (compareLabel : alpha → alpha → Ordering)
    [Std.TransCmp compareLabel] : Std.TransCmp (compareSparseCanonicalLayers compareLabel) := by
  unfold compareSparseCanonicalLayers
  infer_instance

private local instance rule1bDistanceTrans : Std.TransCmp compareRule1bRootDistance := by
  unfold compareRule1bRootDistance
  infer_instance

/-- The complete production constitutional-key comparator is transitive and oriented. -/
theorem compareCanonicalBranchKeys_transCmp : Std.TransCmp compareCanonicalBranchKeys := by
  letI : Std.TransCmp compareCIPAtomicLabel := compareCIPAtomicLabel_transCmp
  unfold compareCanonicalBranchKeys
  infer_instance

/-- Weak constitutional priority is transitive for arbitrary compiled keys. -/
theorem compareCanonicalBranchKeys_le_trans {left middle right : CanonicalBranchKey}
    (leftMiddle : compareCanonicalBranchKeys left middle ≠ .gt)
    (middleRight : compareCanonicalBranchKeys middle right ≠ .gt) :
    compareCanonicalBranchKeys left right ≠ .gt := by
  letI : Std.TransCmp compareCanonicalBranchKeys := compareCanonicalBranchKeys_transCmp
  exact Std.TransCmp.le_trans leftMiddle middleRight

/-- Strict constitutional priority is transitive for arbitrary compiled keys. -/
theorem compareCanonicalBranchKeys_gt_trans {left middle right : CanonicalBranchKey}
    (leftMiddle : compareCanonicalBranchKeys left middle = .gt)
    (middleRight : compareCanonicalBranchKeys middle right = .gt) :
    compareCanonicalBranchKeys left right = .gt := by
  letI : Std.TransCmp compareCanonicalBranchKeys := compareCanonicalBranchKeys_transCmp
  exact Std.TransCmp.gt_trans leftMiddle middleRight

/-- Constitutional-key ties are transitive. -/
theorem compareCanonicalBranchKeys_eq_trans {left middle right : CanonicalBranchKey}
    (leftMiddle : compareCanonicalBranchKeys left middle = .eq)
    (middleRight : compareCanonicalBranchKeys middle right = .eq) :
    compareCanonicalBranchKeys left right = .eq := by
  letI : Std.TransCmp compareCanonicalBranchKeys := compareCanonicalBranchKeys_transCmp
  exact Std.TransCmp.eq_trans leftMiddle middleRight

/-- Every compiled constitutional key ties itself. -/
theorem compareCanonicalBranchKeys_refl (key : CanonicalBranchKey) :
    compareCanonicalBranchKeys key key = .eq := by
  letI : Std.TransCmp compareCanonicalBranchKeys := compareCanonicalBranchKeys_transCmp
  have oriented := Std.OrientedCmp.eq_swap
    (cmp := compareCanonicalBranchKeys) (a := key) (b := key)
  cases decision : compareCanonicalBranchKeys key key <;>
    simp [decision] at oriented ⊢

/-- The weak constitutional priority induced by the comparator is total. -/
theorem compareCanonicalBranchKeys_le_total (left right : CanonicalBranchKey) :
    compareCanonicalBranchKeys left right ≠ .gt ∨
      compareCanonicalBranchKeys right left ≠ .gt := by
  letI : Std.TransCmp compareCanonicalBranchKeys := compareCanonicalBranchKeys_transCmp
  cases decision : compareCanonicalBranchKeys left right with
  | lt => exact Or.inl (by simp)
  | eq => exact Or.inl (by simp)
  | gt =>
      exact Or.inr (by
        have reverse : compareCanonicalBranchKeys right left = .lt :=
          Std.OrientedCmp.gt_iff_lt.mp decision
        simp [reverse])

/-- Constitutional equality is the tie relation of the complete rule-major comparator. -/
def ConstitutionallyEquivalent (left right : CanonicalBranchKey) : Prop :=
  compareCanonicalBranchKeys left right = .eq

instance constitutionalKeySetoid : Setoid CanonicalBranchKey where
  r := ConstitutionallyEquivalent
  iseqv := {
    refl := compareCanonicalBranchKeys_refl
    symm := by
      intro left right tied
      letI : Std.TransCmp compareCanonicalBranchKeys := compareCanonicalBranchKeys_transCmp
      exact Std.OrientedCmp.eq_symm tied
    trans := by
      intro left middle right leftMiddle middleRight
      exact compareCanonicalBranchKeys_eq_trans leftMiddle middleRight }

/-- Opponent-independent constitutional hierarchy signature: a compiled key modulo the exact
ties of the lawful Rules-1a/1b/2 comparator. -/
abbrev ConstitutionalHierarchySignature := Quotient constitutionalKeySetoid

def constitutionalHierarchySignature (key : CanonicalBranchKey) :
    ConstitutionalHierarchySignature :=
  Quotient.mk' key

/-- Two compiled keys have the same hierarchy signature exactly when the constitutional comparator
ties them. -/
theorem constitutionalHierarchySignature_eq_iff (left right : CanonicalBranchKey) :
    constitutionalHierarchySignature left = constitutionalHierarchySignature right ↔
      compareCanonicalBranchKeys left right = .eq := by
  exact Quotient.eq'

/-! ### Atom relabeling of production raw molecules -/

/-- Extend a permutation of the valid atom indices by the identity outside the molecule. -/
def extendAtomPermutation (mol : RawMolecule) (permutation : Equiv.Perm (Fin mol.atomCount)) :
    Equiv.Perm ℕ :=
  permutation.extendDomain
    (Fin.equivSubtype : Fin mol.atomCount ≃ { index : ℕ // index < mol.atomCount })

def relabelRawBond (permutation : Equiv.Perm ℕ) (bond : RawBond) : RawBond :=
  { source := permutation bond.source
    target := permutation bond.target
    kind := bond.kind }

/-- Relabel a parsed molecule by a finite atom permutation.  The atom at old index `i` moves to
`permutation i`; bond endpoints move covariantly.  Neighbour-order metadata is intentionally erased:
the constitutional hierarchical-digraph builder consumes only the atom and bond relations. -/
def relabelRawMolecule (mol : RawMolecule) (permutation : Equiv.Perm (Fin mol.atomCount)) :
    RawMolecule :=
  let atomPermutation := extendAtomPermutation mol permutation
  { atoms := List.ofFn fun index => mol.atoms.get (permutation.symm index)
    bonds := mol.bonds.map (relabelRawBond atomPermutation)
    neighborOrder := [] }

/-- Transport one canonical digraph node along an atom permutation. -/
def relabelCanonicalNode (mol : RawMolecule) (permutation : Equiv.Perm (Fin mol.atomCount))
    (node : CanonicalBranchNode) : CanonicalBranchNode :=
  let atomPermutation := extendAtomPermutation mol permutation
  { atom := atomPermutation node.atom
    parent := atomPermutation node.parent
    history := node.history.map atomPermutation
    provenance := node.provenance }

def relabelCanonicalChildCopy (permutation : Equiv.Perm ℕ) (copy : ℕ × ℕ) : ℕ × ℕ :=
  (permutation copy.1, copy.2)

private theorem listGet?_eq_some_get {alpha : Type*} (values : List alpha)
    (index : Fin values.length) :
    listGet? values index = some (values.get index) := by
  induction values with
  | nil => exact Fin.elim0 index
  | cons value values inductionHypothesis =>
      refine Fin.cases ?_ (fun tail => ?_) index
      · rfl
      · simpa [listGet?] using inductionHypothesis tail

private theorem listGet?_eq_none_of_length_le {alpha : Type*} (values : List alpha)
    (index : ℕ) (outside : values.length ≤ index) :
    listGet? values index = none := by
  induction values generalizing index with
  | nil => rfl
  | cons value values inductionHypothesis =>
      cases index with
      | zero => simp at outside
      | succ index =>
          simp only [listGet?]
          apply inductionHypothesis
          simpa using outside

@[simp] theorem relabelRawMolecule_atomCount (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) :
    (relabelRawMolecule mol permutation).atomCount = mol.atomCount := by
  simp [relabelRawMolecule, RawMolecule.atomCount]

theorem extendAtomPermutation_apply (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (index : Fin mol.atomCount) :
    extendAtomPermutation mol permutation index = permutation index := by
  simpa [extendAtomPermutation] using
    permutation.extendDomain_apply_image Fin.equivSubtype index

/-- Atom lookup commutes with finite relabeling on every valid atom index. -/
theorem relabelRawMolecule_atomAt (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (index : Fin mol.atomCount) :
    (relabelRawMolecule mol permutation).atomAt? (permutation index) =
      mol.atomAt? index := by
  let relabeled := relabelRawMolecule mol permutation
  let newIndex : Fin relabeled.atoms.length :=
    ⟨permutation index, by
      simp [relabeled, relabelRawMolecule, RawMolecule.atomCount]
      ⟩
  unfold RawMolecule.atomAt?
  change listGet? relabeled.atoms newIndex = listGet? mol.atoms index
  rw [listGet?_eq_some_get relabeled.atoms newIndex,
    listGet?_eq_some_get mol.atoms index]
  simp [relabeled, newIndex, relabelRawMolecule]

/-- Atom lookup commutes with relabeling on all natural-number indices; the extended permutation
fixes indices outside the molecule and both lookups return `none`. -/
theorem relabelRawMolecule_atomAt_all (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (index : ℕ) :
    (relabelRawMolecule mol permutation).atomAt?
        (extendAtomPermutation mol permutation index) = mol.atomAt? index := by
  by_cases valid : index < mol.atomCount
  · let finiteIndex : Fin mol.atomCount := ⟨index, valid⟩
    rw [show extendAtomPermutation mol permutation index = permutation finiteIndex by
      simpa [finiteIndex] using extendAtomPermutation_apply mol permutation finiteIndex]
    simpa [finiteIndex] using relabelRawMolecule_atomAt mol permutation finiteIndex
  · have fixed : extendAtomPermutation mol permutation index = index := by
      simpa [extendAtomPermutation] using
        permutation.extendDomain_apply_not_subtype Fin.equivSubtype valid
    unfold RawMolecule.atomAt?
    rw [fixed]
    apply Eq.trans
      (listGet?_eq_none_of_length_le (relabelRawMolecule mol permutation).atoms index (by
        simpa [relabelRawMolecule, RawMolecule.atomCount] using Nat.le_of_not_gt valid))
    symm
    exact listGet?_eq_none_of_length_le mol.atoms index
      (by simpa [RawMolecule.atomCount] using Nat.le_of_not_gt valid)

theorem relabelRawMolecule_atomZAt (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (index : Fin mol.atomCount) :
    (relabelRawMolecule mol permutation).atomZAt (permutation index) = mol.atomZAt index := by
  simp [RawMolecule.atomZAt, relabelRawMolecule_atomAt]

theorem relabelRawMolecule_atomMassAt (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (index : Fin mol.atomCount) :
    (relabelRawMolecule mol permutation).atomMassAt (permutation index) = mol.atomMassAt index := by
  simp [RawMolecule.atomMassAt, RawMolecule.atomMassAt?, relabelRawMolecule_atomAt]

theorem relabelRawMolecule_atomZAt_all (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (index : ℕ) :
    (relabelRawMolecule mol permutation).atomZAt
        (extendAtomPermutation mol permutation index) = mol.atomZAt index := by
  simp [RawMolecule.atomZAt, relabelRawMolecule_atomAt_all]

theorem relabelRawMolecule_atomMassAt_all (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (index : ℕ) :
    (relabelRawMolecule mol permutation).atomMassAt
        (extendAtomPermutation mol permutation index) = mol.atomMassAt index := by
  simp [RawMolecule.atomMassAt, RawMolecule.atomMassAt?, relabelRawMolecule_atomAt_all]

/-- Directed bond order commutes with relabeling, including indices outside the valid atom range
where the extended permutation is the identity. -/
theorem relabelRawMolecule_directedBondOrder (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (source target : ℕ) :
    (relabelRawMolecule mol permutation).directedBondOrder
        (extendAtomPermutation mol permutation source)
        (extendAtomPermutation mol permutation target) =
      mol.directedBondOrder source target := by
  let atomPermutation := extendAtomPermutation mol permutation
  let relabelBond : RawBond → RawBond := fun bond =>
    { source := atomPermutation bond.source
      target := atomPermutation bond.target
      kind := bond.kind }
  have foldRelabel : ∀ (bonds : List RawBond) (initial : BondOrder),
      (bonds.map relabelBond).foldl
          (fun order bond =>
            if bond.directedConnects (atomPermutation source) (atomPermutation target) then
              max order bond.kind.order
            else order)
          initial =
        bonds.foldl
          (fun order bond =>
            if bond.directedConnects source target then max order bond.kind.order else order)
          initial := by
    intro bonds initial
    induction bonds generalizing initial with
    | nil => rfl
    | cons bond bonds inductionHypothesis =>
        simp only [List.map_cons, List.foldl_cons]
        rw [inductionHypothesis]
        simp [relabelBond, RawBond.directedConnects, atomPermutation,
          (extendAtomPermutation mol permutation).injective.eq_iff]
  simpa [RawMolecule.directedBondOrder, relabelRawMolecule, relabelBond,
    atomPermutation] using foldRelabel mol.bonds 0

/-- Symmetric constitutional bond order commutes with atom relabeling. -/
theorem relabelRawMolecule_bondOrder (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (source target : ℕ) :
    (relabelRawMolecule mol permutation).bondOrder
        (extendAtomPermutation mol permutation source)
        (extendAtomPermutation mol permutation target) =
      mol.bondOrder source target := by
  simp [RawMolecule.bondOrder, relabelRawMolecule_directedBondOrder,
    (extendAtomPermutation mol permutation).injective.eq_iff]

private theorem firstNatIndex?_map_equiv (permutation : Equiv.Perm ℕ)
    (target : ℕ) (values : List ℕ) :
    firstNatIndex? (permutation target) (values.map permutation) =
      firstNatIndex? target values := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp [firstNatIndex?, permutation.injective.eq_iff, inductionHypothesis]

@[simp] theorem relabelCanonicalNode_depth (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (node : CanonicalBranchNode) :
    (relabelCanonicalNode mol permutation node).depth = node.depth := by
  simp [relabelCanonicalNode, CanonicalBranchNode.depth]

@[simp] theorem relabelCanonicalNode_forcedLeaf (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (node : CanonicalBranchNode) :
    (relabelCanonicalNode mol permutation node).forcedLeaf = node.forcedLeaf := by
  cases node.provenance <;> rfl

@[simp] theorem relabelCanonicalNode_rule1bRootDistance (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (node : CanonicalBranchNode) :
    (relabelCanonicalNode mol permutation node).rule1bRootDistance =
      node.rule1bRootDistance := by
  cases provenance : node.provenance <;>
    simp [CanonicalBranchNode.rule1bRootDistance, relabelCanonicalNode, provenance,
      CanonicalBranchNode.depth]

theorem relabelCanonicalNode_historyDistance (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (node : CanonicalBranchNode) (atom : ℕ) :
    canonicalHistoryDistance (relabelCanonicalNode mol permutation node)
        (extendAtomPermutation mol permutation atom) =
      canonicalHistoryDistance node atom := by
  unfold canonicalHistoryDistance
  change
    (firstNatIndex? (extendAtomPermutation mol permutation atom)
      (node.history.map (extendAtomPermutation mol permutation)).reverse).getD
        ((relabelCanonicalNode mol permutation node).depth + 1) = _
  rw [← List.map_reverse]
  rw [firstNatIndex?_map_equiv]
  simp

@[simp] theorem relabelCanonicalRoot (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (center atom : ℕ) :
    relabelCanonicalNode mol permutation (canonicalRoot center atom) =
      canonicalRoot (extendAtomPermutation mol permutation center)
        (extendAtomPermutation mol permutation atom) := by
  rfl

theorem relabelRawMolecule_isTrigonalPyramidalOxidoRootEdge (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (center oxygen : ℕ) :
    (relabelRawMolecule mol permutation).isTrigonalPyramidalOxidoRootEdge
        (extendAtomPermutation mol permutation center)
        (extendAtomPermutation mol permutation oxygen) =
      mol.isTrigonalPyramidalOxidoRootEdge center oxygen := by
  simp [RawMolecule.isTrigonalPyramidalOxidoRootEdge,
    relabelRawMolecule_atomAt_all, relabelRawMolecule_bondOrder]

theorem relabelRawMolecule_canonicalBondOrder (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (node : CanonicalBranchNode) (next : ℕ) :
    (relabelRawMolecule mol permutation).canonicalBondOrder
        (relabelCanonicalNode mol permutation node)
        (extendAtomPermutation mol permutation next) =
      mol.canonicalBondOrder node next := by
  cases history : node.history with
  | nil =>
      simp [RawMolecule.canonicalBondOrder, relabelCanonicalNode, history,
        relabelRawMolecule_bondOrder]
  | cons current rest =>
      cases rest with
      | nil =>
          simp [RawMolecule.canonicalBondOrder, relabelCanonicalNode, history,
            relabelRawMolecule_bondOrder]
      | cons center tail =>
          cases tail with
          | nil =>
              simp [RawMolecule.canonicalBondOrder, relabelCanonicalNode, history,
                relabelRawMolecule_bondOrder,
                relabelRawMolecule_isTrigonalPyramidalOxidoRootEdge,
                (extendAtomPermutation mol permutation).injective.eq_iff]
          | cons nextHistory tail =>
              simp [RawMolecule.canonicalBondOrder, relabelCanonicalNode, history,
                relabelRawMolecule_bondOrder]

private theorem eraseCanonicalParentCopy_map_equiv (permutation : Equiv.Perm ℕ)
    (parent : ℕ) (copies : List (ℕ × ℕ)) :
    eraseCanonicalParentCopy (permutation parent)
        (copies.map (relabelCanonicalChildCopy permutation)) =
      (eraseCanonicalParentCopy parent copies).map
        (relabelCanonicalChildCopy permutation) := by
  induction copies with
  | nil => rfl
  | cons copy copies inductionHypothesis =>
      rcases copy with ⟨atom, copyIndex⟩
      simp only [List.map_cons, eraseCanonicalParentCopy,
        relabelCanonicalChildCopy]
      by_cases parentCopy : atom = parent ∧ copyIndex = 0
      · simp [parentCopy]
      · simp [parentCopy, inductionHypothesis]
        rfl

private def canonicalCopiesFromBond (mol : RawMolecule) (node : CanonicalBranchNode)
    (bond : RawBond) : List (ℕ × ℕ) :=
  let next? :=
    if bond.source == node.atom then some bond.target
    else if bond.target == node.atom then some bond.source
    else none
  match next? with
  | none => []
  | some next =>
      (List.range (mol.canonicalBondOrder node next)).map fun copyIndex =>
        (next, copyIndex)

private theorem canonicalCopiesFromBond_relabel (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (node : CanonicalBranchNode)
    (bond : RawBond) :
    canonicalCopiesFromBond (relabelRawMolecule mol permutation)
        (relabelCanonicalNode mol permutation node)
        (relabelRawBond (extendAtomPermutation mol permutation) bond) =
      (canonicalCopiesFromBond mol node bond).map
        (relabelCanonicalChildCopy (extendAtomPermutation mol permutation)) := by
  by_cases source : bond.source = node.atom
  · simp [canonicalCopiesFromBond, relabelRawBond, relabelCanonicalNode, source]
    change
      List.map (fun copyIndex =>
          (extendAtomPermutation mol permutation bond.target, copyIndex))
          (List.range ((relabelRawMolecule mol permutation).canonicalBondOrder
            (relabelCanonicalNode mol permutation node)
            (extendAtomPermutation mol permutation bond.target))) = _
    rw [relabelRawMolecule_canonicalBondOrder]
    simp [Function.comp_def, relabelCanonicalChildCopy]
  · by_cases target : bond.target = node.atom
    · simp [canonicalCopiesFromBond, relabelRawBond, relabelCanonicalNode,
        source, target]
      change
        List.map (fun copyIndex =>
            (extendAtomPermutation mol permutation bond.source, copyIndex))
            (List.range ((relabelRawMolecule mol permutation).canonicalBondOrder
              (relabelCanonicalNode mol permutation node)
              (extendAtomPermutation mol permutation bond.source))) = _
      rw [relabelRawMolecule_canonicalBondOrder]
      simp [Function.comp_def, relabelCanonicalChildCopy]
    · simp [canonicalCopiesFromBond, relabelRawBond, relabelCanonicalNode,
        source, target,
        (extendAtomPermutation mol permutation).injective.eq_iff]

/-- Child-copy generation commutes exactly with atom relabeling.  In particular, the real copy of
the parent edge is deleted in either representation at the corresponding position. -/
theorem relabelRawMolecule_canonicalChildCopies (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (node : CanonicalBranchNode) :
    (relabelRawMolecule mol permutation).canonicalChildCopies
        (relabelCanonicalNode mol permutation node) =
      (mol.canonicalChildCopies node).map
        (relabelCanonicalChildCopy (extendAtomPermutation mol permutation)) := by
  let atomPermutation := extendAtomPermutation mol permutation
  unfold RawMolecule.canonicalChildCopies
  change eraseCanonicalParentCopy (atomPermutation node.parent)
      ((mol.bonds.map (relabelRawBond atomPermutation)).flatMap fun bond =>
        canonicalCopiesFromBond (relabelRawMolecule mol permutation)
          (relabelCanonicalNode mol permutation node) bond) = _
  rw [List.flatMap_map]
  have inner :
      (mol.bonds.flatMap fun bond =>
          canonicalCopiesFromBond (relabelRawMolecule mol permutation)
            (relabelCanonicalNode mol permutation node)
            (relabelRawBond atomPermutation bond)) =
        (mol.bonds.flatMap fun bond => canonicalCopiesFromBond mol node bond).map
          (relabelCanonicalChildCopy atomPermutation) := by
    induction mol.bonds with
    | nil => rfl
    | cons bond bonds inductionHypothesis =>
        simp only [List.flatMap_cons, List.map_append]
        rw [canonicalCopiesFromBond_relabel, inductionHypothesis]
  rw [inner, eraseCanonicalParentCopy_map_equiv]
  rfl

/-- The entire ordered child-node list is natural under atom relabeling.  Real atoms, ring
duplicates, and multiple-bond duplicates are created with exactly transported provenance. -/
private theorem listContains_map_equiv (permutation : Equiv.Perm ℕ)
    (target : ℕ) (values : List ℕ) :
    (values.map permutation).contains (permutation target) = values.contains target := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp [permutation.injective.eq_iff]

private theorem eraseDupsByLoop_map_equiv (permutation : Equiv.Perm ℕ)
    (values kept : List ℕ) :
    List.eraseDupsBy.loop (fun left right : ℕ => left == right)
        (values.map permutation) (kept.map permutation) =
      (List.eraseDupsBy.loop (fun left right : ℕ => left == right) values kept).map
        permutation := by
  induction values generalizing kept with
  | nil => simp [List.eraseDupsBy.loop]
  | cons value values inductionHypothesis =>
      simp only [List.map_cons, List.eraseDupsBy.loop]
      have anyNatural :
          (kept.map permutation).any (fun other => permutation value == other) =
            kept.any (fun other => value == other) := by
        induction kept with
        | nil => rfl
        | cons other kept inductionHypothesis =>
            simp only [List.map_cons, List.any_cons]
            rw [show (permutation value == permutation other) = (value == other) by
              simp [permutation.injective.eq_iff]]
            rw [inductionHypothesis]
      rw [anyNatural]
      split
      · exact inductionHypothesis kept
      · exact inductionHypothesis (value :: kept)

private theorem eraseDups_map_equiv (permutation : Equiv.Perm ℕ) (values : List ℕ) :
    (values.map permutation).eraseDups = values.eraseDups.map permutation := by
  unfold List.eraseDups List.eraseDupsBy
  exact eraseDupsByLoop_map_equiv permutation values []

private def incidentAtomFromBond (atom : ℕ) (bond : RawBond) : Option ℕ :=
  if bond.source == atom then some bond.target
  else if bond.target == atom then some bond.source
  else none

private theorem incidentAtomFromBond_relabel (permutation : Equiv.Perm ℕ)
    (atom : ℕ) (bond : RawBond) :
    incidentAtomFromBond (permutation atom) (relabelRawBond permutation bond) =
      (incidentAtomFromBond atom bond).map permutation := by
  by_cases source : bond.source = atom
  · simp [incidentAtomFromBond, relabelRawBond, source]
  · by_cases target : bond.target = atom
    · simp [incidentAtomFromBond, relabelRawBond, source, target,
        permutation.injective.eq_iff]
    · simp [incidentAtomFromBond, relabelRawBond, source, target,
        permutation.injective.eq_iff]

/-- Neighbour enumeration is equivariant, including its first-occurrence duplicate elimination. -/
theorem relabelRawMolecule_incidentAtoms (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (atom : ℕ) :
    (relabelRawMolecule mol permutation).incidentAtoms
        (extendAtomPermutation mol permutation atom) =
      (mol.incidentAtoms atom).map (extendAtomPermutation mol permutation) := by
  let atomPermutation := extendAtomPermutation mol permutation
  have filtered :
      (mol.bonds.map (relabelRawBond atomPermutation)).filterMap
          (incidentAtomFromBond (atomPermutation atom)) =
        (mol.bonds.filterMap (incidentAtomFromBond atom)).map atomPermutation := by
    induction mol.bonds with
    | nil => rfl
    | cons bond bonds inductionHypothesis =>
        simp only [List.map_cons, List.filterMap_cons]
        rw [incidentAtomFromBond_relabel, inductionHypothesis]
        cases incidentAtomFromBond atom bond <;> rfl
  unfold RawMolecule.incidentAtoms
  change
    ((mol.bonds.map (relabelRawBond atomPermutation)).filterMap
      (incidentAtomFromBond (atomPermutation atom))).eraseDups = _
  rw [filtered, eraseDups_map_equiv]
  rfl

private theorem firstSome_map_equiv {alpha beta gamma delta : Type*}
    (transportInput : alpha → beta) (transportOutput : gamma → delta)
    (left : beta → Option delta) (right : alpha → Option gamma)
    (natural : ∀ value, left (transportInput value) = (right value).map transportOutput)
    (values : List alpha) :
    firstSome left (values.map transportInput) =
      (firstSome right values).map transportOutput := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp only [List.map_cons, firstSome]
      rw [natural, inductionHypothesis]
      cases right value <;> rfl

theorem relabelRawMolecule_alternatingPathTo (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount))
    (blocked target expectedOrder fuel current : ℕ) (visited : List ℕ) :
    (relabelRawMolecule mol permutation).alternatingPathTo
        (extendAtomPermutation mol permutation blocked)
        (extendAtomPermutation mol permutation target) expectedOrder fuel
        (extendAtomPermutation mol permutation current)
        (visited.map (extendAtomPermutation mol permutation)) =
      mol.alternatingPathTo blocked target expectedOrder fuel current visited := by
  induction fuel generalizing expectedOrder current visited with
  | zero =>
      simp [RawMolecule.alternatingPathTo,
        (extendAtomPermutation mol permutation).injective.eq_iff]
  | succ fuel inductionHypothesis =>
      simp only [RawMolecule.alternatingPathTo]
      rw [show (extendAtomPermutation mol permutation current ==
          extendAtomPermutation mol permutation target) = (current == target) by
        simp [(extendAtomPermutation mol permutation).injective.eq_iff]]
      split
      · rfl
      · rw [relabelRawMolecule_incidentAtoms]
        simp only [List.any_map]
        apply congrArg (fun predicate => (mol.incidentAtoms current).any predicate)
        funext next
        simp only [Function.comp_apply]
        rw [show (extendAtomPermutation mol permutation next !=
            extendAtomPermutation mol permutation blocked) = (next != blocked) by
          unfold bne
          rw [show (extendAtomPermutation mol permutation next ==
              extendAtomPermutation mol permutation blocked) = (next == blocked) by
            simp [(extendAtomPermutation mol permutation).injective.eq_iff]]]
        rw [listContains_map_equiv, relabelRawMolecule_bondOrder]
        rw [show extendAtomPermutation mol permutation current ::
            visited.map (extendAtomPermutation mol permutation) =
            (current :: visited).map (extendAtomPermutation mol permutation) by rfl]
        rw [inductionHypothesis]

theorem relabelRawMolecule_alternatingPath? (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount))
    (blocked target expectedOrder fuel current : ℕ) (visited : List ℕ) :
    (relabelRawMolecule mol permutation).alternatingPath?
        (extendAtomPermutation mol permutation blocked)
        (extendAtomPermutation mol permutation target) expectedOrder fuel
        (extendAtomPermutation mol permutation current)
        (visited.map (extendAtomPermutation mol permutation)) =
      (mol.alternatingPath? blocked target expectedOrder fuel current visited).map
        (List.map (extendAtomPermutation mol permutation)) := by
  induction fuel generalizing expectedOrder current visited with
  | zero =>
      simp [RawMolecule.alternatingPath?,
        (extendAtomPermutation mol permutation).injective.eq_iff]
  | succ fuel inductionHypothesis =>
      simp only [RawMolecule.alternatingPath?]
      rw [show (extendAtomPermutation mol permutation current ==
          extendAtomPermutation mol permutation target) = (current == target) by
        simp [(extendAtomPermutation mol permutation).injective.eq_iff]]
      split
      · rfl
      · rw [relabelRawMolecule_incidentAtoms]
        apply firstSome_map_equiv
        intro next
        have condition :
            ((extendAtomPermutation mol permutation next !=
                extendAtomPermutation mol permutation blocked) &&
              !(visited.map (extendAtomPermutation mol permutation)).contains
                (extendAtomPermutation mol permutation next) &&
              (relabelRawMolecule mol permutation).bondOrder
                (extendAtomPermutation mol permutation current)
                (extendAtomPermutation mol permutation next) == expectedOrder) =
              (next != blocked && !visited.contains next &&
                mol.bondOrder current next == expectedOrder) := by
          rw [show (extendAtomPermutation mol permutation next !=
              extendAtomPermutation mol permutation blocked) = (next != blocked) by
            unfold bne
            rw [show (extendAtomPermutation mol permutation next ==
                extendAtomPermutation mol permutation blocked) = (next == blocked) by
              simp [(extendAtomPermutation mol permutation).injective.eq_iff]]]
          rw [listContains_map_equiv, relabelRawMolecule_bondOrder]
        rw [condition]
        split
        · rw [show extendAtomPermutation mol permutation current ::
              visited.map (extendAtomPermutation mol permutation) =
              (current :: visited).map (extendAtomPermutation mol permutation) by rfl]
          rw [inductionHypothesis]
          cases mol.alternatingPath? blocked target
              (if expectedOrder == 1 then 2 else 1) fuel next (current :: visited) <;> rfl
        · rfl

private def relabelEdge (permutation : Equiv.Perm ℕ) (edge : ℕ × ℕ) : ℕ × ℕ :=
  (permutation edge.1, permutation edge.2)

private theorem cycleEdges_map_equiv (permutation : Equiv.Perm ℕ) (cycle : List ℕ) :
    cycleEdges (cycle.map permutation) = (cycleEdges cycle).map (relabelEdge permutation) := by
  cases cycle with
  | nil => rfl
  | cons first rest =>
      change
        (permutation first :: rest.map permutation).zip
            (rest.map permutation ++ [permutation first]) =
          ((first :: rest).zip (rest ++ [first])).map (relabelEdge permutation)
      rw [show rest.map permutation ++ [permutation first] =
          (rest ++ [first]).map permutation by simp]
      rw [show permutation first :: rest.map permutation =
          (first :: rest).map permutation by rfl]
      rw [List.zip_map]
      rfl

private def reachableNeighborFromBond (blocked atom : ℕ) (bond : RawBond) : Option ℕ :=
  if bond.source == atom && bond.target != blocked then some bond.target
  else if bond.target == atom && bond.source != blocked then some bond.source
  else none

private theorem reachableNeighborFromBond_relabel (permutation : Equiv.Perm ℕ)
    (blocked atom : ℕ) (bond : RawBond) :
    reachableNeighborFromBond (permutation blocked) (permutation atom)
        (relabelRawBond permutation bond) =
      (reachableNeighborFromBond blocked atom bond).map permutation := by
  by_cases source : bond.source = atom
  · by_cases blockedTarget : bond.target = blocked
    · simp [reachableNeighborFromBond, relabelRawBond, source, blockedTarget,
        permutation.injective.eq_iff, bne]
    · simp [reachableNeighborFromBond, relabelRawBond, source, blockedTarget,
        permutation.injective.eq_iff, bne]
  · by_cases target : bond.target = atom
    · by_cases blockedSource : bond.source = blocked
      · simp [reachableNeighborFromBond, relabelRawBond, target, blockedSource,
          permutation.injective.eq_iff, bne]
      · simp [reachableNeighborFromBond, relabelRawBond, source, target, blockedSource,
          permutation.injective.eq_iff, bne]
    · simp [reachableNeighborFromBond, relabelRawBond, source, target,
        permutation.injective.eq_iff, bne]

private def reachableCandidates (mol : RawMolecule) (blocked : ℕ)
    (frontier seen : List ℕ) : List ℕ :=
  (frontier.flatMap fun atom =>
    mol.bonds.filterMap (reachableNeighborFromBond blocked atom)).filter fun atom =>
      !(seen.contains atom)

private theorem reachableCandidates_relabel (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (blocked : ℕ)
    (frontier seen : List ℕ) :
    reachableCandidates (relabelRawMolecule mol permutation)
        (extendAtomPermutation mol permutation blocked)
        (frontier.map (extendAtomPermutation mol permutation))
        (seen.map (extendAtomPermutation mol permutation)) =
      (reachableCandidates mol blocked frontier seen).map
        (extendAtomPermutation mol permutation) := by
  let atomPermutation := extendAtomPermutation mol permutation
  have bondFilter : ∀ atom,
      (mol.bonds.map (relabelRawBond atomPermutation)).filterMap
          (reachableNeighborFromBond (atomPermutation blocked) (atomPermutation atom)) =
        (mol.bonds.filterMap (reachableNeighborFromBond blocked atom)).map atomPermutation := by
    intro atom
    induction mol.bonds with
    | nil => rfl
    | cons bond bonds inductionHypothesis =>
        simp only [List.map_cons, List.filterMap_cons]
        rw [reachableNeighborFromBond_relabel, inductionHypothesis]
        cases reachableNeighborFromBond blocked atom bond <;> rfl
  have flattened :
      ((frontier.map atomPermutation).flatMap fun atom =>
          (mol.bonds.map (relabelRawBond atomPermutation)).filterMap
            (reachableNeighborFromBond (atomPermutation blocked) atom)) =
        (frontier.flatMap fun atom =>
          mol.bonds.filterMap (reachableNeighborFromBond blocked atom)).map atomPermutation := by
    rw [List.flatMap_map]
    induction frontier with
    | nil => rfl
    | cons atom frontier inductionHypothesis =>
        simp only [List.flatMap_cons, List.map_append]
        rw [bondFilter, inductionHypothesis]
  unfold reachableCandidates
  change
    (List.filter (fun atom => !(seen.map atomPermutation).contains atom)
      ((frontier.map atomPermutation).flatMap fun atom =>
        (mol.bonds.map (relabelRawBond atomPermutation)).filterMap
          (reachableNeighborFromBond (atomPermutation blocked) atom))) = _
  rw [flattened]
  induction frontier.flatMap fun atom =>
      mol.bonds.filterMap (reachableNeighborFromBond blocked atom) with
  | nil => rfl
  | cons atom atoms inductionHypothesis =>
      simp only [List.map_cons, List.filter_cons]
      rw [listContains_map_equiv, inductionHypothesis]
      split <;> rfl

theorem relabelRawMolecule_reachableAvoiding (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount))
    (fuel blocked : ℕ) (frontier seen : List ℕ) :
    (relabelRawMolecule mol permutation).reachableAvoiding fuel
        (extendAtomPermutation mol permutation blocked)
        (frontier.map (extendAtomPermutation mol permutation))
        (seen.map (extendAtomPermutation mol permutation)) =
      (mol.reachableAvoiding fuel blocked frontier seen).map
        (extendAtomPermutation mol permutation) := by
  induction fuel generalizing frontier seen with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      cases frontier with
      | nil => rfl
      | cons atom frontier =>
          simp only [RawMolecule.reachableAvoiding]
          change
            (relabelRawMolecule mol permutation).reachableAvoiding fuel
              (extendAtomPermutation mol permutation blocked)
              ((reachableCandidates (relabelRawMolecule mol permutation)
                (extendAtomPermutation mol permutation blocked)
                ((atom :: frontier).map (extendAtomPermutation mol permutation))
                (seen.map (extendAtomPermutation mol permutation))).eraseDups)
              (seen.map (extendAtomPermutation mol permutation) ++
                (reachableCandidates (relabelRawMolecule mol permutation)
                  (extendAtomPermutation mol permutation blocked)
                  ((atom :: frontier).map (extendAtomPermutation mol permutation))
                  (seen.map (extendAtomPermutation mol permutation))).eraseDups) = _
          rw [reachableCandidates_relabel, eraseDups_map_equiv]
          rw [← List.map_append]
          exact inductionHypothesis _ _

theorem relabelRawMolecule_cycleIsMancude (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (cycle : List ℕ) :
    (relabelRawMolecule mol permutation).cycleIsMancude
        (cycle.map (extendAtomPermutation mol permutation)) =
      mol.cycleIsMancude cycle := by
  let atomPermutation := extendAtomPermutation mol permutation
  unfold RawMolecule.cycleIsMancude
  rw [cycleEdges_map_equiv, List.length_map]
  dsimp only
  have doubleEdges :
      ((cycleEdges cycle).map (relabelEdge atomPermutation)).filter
          (fun edge => (relabelRawMolecule mol permutation).bondOrder edge.1 edge.2 == 2) =
        ((cycleEdges cycle).filter fun edge => mol.bondOrder edge.1 edge.2 == 2).map
          (relabelEdge atomPermutation) := by
    induction cycleEdges cycle with
    | nil => rfl
    | cons edge edges inductionHypothesis =>
        rcases edge with ⟨left, right⟩
        simp only [List.map_cons, List.filter_cons, relabelEdge]
        rw [relabelRawMolecule_bondOrder, inductionHypothesis]
        split <;> rfl
  rw [doubleEdges, List.length_map]
  simp only [List.all_map]
  apply congrArg (fun condition =>
    ((cycleEdges cycle).filter fun edge => mol.bondOrder edge.1 edge.2 == 2).length ==
      cycle.length / 2 && condition)
  apply congrArg (fun predicate => cycle.all predicate)
  funext atom
  simp only [Function.comp_apply]
  rw [relabelRawMolecule_incidentAtoms]
  have neighbours :
      ((mol.incidentAtoms atom).map atomPermutation).filter
          (fun neighbor => (cycle.map atomPermutation).contains neighbor &&
            (relabelRawMolecule mol permutation).bondOrder (atomPermutation atom) neighbor == 2) =
        ((mol.incidentAtoms atom).filter fun neighbor =>
          cycle.contains neighbor && mol.bondOrder atom neighbor == 2).map atomPermutation := by
    induction mol.incidentAtoms atom with
    | nil => rfl
    | cons neighbor neighbors inductionHypothesis =>
        simp only [List.map_cons, List.filter_cons]
        rw [listContains_map_equiv, relabelRawMolecule_bondOrder, inductionHypothesis]
        split <;> rfl
  rw [neighbours, List.length_map]

theorem relabelRawMolecule_cycleHasExternalReentry (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (cycle : List ℕ) :
    (relabelRawMolecule mol permutation).cycleHasExternalReentry
        (cycle.map (extendAtomPermutation mol permutation)) =
      mol.cycleHasExternalReentry cycle := by
  let atomPermutation := extendAtomPermutation mol permutation
  unfold RawMolecule.cycleHasExternalReentry
  simp only [List.any_map]
  apply congrArg (fun predicate => cycle.any predicate)
  funext atom
  simp only [Function.comp_apply]
  rw [relabelRawMolecule_incidentAtoms]
  simp only [List.any_map]
  apply congrArg (fun predicate => (mol.incidentAtoms atom).any predicate)
  funext neighbor
  simp only [Function.comp_apply]
  rw [listContains_map_equiv]
  rw [relabelRawMolecule_atomCount]
  rw [show [atomPermutation neighbor] = [neighbor].map atomPermutation by rfl]
  rw [relabelRawMolecule_reachableAvoiding]
  simp only [List.any_map]
  apply congrArg (fun predicate =>
    !cycle.contains neighbor &&
      (mol.reachableAvoiding (mol.atomCount + 1) atom [neighbor] [neighbor]).any predicate)
  funext reached
  exact listContains_map_equiv atomPermutation reached cycle

private def relabelCycleCandidate (permutation : Equiv.Perm ℕ)
    (candidate : List ℕ × ℕ) : List ℕ × ℕ :=
  (candidate.1.map permutation, permutation candidate.2)

private def simpleMancudeAlternatives (mol : RawMolecule) (attached duplicated : ℕ) :
    List (List ℕ × ℕ) :=
  (mol.incidentAtoms attached).filterMap fun candidate =>
    if candidate != duplicated && mol.bondOrder attached candidate == 1 then
      (mol.alternatingPath? attached candidate 1 (mol.atomCount + 1) duplicated
        [attached, duplicated]).map fun path => (path, candidate)
    else
      none

private theorem filterMap_map_equiv {alpha beta gamma delta : Type*}
    (transportInput : alpha → beta) (transportOutput : gamma → delta)
    (left : beta → Option delta) (right : alpha → Option gamma)
    (natural : ∀ value, left (transportInput value) = (right value).map transportOutput)
    (values : List alpha) :
    (values.map transportInput).filterMap left =
      (values.filterMap right).map transportOutput := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp only [List.map_cons, List.filterMap_cons]
      rw [natural, inductionHypothesis]
      cases right value <;> rfl

private theorem filter_map_equiv {alpha beta : Type*}
    (transport : alpha → beta) (left : beta → Bool) (right : alpha → Bool)
    (natural : ∀ value, left (transport value) = right value) (values : List alpha) :
    (values.map transport).filter left = (values.filter right).map transport := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp only [List.map_cons, List.filter_cons]
      rw [natural, inductionHypothesis]
      split <;> rfl

private theorem simpleMancudeAlternatives_relabel (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (attached duplicated : ℕ) :
    simpleMancudeAlternatives (relabelRawMolecule mol permutation)
        (extendAtomPermutation mol permutation attached)
        (extendAtomPermutation mol permutation duplicated) =
      (simpleMancudeAlternatives mol attached duplicated).map
        (relabelCycleCandidate (extendAtomPermutation mol permutation)) := by
  let atomPermutation := extendAtomPermutation mol permutation
  unfold simpleMancudeAlternatives
  rw [relabelRawMolecule_incidentAtoms]
  apply filterMap_map_equiv atomPermutation (relabelCycleCandidate atomPermutation)
  intro candidate
  have condition :
      (atomPermutation candidate != atomPermutation duplicated &&
        (relabelRawMolecule mol permutation).bondOrder
          (atomPermutation attached) (atomPermutation candidate) == 1) =
        (candidate != duplicated && mol.bondOrder attached candidate == 1) := by
    unfold bne
    rw [show (atomPermutation candidate == atomPermutation duplicated) =
        (candidate == duplicated) by simp [atomPermutation.injective.eq_iff]]
    rw [relabelRawMolecule_bondOrder]
  rw [condition]
  split
  · rw [relabelRawMolecule_atomCount]
    rw [show [atomPermutation attached, atomPermutation duplicated] =
        [attached, duplicated].map atomPermutation by rfl]
    rw [relabelRawMolecule_alternatingPath?]
    cases mol.alternatingPath? attached candidate 1 (mol.atomCount + 1) duplicated
        [attached, duplicated] <;> rfl
  · rfl

theorem relabelRawMolecule_mancudeDuplicatePartners (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (attached duplicated : ℕ) :
    (relabelRawMolecule mol permutation).mancudeDuplicatePartners
        (extendAtomPermutation mol permutation attached)
        (extendAtomPermutation mol permutation duplicated) =
      (mol.mancudeDuplicatePartners attached duplicated).map
        (extendAtomPermutation mol permutation) := by
  let atomPermutation := extendAtomPermutation mol permutation
  unfold RawMolecule.mancudeDuplicatePartners
  rw [show ((relabelRawMolecule mol permutation).bondOrder
      (atomPermutation attached) (atomPermutation duplicated) != 2) =
      (mol.bondOrder attached duplicated != 2) by
    rw [relabelRawMolecule_bondOrder]]
  split
  · rfl
  · rw [relabelRawMolecule_incidentAtoms]
    have alternates :
        ((mol.incidentAtoms attached).map atomPermutation).filter
            (fun candidate =>
              candidate != atomPermutation duplicated &&
                (relabelRawMolecule mol permutation).bondOrder
                    (atomPermutation attached) candidate == 1 &&
                  (relabelRawMolecule mol permutation).alternatingPathTo
                    (atomPermutation attached) candidate 1
                    ((relabelRawMolecule mol permutation).atomCount + 1)
                    (atomPermutation duplicated)
                    [atomPermutation attached, atomPermutation duplicated]) =
          ((mol.incidentAtoms attached).filter fun candidate =>
            candidate != duplicated && mol.bondOrder attached candidate == 1 &&
              mol.alternatingPathTo attached candidate 1 (mol.atomCount + 1) duplicated
                [attached, duplicated]).map atomPermutation := by
      apply filter_map_equiv atomPermutation
      intro candidate
      rw [show (atomPermutation candidate != atomPermutation duplicated) =
          (candidate != duplicated) by
        unfold bne
        rw [show (atomPermutation candidate == atomPermutation duplicated) =
            (candidate == duplicated) by simp [atomPermutation.injective.eq_iff]]]
      rw [relabelRawMolecule_bondOrder, relabelRawMolecule_atomCount]
      rw [show [atomPermutation attached, atomPermutation duplicated] =
          [attached, duplicated].map atomPermutation by rfl]
      rw [relabelRawMolecule_alternatingPathTo]
    rw [alternates]
    change
      (atomPermutation duplicated ::
        ((mol.incidentAtoms attached).filter fun candidate =>
          candidate != duplicated && mol.bondOrder attached candidate == 1 &&
            mol.alternatingPathTo attached candidate 1 (mol.atomCount + 1) duplicated
              [attached, duplicated]).map atomPermutation).eraseDups = _
    rw [show atomPermutation duplicated ::
        ((mol.incidentAtoms attached).filter fun candidate =>
          candidate != duplicated && mol.bondOrder attached candidate == 1 &&
            mol.alternatingPathTo attached candidate 1 (mol.atomCount + 1) duplicated
              [attached, duplicated]).map atomPermutation =
        (duplicated :: (mol.incidentAtoms attached).filter fun candidate =>
          candidate != duplicated && mol.bondOrder attached candidate == 1 &&
            mol.alternatingPathTo attached candidate 1 (mol.atomCount + 1) duplicated
              [attached, duplicated]).map atomPermutation by rfl]
    exact eraseDups_map_equiv atomPermutation _

theorem relabelRawMolecule_incidentDoubleBondCount (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (atom : ℕ) :
    (relabelRawMolecule mol permutation).incidentDoubleBondCount
        (extendAtomPermutation mol permutation atom) =
      mol.incidentDoubleBondCount atom := by
  let atomPermutation := extendAtomPermutation mol permutation
  unfold RawMolecule.incidentDoubleBondCount
  have filtered :
      (mol.bonds.map (relabelRawBond atomPermutation)).filter
          (fun bond => bond.kind.order == 2 &&
            (bond.source == atomPermutation atom || bond.target == atomPermutation atom)) =
        (mol.bonds.filter fun bond => bond.kind.order == 2 &&
          (bond.source == atom || bond.target == atom)).map (relabelRawBond atomPermutation) := by
    apply filter_map_equiv (relabelRawBond atomPermutation)
    intro bond
    simp only [relabelRawBond]
    rw [show (atomPermutation bond.source == atomPermutation atom) =
        (bond.source == atom) by simp [atomPermutation.injective.eq_iff]]
    rw [show (atomPermutation bond.target == atomPermutation atom) =
        (bond.target == atom) by simp [atomPermutation.injective.eq_iff]]
  change
    ((mol.bonds.map (relabelRawBond atomPermutation)).filter
      (fun bond => bond.kind.order == 2 &&
        (bond.source == atomPermutation atom || bond.target == atomPermutation atom))).length = _
  rw [filtered, List.length_map]

theorem relabelRawMolecule_localizedMancudeVertex (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (atom : ℕ) :
    (relabelRawMolecule mol permutation).localizedMancudeVertex
        (extendAtomPermutation mol permutation atom) =
      mol.localizedMancudeVertex atom := by
  unfold RawMolecule.localizedMancudeVertex
  rw [relabelRawMolecule_incidentDoubleBondCount,
    relabelRawMolecule_atomAt_all]

theorem relabelRawMolecule_localizedMancudeCandidateEdges (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) :
    (relabelRawMolecule mol permutation).localizedMancudeCandidateEdges =
      mol.localizedMancudeCandidateEdges.map
        (relabelEdge (extendAtomPermutation mol permutation)) := by
  let atomPermutation := extendAtomPermutation mol permutation
  unfold RawMolecule.localizedMancudeCandidateEdges
  apply filterMap_map_equiv (relabelRawBond atomPermutation) (relabelEdge atomPermutation)
  intro bond
  simp only [relabelRawBond]
  rw [relabelRawMolecule_localizedMancudeVertex,
    relabelRawMolecule_localizedMancudeVertex]
  split <;> rfl

private def edgeNeighborWithout (blocked : ℕ × ℕ) (atom : ℕ)
    (edge : ℕ × ℕ) : Option ℕ :=
  let isBlocked :=
    (edge.1 == blocked.1 && edge.2 == blocked.2) ||
      (edge.1 == blocked.2 && edge.2 == blocked.1)
  if isBlocked then none
  else if edge.1 == atom then some edge.2
  else if edge.2 == atom then some edge.1
  else none

private theorem edgeNeighborWithout_relabel (permutation : Equiv.Perm ℕ)
    (blocked : ℕ × ℕ) (atom : ℕ) (edge : ℕ × ℕ) :
    edgeNeighborWithout (relabelEdge permutation blocked) (permutation atom)
        (relabelEdge permutation edge) =
      (edgeNeighborWithout blocked atom edge).map permutation := by
  rcases blocked with ⟨blockedLeft, blockedRight⟩
  rcases edge with ⟨left, right⟩
  simp only [edgeNeighborWithout, relabelEdge]
  rw [show ((permutation left == permutation blockedLeft &&
      permutation right == permutation blockedRight) ||
      (permutation left == permutation blockedRight &&
        permutation right == permutation blockedLeft)) =
      ((left == blockedLeft && right == blockedRight) ||
        (left == blockedRight && right == blockedLeft)) by
    rw [show (permutation left == permutation blockedLeft) = (left == blockedLeft) by
      simp [permutation.injective.eq_iff]]
    rw [show (permutation right == permutation blockedRight) = (right == blockedRight) by
      simp [permutation.injective.eq_iff]]
    rw [show (permutation left == permutation blockedRight) = (left == blockedRight) by
      simp [permutation.injective.eq_iff]]
    rw [show (permutation right == permutation blockedLeft) = (right == blockedLeft) by
      simp [permutation.injective.eq_iff]]]
  split
  · rfl
  · rw [show (permutation left == permutation atom) = (left == atom) by
        simp [permutation.injective.eq_iff]]
    split
    · rfl
    · rw [show (permutation right == permutation atom) = (right == atom) by
          simp [permutation.injective.eq_iff]]
      split <;> rfl

private def reachableWithoutEdgeCandidates (blocked : ℕ × ℕ)
    (edges : List (ℕ × ℕ)) (frontier seen : List ℕ) : List ℕ :=
  (frontier.flatMap fun atom =>
    edges.filterMap (edgeNeighborWithout blocked atom)).filter fun atom =>
      !(seen.contains atom)

private theorem reachableWithoutEdgeCandidates_relabel (permutation : Equiv.Perm ℕ)
    (blocked : ℕ × ℕ) (edges : List (ℕ × ℕ)) (frontier seen : List ℕ) :
    reachableWithoutEdgeCandidates (relabelEdge permutation blocked)
        (edges.map (relabelEdge permutation)) (frontier.map permutation)
        (seen.map permutation) =
      (reachableWithoutEdgeCandidates blocked edges frontier seen).map permutation := by
  unfold reachableWithoutEdgeCandidates
  have edgeFilter : ∀ atom,
      (edges.map (relabelEdge permutation)).filterMap
          (edgeNeighborWithout (relabelEdge permutation blocked) (permutation atom)) =
        (edges.filterMap (edgeNeighborWithout blocked atom)).map permutation := by
    intro atom
    apply filterMap_map_equiv (relabelEdge permutation) permutation
    exact edgeNeighborWithout_relabel permutation blocked atom
  have flattened :
      ((frontier.map permutation).flatMap fun atom =>
        (edges.map (relabelEdge permutation)).filterMap
          (edgeNeighborWithout (relabelEdge permutation blocked) atom)) =
        (frontier.flatMap fun atom =>
          edges.filterMap (edgeNeighborWithout blocked atom)).map permutation := by
    rw [List.flatMap_map]
    induction frontier with
    | nil => rfl
    | cons atom frontier inductionHypothesis =>
        simp only [List.flatMap_cons, List.map_append]
        rw [edgeFilter, inductionHypothesis]
  rw [flattened]
  apply filter_map_equiv permutation
  intro atom
  rw [listContains_map_equiv]

private theorem flatMap_const_nil {alpha beta : Type*} (values : List alpha) :
    values.flatMap (fun _ => ([] : List beta)) = [] := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      exact inductionHypothesis

theorem reachableWithoutEdge_relabel (permutation : Equiv.Perm ℕ)
    (blocked : ℕ × ℕ) (fuel : ℕ) (edges : List (ℕ × ℕ))
    (frontier seen : List ℕ) :
    reachableWithoutEdge (relabelEdge permutation blocked) fuel
        (edges.map (relabelEdge permutation)) (frontier.map permutation)
        (seen.map permutation) =
      (reachableWithoutEdge blocked fuel edges frontier seen).map permutation := by
  induction fuel generalizing frontier seen with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      cases frontier with
      | nil => rfl
      | cons atom frontier =>
          cases edges with
          | nil =>
              simpa [reachableWithoutEdge, flatMap_const_nil] using
                inductionHypothesis [] seen
          | cons edge edges =>
              simp only [reachableWithoutEdge]
              change reachableWithoutEdge (relabelEdge permutation blocked) fuel
                  ((edge :: edges).map (relabelEdge permutation))
                  ((reachableWithoutEdgeCandidates (relabelEdge permutation blocked)
                    ((edge :: edges).map (relabelEdge permutation))
                    ((atom :: frontier).map permutation) (seen.map permutation)).eraseDups)
                  (seen.map permutation ++
                    (reachableWithoutEdgeCandidates (relabelEdge permutation blocked)
                      ((edge :: edges).map (relabelEdge permutation))
                      ((atom :: frontier).map permutation) (seen.map permutation)).eraseDups) = _
              rw [reachableWithoutEdgeCandidates_relabel, eraseDups_map_equiv]
              rw [← List.map_append]
              exact inductionHypothesis _ _

theorem relabelRawMolecule_localizedMancudeEdges (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) :
    (relabelRawMolecule mol permutation).localizedMancudeEdges =
      mol.localizedMancudeEdges.map
        (relabelEdge (extendAtomPermutation mol permutation)) := by
  let atomPermutation := extendAtomPermutation mol permutation
  unfold RawMolecule.localizedMancudeEdges
  rw [relabelRawMolecule_localizedMancudeCandidateEdges]
  apply filter_map_equiv (relabelEdge atomPermutation)
  intro edge
  simp only [relabelEdge, List.length_map]
  rw [show [atomPermutation edge.1] = [edge.1].map atomPermutation by rfl]
  change
    (reachableWithoutEdge (relabelEdge atomPermutation edge)
      (mol.localizedMancudeCandidateEdges.length + 1)
      (mol.localizedMancudeCandidateEdges.map (relabelEdge atomPermutation))
      ([edge.1].map atomPermutation) ([edge.1].map atomPermutation)).contains
        (atomPermutation edge.2) = _
  rw [reachableWithoutEdge_relabel]
  exact listContains_map_equiv atomPermutation edge.2 _

theorem containsUndirectedEdge_relabel (permutation : Equiv.Perm ℕ)
    (edges : List (ℕ × ℕ)) (left right : ℕ) :
    containsUndirectedEdge (edges.map (relabelEdge permutation))
        (permutation left) (permutation right) =
      containsUndirectedEdge edges left right := by
  unfold containsUndirectedEdge
  simp only [List.any_map]
  apply congrArg (fun predicate => edges.any predicate)
  funext edge
  rcases edge with ⟨edgeLeft, edgeRight⟩
  simp only [Function.comp_apply, relabelEdge]
  rw [show (permutation edgeLeft == permutation left) = (edgeLeft == left) by
    simp [permutation.injective.eq_iff]]
  rw [show (permutation edgeRight == permutation right) = (edgeRight == right) by
    simp [permutation.injective.eq_iff]]
  rw [show (permutation edgeLeft == permutation right) = (edgeLeft == right) by
    simp [permutation.injective.eq_iff]]
  rw [show (permutation edgeRight == permutation left) = (edgeRight == left) by
    simp [permutation.injective.eq_iff]]

private def edgeNeighbor (atom : ℕ) (edge : ℕ × ℕ) : Option ℕ :=
  if edge.1 == atom then some edge.2
  else if edge.2 == atom then some edge.1
  else none

private theorem edgeNeighbor_relabel (permutation : Equiv.Perm ℕ)
    (atom : ℕ) (edge : ℕ × ℕ) :
    edgeNeighbor (permutation atom) (relabelEdge permutation edge) =
      (edgeNeighbor atom edge).map permutation := by
  rcases edge with ⟨left, right⟩
  simp only [edgeNeighbor, relabelEdge]
  rw [show (permutation left == permutation atom) = (left == atom) by
    simp [permutation.injective.eq_iff]]
  split
  · rfl
  · rw [show (permutation right == permutation atom) = (right == atom) by
      simp [permutation.injective.eq_iff]]
    split <;> rfl

private def edgeComponentCandidates (edges : List (ℕ × ℕ))
    (frontier seen : List ℕ) : List ℕ :=
  (frontier.flatMap fun atom => edges.filterMap (edgeNeighbor atom)).filter fun atom =>
    !(seen.contains atom)

private theorem edgeComponentCandidates_relabel (permutation : Equiv.Perm ℕ)
    (edges : List (ℕ × ℕ)) (frontier seen : List ℕ) :
    edgeComponentCandidates (edges.map (relabelEdge permutation))
        (frontier.map permutation) (seen.map permutation) =
      (edgeComponentCandidates edges frontier seen).map permutation := by
  unfold edgeComponentCandidates
  have edgeFilter : ∀ atom,
      (edges.map (relabelEdge permutation)).filterMap (edgeNeighbor (permutation atom)) =
        (edges.filterMap (edgeNeighbor atom)).map permutation := by
    intro atom
    apply filterMap_map_equiv (relabelEdge permutation) permutation
    exact edgeNeighbor_relabel permutation atom
  have flattened :
      ((frontier.map permutation).flatMap fun atom =>
        (edges.map (relabelEdge permutation)).filterMap (edgeNeighbor atom)) =
        (frontier.flatMap fun atom => edges.filterMap (edgeNeighbor atom)).map permutation := by
    rw [List.flatMap_map]
    induction frontier with
    | nil => rfl
    | cons atom frontier inductionHypothesis =>
        simp only [List.flatMap_cons, List.map_append]
        rw [edgeFilter, inductionHypothesis]
  rw [flattened]
  apply filter_map_equiv permutation
  intro atom
  rw [listContains_map_equiv]

theorem edgeComponent_relabel (permutation : Equiv.Perm ℕ)
    (edges : List (ℕ × ℕ)) (fuel : ℕ) (frontier seen : List ℕ) :
    edgeComponent (edges.map (relabelEdge permutation)) fuel
        (frontier.map permutation) (seen.map permutation) =
      (edgeComponent edges fuel frontier seen).map permutation := by
  induction fuel generalizing frontier seen with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      cases frontier with
      | nil => rfl
      | cons atom frontier =>
          simp only [edgeComponent]
          change edgeComponent (edges.map (relabelEdge permutation)) fuel
              ((edgeComponentCandidates (edges.map (relabelEdge permutation))
                ((atom :: frontier).map permutation) (seen.map permutation)).eraseDups)
              (seen.map permutation ++
                (edgeComponentCandidates (edges.map (relabelEdge permutation))
                  ((atom :: frontier).map permutation) (seen.map permutation)).eraseDups) = _
          rw [edgeComponentCandidates_relabel, eraseDups_map_equiv]
          rw [← List.map_append]
          exact inductionHypothesis _ _

private def matchingRemaining (edge : ℕ × ℕ)
    (edges : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  edges.filter fun candidate =>
    candidate.1 != edge.1 && candidate.2 != edge.1 &&
      candidate.1 != edge.2 && candidate.2 != edge.2

private theorem matchingRemaining_relabel (permutation : Equiv.Perm ℕ)
    (edge : ℕ × ℕ) (edges : List (ℕ × ℕ)) :
    matchingRemaining (relabelEdge permutation edge)
        (edges.map (relabelEdge permutation)) =
      (matchingRemaining edge edges).map (relabelEdge permutation) := by
  apply filter_map_equiv (relabelEdge permutation)
  intro candidate
  rcases edge with ⟨edgeLeft, edgeRight⟩
  rcases candidate with ⟨left, right⟩
  simp only [relabelEdge]
  unfold bne
  rw [show (permutation left == permutation edgeLeft) = (left == edgeLeft) by
    simp [permutation.injective.eq_iff]]
  rw [show (permutation right == permutation edgeLeft) = (right == edgeLeft) by
    simp [permutation.injective.eq_iff]]
  rw [show (permutation left == permutation edgeRight) = (left == edgeRight) by
    simp [permutation.injective.eq_iff]]
  rw [show (permutation right == permutation edgeRight) = (right == edgeRight) by
    simp [permutation.injective.eq_iff]]

theorem relabelRawMolecule_mancudeMatchingStats (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (attached fuel : ℕ)
    (edges : List (ℕ × ℕ)) :
    (relabelRawMolecule mol permutation).mancudeMatchingStats
        (extendAtomPermutation mol permutation attached) fuel
        (edges.map (relabelEdge (extendAtomPermutation mol permutation))) =
      mol.mancudeMatchingStats attached fuel edges := by
  let atomPermutation := extendAtomPermutation mol permutation
  induction fuel generalizing edges with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      cases edges with
      | nil => rfl
      | cons edge edges =>
          simp only [List.map_cons, RawMolecule.mancudeMatchingStats]
          rw [inductionHypothesis]
          cases excluded : mol.mancudeMatchingStats attached fuel edges with
          | none => rfl
          | some excludedStats =>
              change
                (do
                  let includedTail ←
                    (relabelRawMolecule mol permutation).mancudeMatchingStats
                      (atomPermutation attached) fuel
                      (matchingRemaining (relabelEdge atomPermutation edge)
                        (edges.map (relabelEdge atomPermutation)))
                  let partnerZ :=
                    if (relabelEdge atomPermutation edge).1 == atomPermutation attached then
                      (relabelRawMolecule mol permutation).atomZAt
                        (relabelEdge atomPermutation edge).2
                    else if (relabelEdge atomPermutation edge).2 == atomPermutation attached then
                      (relabelRawMolecule mol permutation).atomZAt
                        (relabelEdge atomPermutation edge).1
                    else 0
                  let included : MancudeMatchingStats :=
                    { size := includedTail.size + 1
                      count := includedTail.count
                      partnerZSum := includedTail.partnerZSum + includedTail.count * partnerZ }
                  some (combineMancudeStats excludedStats included)) =
                (do
                  let includedTail ←
                    mol.mancudeMatchingStats attached fuel (matchingRemaining edge edges)
                  let partnerZ :=
                    if edge.1 == attached then mol.atomZAt edge.2
                    else if edge.2 == attached then mol.atomZAt edge.1 else 0
                  let included : MancudeMatchingStats :=
                    { size := includedTail.size + 1
                      count := includedTail.count
                      partnerZSum := includedTail.partnerZSum + includedTail.count * partnerZ }
                  some (combineMancudeStats excludedStats included))
              rw [matchingRemaining_relabel, inductionHypothesis]
              cases includedTail :
                  mol.mancudeMatchingStats attached fuel (matchingRemaining edge edges) with
              | none => rfl
              | some stats =>
                  have partnerNatural :
                      (if (relabelEdge atomPermutation edge).1 == atomPermutation attached then
                          (relabelRawMolecule mol permutation).atomZAt
                            (relabelEdge atomPermutation edge).2
                        else if (relabelEdge atomPermutation edge).2 == atomPermutation attached then
                          (relabelRawMolecule mol permutation).atomZAt
                            (relabelEdge atomPermutation edge).1
                        else 0) =
                        (if edge.1 == attached then mol.atomZAt edge.2
                        else if edge.2 == attached then mol.atomZAt edge.1 else 0) := by
                    rcases edge with ⟨left, right⟩
                    simp only [relabelEdge]
                    rw [show (atomPermutation left == atomPermutation attached) =
                        (left == attached) by simp [atomPermutation.injective.eq_iff]]
                    rw [show (atomPermutation right == atomPermutation attached) =
                        (right == attached) by simp [atomPermutation.injective.eq_iff]]
                    rw [relabelRawMolecule_atomZAt_all,
                      relabelRawMolecule_atomZAt_all]
                  rw [partnerNatural]

private def mancudeComponentVertices (mol : RawMolecule) (attached : ℕ) : List ℕ :=
  let allEdges := mol.localizedMancudeEdges
  edgeComponent allEdges (allEdges.length + 1) [attached] [attached]

private def mancudeComponentEdges (mol : RawMolecule) (attached : ℕ) :
    List (ℕ × ℕ) :=
  let allEdges := mol.localizedMancudeEdges
  let vertices := mancudeComponentVertices mol attached
  allEdges.filter fun edge => vertices.contains edge.1 && vertices.contains edge.2

private def simpleCycleExactComponent (mol : RawMolecule) (attached : ℕ)
    (cycle : List ℕ) : Bool :=
  let reportedEdges := cycleEdges cycle
  let localizedVertices := mancudeComponentVertices mol attached
  let localizedEdges := mancudeComponentEdges mol attached
  cycle.all localizedVertices.contains && localizedVertices.all cycle.contains &&
    reportedEdges.all (fun edge => containsUndirectedEdge localizedEdges edge.1 edge.2) &&
    localizedEdges.all (fun edge => containsUndirectedEdge reportedEdges edge.1 edge.2)

private theorem mancudeComponentVertices_relabel (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (attached : ℕ) :
    mancudeComponentVertices (relabelRawMolecule mol permutation)
        (extendAtomPermutation mol permutation attached) =
      (mancudeComponentVertices mol attached).map
        (extendAtomPermutation mol permutation) := by
  let atomPermutation := extendAtomPermutation mol permutation
  unfold mancudeComponentVertices
  rw [relabelRawMolecule_localizedMancudeEdges]
  dsimp only
  rw [List.length_map]
  change edgeComponent (mol.localizedMancudeEdges.map (relabelEdge atomPermutation))
      (mol.localizedMancudeEdges.length + 1) ([attached].map atomPermutation)
      ([attached].map atomPermutation) = _
  exact edgeComponent_relabel atomPermutation mol.localizedMancudeEdges
    (mol.localizedMancudeEdges.length + 1) [attached] [attached]

private theorem mancudeComponentEdges_relabel (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (attached : ℕ) :
    mancudeComponentEdges (relabelRawMolecule mol permutation)
        (extendAtomPermutation mol permutation attached) =
      (mancudeComponentEdges mol attached).map
        (relabelEdge (extendAtomPermutation mol permutation)) := by
  let atomPermutation := extendAtomPermutation mol permutation
  unfold mancudeComponentEdges
  rw [relabelRawMolecule_localizedMancudeEdges,
    mancudeComponentVertices_relabel]
  apply filter_map_equiv (relabelEdge atomPermutation)
  intro edge
  simp only [relabelEdge]
  rw [listContains_map_equiv, listContains_map_equiv]

private theorem simpleCycleExactComponent_relabel (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (attached : ℕ) (cycle : List ℕ) :
    simpleCycleExactComponent (relabelRawMolecule mol permutation)
        (extendAtomPermutation mol permutation attached)
        (cycle.map (extendAtomPermutation mol permutation)) =
      simpleCycleExactComponent mol attached cycle := by
  let atomPermutation := extendAtomPermutation mol permutation
  unfold simpleCycleExactComponent
  rw [cycleEdges_map_equiv, mancudeComponentVertices_relabel,
    mancudeComponentEdges_relabel]
  simp only [List.all_map]
  have hcycleVertices :
      cycle.all (((mancudeComponentVertices mol attached).map atomPermutation).contains ∘
          atomPermutation) =
        cycle.all (mancudeComponentVertices mol attached).contains := by
    apply congrArg cycle.all
    funext atom
    exact listContains_map_equiv atomPermutation atom _
  have hverticesCycle :
      (mancudeComponentVertices mol attached).all
          ((cycle.map atomPermutation).contains ∘ atomPermutation) =
        (mancudeComponentVertices mol attached).all cycle.contains := by
    apply congrArg (mancudeComponentVertices mol attached).all
    funext atom
    exact listContains_map_equiv atomPermutation atom _
  have hreportedEdges :
      (cycleEdges cycle).all
          ((fun edge => containsUndirectedEdge
            ((mancudeComponentEdges mol attached).map (relabelEdge atomPermutation))
              edge.1 edge.2) ∘ relabelEdge atomPermutation) =
        (cycleEdges cycle).all (fun edge =>
          containsUndirectedEdge (mancudeComponentEdges mol attached) edge.1 edge.2) := by
    apply congrArg (cycleEdges cycle).all
    funext edge
    rcases edge with ⟨left, right⟩
    exact containsUndirectedEdge_relabel atomPermutation
      (mancudeComponentEdges mol attached) left right
  have hlocalizedEdges :
      (mancudeComponentEdges mol attached).all
          ((fun edge => containsUndirectedEdge
            ((cycleEdges cycle).map (relabelEdge atomPermutation)) edge.1 edge.2) ∘
              relabelEdge atomPermutation) =
        (mancudeComponentEdges mol attached).all (fun edge =>
          containsUndirectedEdge (cycleEdges cycle) edge.1 edge.2) := by
    apply congrArg (mancudeComponentEdges mol attached).all
    funext edge
    rcases edge with ⟨left, right⟩
    exact containsUndirectedEdge_relabel atomPermutation (cycleEdges cycle) left right
  rw [hcycleVertices, hverticesCycle, hreportedEdges, hlocalizedEdges]

theorem relabelRawMolecule_simpleMancudeCycle? (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (attached duplicated : ℕ) :
    (relabelRawMolecule mol permutation).simpleMancudeCycle?
        (extendAtomPermutation mol permutation attached)
        (extendAtomPermutation mol permutation duplicated) =
      (mol.simpleMancudeCycle? attached duplicated).map
        (relabelCycleCandidate (extendAtomPermutation mol permutation)) := by
  let atomPermutation := extendAtomPermutation mol permutation
  unfold RawMolecule.simpleMancudeCycle?
  rw [show ((relabelRawMolecule mol permutation).bondOrder
      (atomPermutation attached) (atomPermutation duplicated) != 2) =
      (mol.bondOrder attached duplicated != 2) by
    rw [relabelRawMolecule_bondOrder]]
  split
  · rfl
  · change
      (match simpleMancudeAlternatives (relabelRawMolecule mol permutation)
          (atomPermutation attached) (atomPermutation duplicated) with
        | [(path, candidate)] =>
            let cycle := atomPermutation attached :: path
            if 3 ≤ cycle.length && cycle.eraseDups.length == cycle.length &&
                (relabelRawMolecule mol permutation).cycleIsMancude cycle &&
                simpleCycleExactComponent (relabelRawMolecule mol permutation)
                  (atomPermutation attached) cycle then
              some (cycle, candidate)
            else none
        | _ => none) =
      (match simpleMancudeAlternatives mol attached duplicated with
        | [(path, candidate)] =>
            let cycle := attached :: path
            if 3 ≤ cycle.length && cycle.eraseDups.length == cycle.length &&
                mol.cycleIsMancude cycle && simpleCycleExactComponent mol attached cycle then
              some (cycle, candidate)
            else none
        | _ => none).map (relabelCycleCandidate atomPermutation)
    rw [simpleMancudeAlternatives_relabel]
    cases alternatives : simpleMancudeAlternatives mol attached duplicated with
    | nil => rfl
    | cons candidate candidates =>
        cases candidates with
        | nil =>
            rcases candidate with ⟨path, alternate⟩
            simp only [List.map_cons, List.map_nil, relabelCycleCandidate]
            rw [show atomPermutation attached :: path.map atomPermutation =
                (attached :: path).map atomPermutation by rfl]
            rw [List.length_map, eraseDups_map_equiv, List.length_map,
              relabelRawMolecule_cycleIsMancude,
              simpleCycleExactComponent_relabel]
            split <;> rfl
        | cons second rest => rfl

private theorem generalMancudeRule1aLabel?_eq_components (mol : RawMolecule)
    (attached duplicated : ℕ) :
    mol.generalMancudeRule1aLabel? attached duplicated =
      (let vertices := mancudeComponentVertices mol attached
       let edges := mancudeComponentEdges mol attached
       if !(vertices.contains duplicated) || edges.isEmpty then none
       else do
         let stats ← mol.mancudeMatchingStats attached (edges.length + 1) edges
         let writtenDoubleCount :=
           (edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2).length
         if stats.size != writtenDoubleCount || stats.count == 0 then none
         else some ({ numerator := stats.partnerZSum, denominator := stats.count } :
           CIPAtomicLabel)) := by
  rfl

theorem relabelRawMolecule_generalMancudeRule1aLabel? (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (attached duplicated : ℕ) :
    (relabelRawMolecule mol permutation).generalMancudeRule1aLabel?
        (extendAtomPermutation mol permutation attached)
        (extendAtomPermutation mol permutation duplicated) =
      mol.generalMancudeRule1aLabel? attached duplicated := by
  let atomPermutation := extendAtomPermutation mol permutation
  rw [generalMancudeRule1aLabel?_eq_components,
    generalMancudeRule1aLabel?_eq_components]
  rw [mancudeComponentVertices_relabel, mancudeComponentEdges_relabel]
  dsimp only
  rw [listContains_map_equiv, List.isEmpty_map, List.length_map]
  split
  · rfl
  · rw [relabelRawMolecule_mancudeMatchingStats]
    cases stats : mol.mancudeMatchingStats attached
        ((mancudeComponentEdges mol attached).length + 1)
        (mancudeComponentEdges mol attached) with
    | none => rfl
    | some value =>
        have writtenDoubleEdges :
            ((mancudeComponentEdges mol attached).map (relabelEdge atomPermutation)).filter
                (fun edge =>
                  (relabelRawMolecule mol permutation).bondOrder edge.1 edge.2 == 2) =
              ((mancudeComponentEdges mol attached).filter fun edge =>
                mol.bondOrder edge.1 edge.2 == 2).map (relabelEdge atomPermutation) := by
          apply filter_map_equiv (relabelEdge atomPermutation)
          intro edge
          rcases edge with ⟨left, right⟩
          simp only [relabelEdge]
          rw [relabelRawMolecule_bondOrder]
        rw [writtenDoubleEdges, List.length_map]

theorem relabelRawMolecule_mancudeRule1aLabel? (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (attached duplicated : ℕ) :
    (relabelRawMolecule mol permutation).mancudeRule1aLabel?
        (extendAtomPermutation mol permutation attached)
        (extendAtomPermutation mol permutation duplicated) =
      mol.mancudeRule1aLabel? attached duplicated := by
  let atomPermutation := extendAtomPermutation mol permutation
  unfold RawMolecule.mancudeRule1aLabel?
  rw [relabelRawMolecule_localizedMancudeEdges]
  rw [containsUndirectedEdge_relabel]
  split
  · rw [relabelRawMolecule_atomZAt_all]
  · rw [relabelRawMolecule_simpleMancudeCycle?]
    cases cycleResult : mol.simpleMancudeCycle? attached duplicated with
    | none =>
        simp only [Option.map]
        exact relabelRawMolecule_generalMancudeRule1aLabel?
          mol permutation attached duplicated
    | some result =>
        rcases result with ⟨cycle, alternate⟩
        simp only [Option.map, relabelCycleCandidate]
        simp [RawMolecule.simpleMancudeCycleLabel, List.length_map,
          relabelRawMolecule_atomZAt_all]

/-- The derived Rule-1a label is a graph invariant: the entire bounded mancude/Kekulé
construction commutes with every finite atom relabeling. -/
theorem relabelRawMolecule_canonicalRule1aLabel? (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (node : CanonicalBranchNode) :
    (relabelRawMolecule mol permutation).canonicalRule1aLabel?
        (relabelCanonicalNode mol permutation node) =
      mol.canonicalRule1aLabel? node := by
  rcases node with ⟨atom, parent, history, provenance⟩
  cases provenance <;>
    simp [RawMolecule.canonicalRule1aLabel?, relabelCanonicalNode,
      relabelRawMolecule_atomZAt_all,
      relabelRawMolecule_mancudeRule1aLabel?]

private def canonicalChildFromCopy (node : CanonicalBranchNode)
    (copy : ℕ × ℕ) : CanonicalBranchNode :=
  let next := copy.1
  let provenance :=
    if copy.2 != 0 then
      CanonicalNodeProvenance.multipleBondDuplicate node.depth
    else if node.history.contains next then
      CanonicalNodeProvenance.ringDuplicate (canonicalHistoryDistance node next)
    else
      CanonicalNodeProvenance.realAtom
  { atom := next, parent := node.atom, history := next :: node.history,
    provenance := provenance }

private theorem canonicalChildren_eq_map_childFromCopy (mol : RawMolecule)
    (node : CanonicalBranchNode) :
    mol.canonicalChildren node =
      if node.forcedLeaf then []
      else (mol.canonicalChildCopies node).map (canonicalChildFromCopy node) := by
  rfl

private theorem canonicalChildFromCopy_relabel (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (node : CanonicalBranchNode)
    (copy : ℕ × ℕ) :
    canonicalChildFromCopy (relabelCanonicalNode mol permutation node)
        (relabelCanonicalChildCopy (extendAtomPermutation mol permutation) copy) =
      relabelCanonicalNode mol permutation (canonicalChildFromCopy node copy) := by
  rcases copy with ⟨atom, copyIndex⟩
  unfold canonicalChildFromCopy
  simp only [relabelCanonicalChildCopy, relabelCanonicalNode_depth]
  rw [show (relabelCanonicalNode mol permutation node).history.contains
      (extendAtomPermutation mol permutation atom) = node.history.contains atom by
    exact listContains_map_equiv (extendAtomPermutation mol permutation) atom node.history]
  rw [relabelCanonicalNode_historyDistance]
  rfl

theorem relabelRawMolecule_canonicalChildren (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (node : CanonicalBranchNode) :
    (relabelRawMolecule mol permutation).canonicalChildren
        (relabelCanonicalNode mol permutation node) =
      (mol.canonicalChildren node).map (relabelCanonicalNode mol permutation) := by
  rw [canonicalChildren_eq_map_childFromCopy,
    canonicalChildren_eq_map_childFromCopy]
  rw [relabelCanonicalNode_forcedLeaf, relabelRawMolecule_canonicalChildCopies]
  split
  · simp
  · rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro copy _
    exact canonicalChildFromCopy_relabel mol permutation node copy

/-- Terminality of a rooted-digraph node is independent of atom names. -/
theorem relabelRawMolecule_canonicalTerminal (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (node : CanonicalBranchNode) :
    (relabelRawMolecule mol permutation).canonicalTerminal
        (relabelCanonicalNode mol permutation node) =
      mol.canonicalTerminal node := by
  simp [RawMolecule.canonicalTerminal, relabelRawMolecule_canonicalChildren]

/-! ### Atom-name-free hierarchy keys -/

/-- Equality of every field consumed by constitutional ranking.  `realAtoms`, `sourceNodes`, and
`sourceOccurrences`, and `sourceTree?` are bookkeeping witnesses; the comparator intentionally
does not inspect them. -/
structure SameConstitutionalHierarchy (left right : CanonicalBranchKey) : Prop where
  rule1a : left.rule1a = right.rule1a
  rule1b : left.rule1b = right.rule1b
  rule2 : left.rule2 = right.rule2
  complete : left.complete = right.complete

/-- Erase representation-specific atom witnesses while retaining the complete hierarchy. -/
def constitutionalProjection (key : CanonicalBranchKey) : CanonicalBranchKey :=
  { key with realAtoms := [], sourceNodes := [], sourceOccurrences := [], sourceTree? := none }

theorem sameConstitutionalHierarchy_iff_projection_eq (left right : CanonicalBranchKey) :
    SameConstitutionalHierarchy left right ↔
      constitutionalProjection left = constitutionalProjection right := by
  constructor
  · intro equivalent
    rcases equivalent with ⟨rule1a, rule1b, rule2, complete⟩
    cases left
    cases right
    simp_all [constitutionalProjection]
  · intro projected
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [constitutionalProjection] using
        congrArg CanonicalBranchKey.rule1a projected
    · simpa [constitutionalProjection] using
        congrArg CanonicalBranchKey.rule1b projected
    · simpa [constitutionalProjection] using
        congrArg CanonicalBranchKey.rule2 projected
    · simpa [constitutionalProjection] using
        congrArg CanonicalBranchKey.complete projected

@[refl] theorem SameConstitutionalHierarchy.refl (key : CanonicalBranchKey) :
    SameConstitutionalHierarchy key key := ⟨rfl, rfl, rfl, rfl⟩

@[symm] theorem SameConstitutionalHierarchy.symm {left right : CanonicalBranchKey}
    (equivalent : SameConstitutionalHierarchy left right) :
    SameConstitutionalHierarchy right left :=
  ⟨equivalent.rule1a.symm, equivalent.rule1b.symm, equivalent.rule2.symm,
    equivalent.complete.symm⟩

@[trans] theorem SameConstitutionalHierarchy.trans {left middle right : CanonicalBranchKey}
    (leftMiddle : SameConstitutionalHierarchy left middle)
    (middleRight : SameConstitutionalHierarchy middle right) :
    SameConstitutionalHierarchy left right :=
  ⟨leftMiddle.rule1a.trans middleRight.rule1a,
    leftMiddle.rule1b.trans middleRight.rule1b,
    leftMiddle.rule2.trans middleRight.rule2,
    leftMiddle.complete.trans middleRight.complete⟩

theorem SameConstitutionalHierarchy.nodeCount_eq {left right : CanonicalBranchKey}
    (equivalent : SameConstitutionalHierarchy left right) :
    left.nodeCount = right.nodeCount := by
  simp [CanonicalBranchKey.nodeCount, equivalent.rule1a]

/-- Constitutionally equivalent compiled representations give exactly the same comparison result
against constitutionally equivalent opponents. -/
theorem compareCanonicalBranchKeys_congr {left left' right right' : CanonicalBranchKey}
    (leftEquivalent : SameConstitutionalHierarchy left left')
    (rightEquivalent : SameConstitutionalHierarchy right right') :
    compareCanonicalBranchKeys left right = compareCanonicalBranchKeys left' right' := by
  simp [compareCanonicalBranchKeys, compareLex, Ordering.byKey,
    leftEquivalent.rule1a, leftEquivalent.rule1b, leftEquivalent.rule2,
    rightEquivalent.rule1a, rightEquivalent.rule1b, rightEquivalent.rule2]

theorem compareCanonicalBranchKeys?_congr {left left' right right' : CanonicalBranchKey}
    (leftEquivalent : SameConstitutionalHierarchy left left')
    (rightEquivalent : SameConstitutionalHierarchy right right') :
    compareCanonicalBranchKeys? left right = compareCanonicalBranchKeys? left' right' := by
  simp [compareCanonicalBranchKeys?, leftEquivalent.rule1a, leftEquivalent.complete,
    rightEquivalent.rule1a, rightEquivalent.complete,
    compareCanonicalBranchKeys_congr leftEquivalent rightEquivalent]

private theorem optionRel_map {alpha beta gamma delta : Type*}
    {relation : alpha → beta → Prop} {targetRelation : gamma → delta → Prop}
    {left : Option alpha} {right : Option beta} (leftMap : alpha → gamma)
    (rightMap : beta → delta)
    (preserves : ∀ {a b}, relation a b → targetRelation (leftMap a) (rightMap b))
    (related : Option.Rel relation left right) :
    Option.Rel targetRelation (left.map leftMap) (right.map rightMap) := by
  cases left <;> cases right <;> simp_all

private theorem optionRel_bind {alpha beta gamma delta : Type*}
    {relation : alpha → beta → Prop} {targetRelation : gamma → delta → Prop}
    {left : Option alpha} {right : Option beta} (leftBind : alpha → Option gamma)
    (rightBind : beta → Option delta)
    (preserves : ∀ {a b}, relation a b →
      Option.Rel targetRelation (leftBind a) (rightBind b))
    (related : Option.Rel relation left right) :
    Option.Rel targetRelation (left.bind leftBind) (right.bind rightBind) := by
  cases left <;> cases right <;> simp_all

private theorem option_eq_of_rel_eq {alpha : Type*} {left right : Option alpha}
    (related : Option.Rel Eq left right) : left = right := by
  cases left <;> cases right <;> simp_all

private theorem insertCanonicalKey?_congr {key key' : CanonicalBranchKey}
    (keyEquivalent : SameConstitutionalHierarchy key key') :
    ∀ {keys keys' : List CanonicalBranchKey},
      List.Forall₂ SameConstitutionalHierarchy keys keys' →
      Option.Rel (List.Forall₂ SameConstitutionalHierarchy)
        (insertCanonicalKey? key keys) (insertCanonicalKey? key' keys') := by
  intro keys keys' keysEquivalent
  induction keysEquivalent with
  | nil =>
      exact Option.Rel.some
        (List.Forall₂.cons keyEquivalent List.Forall₂.nil)
  | @cons head head' heads heads' headEquivalent tailEquivalent inductionHypothesis =>
      unfold insertCanonicalKey?
      rw [compareCanonicalBranchKeys?_congr keyEquivalent headEquivalent]
      cases comparison : compareCanonicalBranchKeys? key' _ with
      | none => exact Option.Rel.none
      | some ordering =>
          cases ordering with
          | gt =>
              exact Option.Rel.some
                (List.Forall₂.cons keyEquivalent
                  (List.Forall₂.cons headEquivalent tailEquivalent))
          | eq =>
              exact Option.Rel.some
                (List.Forall₂.cons keyEquivalent
                  (List.Forall₂.cons headEquivalent tailEquivalent))
          | lt =>
              exact optionRel_map (List.cons head) (List.cons head')
                (fun related => List.Forall₂.cons headEquivalent related)
                inductionHypothesis

/-- Sorting complete child keys is natural: tied-node bookkeeping may differ, but the sorted
constitutional hierarchy is pointwise identical. -/
theorem sortCanonicalKeys?_congr {keys keys' : List CanonicalBranchKey}
    (equivalent : List.Forall₂ SameConstitutionalHierarchy keys keys') :
    Option.Rel (List.Forall₂ SameConstitutionalHierarchy)
      (sortCanonicalKeys? keys) (sortCanonicalKeys? keys') := by
  induction equivalent with
  | nil => exact Option.Rel.some List.Forall₂.nil
  | cons keyEquivalent tailEquivalent inductionHypothesis =>
      unfold sortCanonicalKeys?
      exact optionRel_bind (insertCanonicalKey? _) (insertCanonicalKey? _)
        (fun sortedEquivalent =>
          insertCanonicalKey?_congr keyEquivalent sortedEquivalent)
        inductionHypothesis

private theorem map_constitutionalProjection_eq {keys keys' : List CanonicalBranchKey}
    (equivalent : List.Forall₂ SameConstitutionalHierarchy keys keys') :
    keys.map constitutionalProjection = keys'.map constitutionalProjection := by
  induction equivalent with
  | nil => rfl
  | cons headEquivalent tailEquivalent inductionHypothesis =>
      simp only [List.map_cons, inductionHypothesis, List.cons.injEq, and_true]
      exact (sameConstitutionalHierarchy_iff_projection_eq _ _).mp headEquivalent

private theorem mergeCanonicalAtomicChildren_projection
    (children : List CanonicalBranchKey) :
    mergeCanonicalAtomicChildren (children.map constitutionalProjection) =
      mergeCanonicalAtomicChildren children := by
  simp [mergeCanonicalAtomicChildren, canonicalChildLayerCount,
    constitutionalProjection, List.foldl_map, List.zipIdx_map,
    List.flatMap_map]

private theorem mergeCanonicalNatChildren_projection
    (layers : CanonicalBranchKey → List (List CanonicalNatEntry))
    (projectionLayers : ∀ key, layers (constitutionalProjection key) = layers key)
    (children : List CanonicalBranchKey) :
    mergeCanonicalNatChildren layers (children.map constitutionalProjection) =
      mergeCanonicalNatChildren layers children := by
  have projectionLayers' : ∀ key : CanonicalBranchKey,
      layers
        { rule1a := key.rule1a
          rule1b := key.rule1b
          rule2 := key.rule2
          realAtoms := []
          sourceNodes := []
          sourceOccurrences := []
          sourceTree? := none
          complete := key.complete } = layers key := by
    intro key
    simpa [constitutionalProjection] using projectionLayers key
  simp [mergeCanonicalNatChildren, canonicalChildLayerCount,
    constitutionalProjection, projectionLayers', List.foldl_map, List.zipIdx_map,
    List.flatMap_map]

theorem mergeCanonicalAtomicChildren_congr {children children' : List CanonicalBranchKey}
    (equivalent : List.Forall₂ SameConstitutionalHierarchy children children') :
    mergeCanonicalAtomicChildren children = mergeCanonicalAtomicChildren children' := by
  rw [← mergeCanonicalAtomicChildren_projection children,
    ← mergeCanonicalAtomicChildren_projection children',
    map_constitutionalProjection_eq equivalent]

theorem mergeCanonicalNatChildren_congr
    (layers : CanonicalBranchKey → List (List CanonicalNatEntry))
    (projectionLayers : ∀ key, layers (constitutionalProjection key) = layers key)
    {children children' : List CanonicalBranchKey}
    (equivalent : List.Forall₂ SameConstitutionalHierarchy children children') :
    mergeCanonicalNatChildren layers children = mergeCanonicalNatChildren layers children' := by
  rw [← mergeCanonicalNatChildren_projection layers projectionLayers children,
    ← mergeCanonicalNatChildren_projection layers projectionLayers children',
    map_constitutionalProjection_eq equivalent]

/-- A root key is atom-name invariant whenever its Rule-1a label is.  Rule 1b, isotope mass,
terminality, and all sparse positions are discharged here from the graph transport theorems. -/
theorem canonicalRootKey_relabel (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (node : CanonicalBranchNode)
    (complete : Bool)
    (labelNatural :
      (relabelRawMolecule mol permutation).canonicalRule1aLabel?
          (relabelCanonicalNode mol permutation node) =
        mol.canonicalRule1aLabel? node) :
    SameConstitutionalHierarchy
      ((relabelRawMolecule mol permutation).canonicalRootKey
        (relabelCanonicalNode mol permutation node) complete)
      (mol.canonicalRootKey node complete) := by
  constructor
  · simp [RawMolecule.canonicalRootKey, RawMolecule.canonicalRule1aLabel,
      labelNatural]
  · simp [RawMolecule.canonicalRootKey, CanonicalBranchNode.rule1bCode,
      relabelCanonicalNode_rule1bRootDistance]
  · cases provenance : node.provenance <;>
      simp [RawMolecule.canonicalRootKey, relabelCanonicalNode, provenance,
        relabelRawMolecule_atomMassAt_all]
  · rfl

/-- Ordinary, ring-duplicate, and phantom Rule-1a labels are immediately natural.  The remaining
multiple-bond case is precisely the separately auditable mancude/Kekulé normalization boundary. -/
theorem canonicalRule1aLabel?_relabel_of_not_multipleBondDuplicate
    (mol : RawMolecule) (permutation : Equiv.Perm (Fin mol.atomCount))
    (node : CanonicalBranchNode)
    (notMultiple : ∀ distance,
      node.provenance ≠ CanonicalNodeProvenance.multipleBondDuplicate distance) :
    (relabelRawMolecule mol permutation).canonicalRule1aLabel?
        (relabelCanonicalNode mol permutation node) =
      mol.canonicalRule1aLabel? node := by
  cases provenance : node.provenance with
  | multipleBondDuplicate distance => exact (notMultiple distance provenance).elim
  | phantom distance => simp [RawMolecule.canonicalRule1aLabel?, relabelCanonicalNode, provenance]
  | ringDuplicate distance =>
      simp [RawMolecule.canonicalRule1aLabel?, relabelCanonicalNode, provenance,
        relabelRawMolecule_atomZAt_all]
  | realAtom =>
      simp [RawMolecule.canonicalRule1aLabel?, relabelCanonicalNode, provenance,
        relabelRawMolecule_atomZAt_all]

private theorem buildCanonicalChildKeys_congr
    {buildLeft buildRight : ℕ → CanonicalBranchNode → Option CanonicalBranchKey}
    (transportNode : CanonicalBranchNode → CanonicalBranchNode)
    (buildNatural : ∀ remaining node,
      Option.Rel SameConstitutionalHierarchy
        (buildLeft remaining (transportNode node)) (buildRight remaining node)) :
    ∀ (remaining : ℕ) (nodes : List CanonicalBranchNode),
      Option.Rel (List.Forall₂ SameConstitutionalHierarchy)
        (buildCanonicalChildKeys buildLeft remaining (nodes.map transportNode))
        (buildCanonicalChildKeys buildRight remaining nodes) := by
  intro remaining nodes
  induction nodes generalizing remaining with
  | nil => exact Option.Rel.some List.Forall₂.nil
  | cons node nodes inductionHypothesis =>
      simp only [List.map_cons]
      unfold buildCanonicalChildKeys
      exact optionRel_bind (targetRelation := List.Forall₂ SameConstitutionalHierarchy)
        (fun leftKey =>
          if remaining < leftKey.nodeCount then none
          else
            (buildCanonicalChildKeys buildLeft (remaining - leftKey.nodeCount)
              (nodes.map transportNode)).bind fun keys => some (leftKey :: keys))
        (fun rightKey =>
          if remaining < rightKey.nodeCount then none
          else
            (buildCanonicalChildKeys buildRight (remaining - rightKey.nodeCount) nodes).bind
              fun keys => some (rightKey :: keys))
        (fun keyEquivalent => by
          dsimp
          rw [keyEquivalent.nodeCount_eq]
          split
          · exact Option.Rel.none
          · exact optionRel_bind (fun keys => some (_ :: keys))
              (fun keys => some (_ :: keys))
              (fun tailEquivalent =>
                Option.Rel.some (List.Forall₂.cons keyEquivalent tailEquivalent))
              (inductionHypothesis _))
        (buildNatural remaining node)

private theorem all_complete_eq {keys keys' : List CanonicalBranchKey}
    (equivalent : List.Forall₂ SameConstitutionalHierarchy keys keys') :
    (keys.all fun key => key.complete) = (keys'.all fun key => key.complete) := by
  induction equivalent with
  | nil => rfl
  | cons headEquivalent tailEquivalent inductionHypothesis =>
      simp [headEquivalent.complete, inductionHypothesis]

private theorem assembleCanonicalBranchKey_congr
    {root root' : CanonicalBranchKey} {children children' : List CanonicalBranchKey}
    (rootEquivalent : SameConstitutionalHierarchy root root')
    (childrenEquivalent : List.Forall₂ SameConstitutionalHierarchy children children') :
    SameConstitutionalHierarchy
      (assembleCanonicalBranchKey root children)
      (assembleCanonicalBranchKey root' children') := by
  constructor
  · simp [assembleCanonicalBranchKey, rootEquivalent.rule1a,
      mergeCanonicalAtomicChildren_congr childrenEquivalent]
  · simp [assembleCanonicalBranchKey, rootEquivalent.rule1b,
      mergeCanonicalNatChildren_congr (fun key => key.rule1b)
        (by intro key; rfl) childrenEquivalent]
  · simp [assembleCanonicalBranchKey, rootEquivalent.rule2,
      mergeCanonicalNatChildren_congr (fun key => key.rule2)
        (by intro key; rfl) childrenEquivalent]
  · exact rootEquivalent.complete

private theorem finishCanonicalBranchKey_relabel (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (node : CanonicalBranchNode)
    (labelNatural :
      (relabelRawMolecule mol permutation).canonicalRule1aLabel?
          (relabelCanonicalNode mol permutation node) = mol.canonicalRule1aLabel? node)
    (cap : ℕ) {left right : List CanonicalBranchKey}
    (sortedEquivalent : List.Forall₂ SameConstitutionalHierarchy left right) :
    Option.Rel SameConstitutionalHierarchy
      (let root := (relabelRawMolecule mol permutation).canonicalRootKey
          (relabelCanonicalNode mol permutation node)
          (left.all fun child => child.complete)
       let key := assembleCanonicalBranchKey root left
       if cap < key.nodeCount then none else some key)
      (let root := mol.canonicalRootKey node (right.all fun child => child.complete)
       let key := assembleCanonicalBranchKey root right
       if cap < key.nodeCount then none else some key) := by
  dsimp
  rw [all_complete_eq sortedEquivalent]
  let rootEquivalent := canonicalRootKey_relabel mol permutation node
    (right.all fun child => child.complete) labelNatural
  let keyEquivalent := assembleCanonicalBranchKey_congr rootEquivalent sortedEquivalent
  rw [keyEquivalent.nodeCount_eq]
  split
  · exact Option.Rel.none
  · exact Option.Rel.some keyEquivalent

/-- Main rooted-digraph naturality theorem.

For a relabeling of the constitutionally labeled graph, the production compiler has identical
success/refusal behavior and produces the same complete rule-major hierarchy.  The statement is
uniform in both fuel and the exact node cap; no bound is increased.  Atom-index witness fields may
be renamed and tied siblings may exchange bookkeeping order, but every comparator-visible field is
identical. -/
theorem buildCanonicalBranchKey_relabel_of_rule1aNatural (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount))
    (labelNatural : ∀ node : CanonicalBranchNode,
      (relabelRawMolecule mol permutation).canonicalRule1aLabel?
          (relabelCanonicalNode mol permutation node) =
        mol.canonicalRule1aLabel? node) :
    ∀ (fuel cap : ℕ) (node : CanonicalBranchNode),
      Option.Rel SameConstitutionalHierarchy
        ((relabelRawMolecule mol permutation).buildCanonicalBranchKey cap fuel
          (relabelCanonicalNode mol permutation node))
        (mol.buildCanonicalBranchKey cap fuel node) := by
  intro fuel
  induction fuel with
  | zero =>
      intro cap node
      unfold RawMolecule.buildCanonicalBranchKey
      rw [labelNatural node, relabelRawMolecule_canonicalTerminal]
      cases label : mol.canonicalRule1aLabel? node with
      | none => exact Option.Rel.none
      | some value =>
          exact Option.Rel.some
            (canonicalRootKey_relabel mol permutation node _ (labelNatural node))
  | succ fuel inductionHypothesis =>
      intro cap node
      unfold RawMolecule.buildCanonicalBranchKey
      rw [labelNatural node, relabelRawMolecule_canonicalTerminal]
      cases label : mol.canonicalRule1aLabel? node with
      | none => exact Option.Rel.none
      | some value =>
          by_cases terminal : mol.canonicalTerminal node = true
          · simp only [terminal, ↓reduceIte]
            exact Option.Rel.some
              (canonicalRootKey_relabel mol permutation node true (labelNatural node))
          · have terminalFalse : mol.canonicalTerminal node = false := by
              exact Bool.eq_false_of_not_eq_true terminal
            simp only [terminalFalse, Bool.false_eq]
            rw [relabelRawMolecule_canonicalChildren, List.length_map]
            by_cases tooMany : 3 < (mol.canonicalChildren node).length
            · simp [tooMany]
            · simp only [tooMany, ↓reduceIte]
              have childBuilds := buildCanonicalChildKeys_congr
                (relabelCanonicalNode mol permutation)
                (fun remaining child => inductionHypothesis remaining child)
                (cap - 1) (mol.canonicalChildren node)
              exact optionRel_bind
                (fun childKeys => do
                  let sorted ← sortCanonicalKeys? childKeys
                  let root := (relabelRawMolecule mol permutation).canonicalRootKey
                    (relabelCanonicalNode mol permutation node)
                    (sorted.all fun child => child.complete)
                  let key := assembleCanonicalBranchKey root sorted
                  if cap < key.nodeCount then none else some key)
                (fun childKeys => do
                  let sorted ← sortCanonicalKeys? childKeys
                  let root := mol.canonicalRootKey node
                    (sorted.all fun child => child.complete)
                  let key := assembleCanonicalBranchKey root sorted
                  if cap < key.nodeCount then none else some key)
                (fun childKeysEquivalent =>
                  optionRel_bind
                    (fun sorted =>
                      let root := (relabelRawMolecule mol permutation).canonicalRootKey
                        (relabelCanonicalNode mol permutation node)
                        (sorted.all fun child => child.complete)
                      let key := assembleCanonicalBranchKey root sorted
                      if cap < key.nodeCount then none else some key)
                    (fun sorted =>
                      let root := mol.canonicalRootKey node
                        (sorted.all fun child => child.complete)
                      let key := assembleCanonicalBranchKey root sorted
                      if cap < key.nodeCount then none else some key)
                    (fun sortedEquivalent =>
                      finishCanonicalBranchKey_relabel mol permutation node
                        (labelNatural node) cap sortedEquivalent)
                    (sortCanonicalKeys?_congr childKeysEquivalent))
                childBuilds

/-- Unconditional rooted-digraph naturality under every finite atom relabeling.  The Rule-1a
premise of the structural induction is discharged by the graph-invariance theorem for the complete
bounded mancude/Kekulé construction. -/
theorem buildCanonicalBranchKey_relabel (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) :
    ∀ (fuel cap : ℕ) (node : CanonicalBranchNode),
      Option.Rel SameConstitutionalHierarchy
        ((relabelRawMolecule mol permutation).buildCanonicalBranchKey cap fuel
          (relabelCanonicalNode mol permutation node))
        (mol.buildCanonicalBranchKey cap fuel node) :=
  buildCanonicalBranchKey_relabel_of_rule1aNatural mol permutation
    (relabelRawMolecule_canonicalRule1aLabel? mol permutation)

/-- Comparator equality follows from equality of all comparator-visible hierarchy fields. -/
theorem SameConstitutionalHierarchy.compare_eq {left right : CanonicalBranchKey}
    (equivalent : SameConstitutionalHierarchy left right) :
    compareCanonicalBranchKeys left right = .eq := by
  calc
    compareCanonicalBranchKeys left right = compareCanonicalBranchKeys right right :=
      compareCanonicalBranchKeys_congr equivalent (SameConstitutionalHierarchy.refl right)
    _ = .eq := compareCanonicalBranchKeys_refl right

/-- Therefore representation-equivalent compiled keys define literally the same quotient
hierarchy signature. -/
theorem SameConstitutionalHierarchy.signature_eq {left right : CanonicalBranchKey}
    (equivalent : SameConstitutionalHierarchy left right) :
    constitutionalHierarchySignature left = constitutionalHierarchySignature right := by
  exact (constitutionalHierarchySignature_eq_iff left right).2 equivalent.compare_eq

/-- Headline boundary theorem: rooted-digraph compilation produces the same hierarchy signature
under every finite atom relabeling, at every fuel and cap, including identical refusal behavior. -/
theorem canonicalHierarchySignature_relabel (mol : RawMolecule)
    (permutation : Equiv.Perm (Fin mol.atomCount)) (fuel cap : ℕ)
    (node : CanonicalBranchNode) :
    ((relabelRawMolecule mol permutation).buildCanonicalBranchKey cap fuel
        (relabelCanonicalNode mol permutation node)).map
          constitutionalHierarchySignature =
      (mol.buildCanonicalBranchKey cap fuel node).map constitutionalHierarchySignature := by
  have natural := buildCanonicalBranchKey_relabel mol permutation fuel cap node
  exact option_eq_of_rel_eq <| optionRel_map constitutionalHierarchySignature
    constitutionalHierarchySignature
    (fun equivalent => equivalent.signature_eq) natural

/-- Swapping or otherwise permuting tied child representations leaves the input projection list
unchanged and hence produces pointwise equivalent sorted keys. -/
theorem sortCanonicalKeys?_tiedNodePermutation {keys keys' : List CanonicalBranchKey}
    (tiedPermutation :
      keys.map constitutionalProjection = keys'.map constitutionalProjection) :
    Option.Rel (List.Forall₂ SameConstitutionalHierarchy)
      (sortCanonicalKeys? keys) (sortCanonicalKeys? keys') := by
  have pointwise : List.Forall₂ SameConstitutionalHierarchy keys keys' := by
    induction keys generalizing keys' with
    | nil => simpa using tiedPermutation
    | cons key keys inductionHypothesis =>
        cases keys' with
        | nil => simp at tiedPermutation
        | cons key' keys' =>
            simp only [List.map_cons, List.cons.injEq] at tiedPermutation
            exact List.Forall₂.cons
              ((sameConstitutionalHierarchy_iff_projection_eq key key').2
                tiedPermutation.1)
              (inductionHypothesis tiedPermutation.2)
  exact sortCanonicalKeys?_congr pointwise


private def atomicLayer : List (List CanonicalAtomicEntry) :=
  [[([0], carbonLabel), ([1], carbonLabel)]]

private def keyOf (distances masses : List ℕ) : CanonicalBranchKey :=
  { rule1a := atomicLayer
    rule1b := [[([0], distances.getD 0 0), ([1], distances.getD 1 0)]]
    rule2 := [[([0], masses.getD 0 0), ([1], masses.getD 1 0)]]
    realAtoms := []
    sourceNodes := []
    complete := true }

private def cycleA : CanonicalBranchKey := keyOf [0, 3] [12011000, 0]
private def cycleB : CanonicalBranchKey := keyOf [2, 0] [0, 12011000]
private def cycleC : CanonicalBranchKey := keyOf [2, 2] [0, 0]

/-- The former minimal Rule-1b cycle is an ordinary strict chain once every node receives its
revised root distance. -/
theorem former_compiled_key_cycle_is_transitive :
    compareCanonicalBranchKeys cycleA cycleB = .gt ∧
      compareCanonicalBranchKeys cycleB cycleC = .gt ∧
      compareCanonicalBranchKeys cycleA cycleC = .gt := by
  decide

end TetraStereo.Examples.CanonicalBranchNaturality
