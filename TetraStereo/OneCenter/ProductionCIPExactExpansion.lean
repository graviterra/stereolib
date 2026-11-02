import TetraStereo.OneCenter.ProductionCIPHierarchy

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

namespace List.Perm

def finConsCongr {n m : ℕ} (equivalence : Fin n ≃ Fin m) :
    Fin (n + 1) ≃ Fin (m + 1) :=
  (finSuccEquiv n).trans
    ((Equiv.optionCongr equivalence).trans (finSuccEquiv m).symm)

@[simp] theorem finConsCongr_zero {n m : ℕ} (equivalence : Fin n ≃ Fin m) :
    finConsCongr equivalence 0 = 0 := by
  simp [finConsCongr]

@[simp] theorem finConsCongr_succ {n m : ℕ} (equivalence : Fin n ≃ Fin m)
    (index : Fin n) :
    finConsCongr equivalence index.succ = (equivalence index).succ := by
  simp [finConsCongr]

/-- A list permutation induces an occurrence-preserving index equivalence, even when values are
equal. -/
theorem exists_finEquiv_get {alpha : Type*} {left right : List alpha}
    (permutation : left.Perm right) :
    ∃ equivalence : Fin left.length ≃ Fin right.length,
      ∀ index, left.get index = right.get (equivalence index) := by
  induction permutation with
  | nil => exact ⟨Equiv.refl _, fun index => Fin.elim0 index⟩
  | @cons value left right permutation inductionHypothesis =>
      obtain ⟨equivalence, hequivalence⟩ := inductionHypothesis
      refine ⟨finConsCongr equivalence, ?_⟩
      intro index
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · simp
      · simpa using hequivalence tailIndex
  | @swap first second tail =>
      let equivalence : Fin (first :: second :: tail).length ≃
          Fin (second :: first :: tail).length :=
        Equiv.swap (0 : Fin (tail.length + 2)) 1
      refine ⟨equivalence, ?_⟩
      intro index
      refine Fin.cases ?_ (fun index => ?_) index
      · simp [equivalence]
      · refine Fin.cases ?_ (fun tailIndex => ?_) index
        · simp [equivalence]
        · have hne : tailIndex.succ.succ ≠ (1 : Fin (tail.length + 2)) := by
            intro heq
            have := congrArg Fin.val heq
            simp at this
          simp [equivalence, Equiv.swap_apply_def, hne]
  | @trans left middle right first second firstIH secondIH =>
      obtain ⟨firstEquivalence, hfirst⟩ := firstIH
      obtain ⟨secondEquivalence, hsecond⟩ := secondIH
      exact ⟨firstEquivalence.trans secondEquivalence,
        fun index => (hfirst index).trans (hsecond (firstEquivalence index))⟩

end List.Perm

theorem card_fin_subtype_eq_countP {alpha : Type*}
    (values : List alpha) (predicate : alpha → Prop) [DecidablePred predicate] :
    Nat.card {index : Fin values.length // predicate (values.get index)} =
      values.countP fun value => decide (predicate value) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  induction values with
  | nil => simp
  | cons value values inductionHypothesis =>
      change (Finset.univ.filter fun index : Fin (values.length + 1) =>
        predicate ((value :: values).get index)).card = _
      rw [Fin.card_filter_univ_succ']
      simp only [List.countP_cons]
      have hzero : (value :: values).get (0 : Fin (values.length + 1)) = value := rfl
      have hsucc (index : Fin values.length) :
          (value :: values).get index.succ = values.get index := rfl
      simp only [hzero, hsucc]
      rw [inductionHypothesis]
      by_cases hpredicate : predicate value <;> simp [hpredicate, Nat.add_comm]

theorem card_inter_equiv_countP {alpha beta : Type*} [Finite beta]
    (values : List alpha) (restricted predicate : beta → Prop)
    (valuePredicate : alpha → Prop)
    [DecidablePred restricted] [DecidablePred predicate] [DecidablePred valuePredicate]
    (equivalence : {value : beta // restricted value} ≃ Fin values.length)
    (hpredicate : ∀ value : {value : beta // restricted value},
      predicate value.1 ↔ valuePredicate (values.get (equivalence value))) :
    Nat.card {value : beta // restricted value ∧ predicate value} =
      values.countP fun value => decide (valuePredicate value) := by
  rw [← Nat.card_congr
    (Equiv.subtypeSubtypeEquivSubtypeInter restricted predicate)]
  rw [Nat.card_congr (equivalence.subtypeEquiv
    (q := fun index => valuePredicate (values.get index)) hpredicate)]
  exact card_fin_subtype_eq_countP values valuePredicate

/-!
# Constitutional realization of production CIP hierarchies

This module states the chemical graph seen by the production hierarchy compiler and begins the
exact-expansion bridge.  The only bond normalization is the documented P/S oxido convention on
the suppressed root edge.  It is represented in the molecular graph itself rather than hidden in
an executable child-builder exception.
-/

namespace RawMolecule

/-- Whether an unordered atom pair is the distinguished center--ligand root edge. -/
def IsRootPair (center ligand left right : ℕ) : Prop :=
  (left = center ∧ right = ligand) ∨ (left = ligand ∧ right = center)

instance (center ligand left right : ℕ) : Decidable (IsRootPair center ligand left right) :=
  by
    unfold IsRootPair
    infer_instance

theorem isRootPair_symm (center ligand left right : ℕ) :
    IsRootPair center ligand left right ↔ IsRootPair center ligand right left := by
  unfold IsRootPair
  aesop

/-- Bond order used by the constitutional semantics for one production ligand hierarchy.

The raw parser graph is retained everywhere except the distinguished P/S oxido root edge, where
the production convention treats a written double bond as one coordination-sphere edge.  The
diagonal is explicitly zero, so this remains a lawful `MoleculeGraph` even for arbitrary indices. -/
def canonicalHierarchyBond (mol : RawMolecule) (center ligand left right : ℕ) : ℕ :=
  if left = right then 0
  else if IsRootPair center ligand left right &&
      mol.isTrigonalPyramidalOxidoRootEdge center ligand then 1
  else mol.bondOrder left right

theorem canonicalHierarchyBond_symm (mol : RawMolecule) (center ligand left right : ℕ) :
    mol.canonicalHierarchyBond center ligand left right =
      mol.canonicalHierarchyBond center ligand right left := by
  unfold canonicalHierarchyBond
  rw [mol.bondOrder_symm left right]
  by_cases heq : left = right
  · subst right
    simp
  · have hne : right ≠ left := fun h => heq h.symm
    simp only [heq, hne, ↓reduceIte]
    by_cases hpair : IsRootPair center ligand left right
    · have hpair' : IsRootPair center ligand right left :=
        (isRootPair_symm center ligand left right).1 hpair
      simp [hpair, hpair']
    · have hpair' : ¬IsRootPair center ligand right left := by
        intro h
        exact hpair ((isRootPair_symm center ligand left right).2 h)
      simp [hpair, hpair']

@[simp] theorem canonicalHierarchyBond_self (mol : RawMolecule)
    (center ligand atom : ℕ) :
    mol.canonicalHierarchyBond center ligand atom atom = 0 := by
  simp [canonicalHierarchyBond]

/-- Proof-facing molecule graph matching the production root-edge convention exactly. -/
def canonicalHierarchyMoleculeGraph (mol : RawMolecule)
    (center ligand : Fin mol.atomCount) : MoleculeGraph (Fin mol.atomCount) where
  atomZ := fun atom => (mol.atoms.get atom).element.atomicNumber
  atomMass := fun atom => mol.atomMassAt atom
  formalCharge := fun atom => (mol.atoms.get atom).charge
  bond := fun left right => mol.canonicalHierarchyBond center ligand left right
  bond_symm := by
    intro left right
    exact mol.canonicalHierarchyBond_symm center ligand left right
  bond_self := by
    intro atom
    exact mol.canonicalHierarchyBond_self center ligand atom

@[simp] theorem canonicalHierarchyMoleculeGraph_atomZ (mol : RawMolecule)
    (center ligand atom : Fin mol.atomCount) :
    (mol.canonicalHierarchyMoleculeGraph center ligand).atomZ atom =
      mol.toMoleculeGraph.atomZ atom :=
  rfl

@[simp] theorem canonicalHierarchyMoleculeGraph_atomMass (mol : RawMolecule)
    (center ligand atom : Fin mol.atomCount) :
    (mol.canonicalHierarchyMoleculeGraph center ligand).atomMass atom =
      mol.toMoleculeGraph.atomMass atom :=
  rfl

@[simp] theorem canonicalHierarchyMoleculeGraph_formalCharge (mol : RawMolecule)
    (center ligand atom : Fin mol.atomCount) :
    (mol.canonicalHierarchyMoleculeGraph center ligand).formalCharge atom =
      mol.toMoleculeGraph.formalCharge atom :=
  rfl

@[simp] theorem canonicalHierarchyMoleculeGraph_bond (mol : RawMolecule)
    (center ligand left right : Fin mol.atomCount) :
    (mol.canonicalHierarchyMoleculeGraph center ligand).bond left right =
      mol.canonicalHierarchyBond center ligand left right :=
  rfl

theorem canonicalHierarchyBond_eq_bondOrder_of_not_rootPair (mol : RawMolecule)
    (center ligand left right : ℕ) (hpair : ¬IsRootPair center ligand left right) :
    mol.canonicalHierarchyBond center ligand left right = mol.bondOrder left right := by
  by_cases heq : left = right
  · subst right
    simp [canonicalHierarchyBond, mol.bondOrder_self]
  · simp [canonicalHierarchyBond, heq, hpair]

theorem canonicalHierarchyBond_eq_bondOrder_of_not_oxido (mol : RawMolecule)
    (center ligand left right : ℕ)
    (hoxido : mol.isTrigonalPyramidalOxidoRootEdge center ligand = false) :
    mol.canonicalHierarchyBond center ligand left right = mol.bondOrder left right := by
  by_cases heq : left = right
  · subst right
    simp [canonicalHierarchyBond, mol.bondOrder_self]
  · simp [canonicalHierarchyBond, heq, hoxido]

theorem canonicalHierarchyMoleculeGraph_bond_eq_toMoleculeGraph_of_not_oxido
    (mol : RawMolecule) (center ligand left right : Fin mol.atomCount)
    (hoxido : mol.isTrigonalPyramidalOxidoRootEdge center ligand = false) :
    (mol.canonicalHierarchyMoleculeGraph center ligand).bond left right =
      mol.toMoleculeGraph.bond left right := by
  exact mol.canonicalHierarchyBond_eq_bondOrder_of_not_oxido
    center ligand left right hoxido

/-! ## Child-construction facts -/

theorem mem_of_mem_eraseCanonicalParentCopy (parent : ℕ)
    (copy : ℕ × ℕ) (copies : List (ℕ × ℕ)) :
    copy ∈ eraseCanonicalParentCopy parent copies → copy ∈ copies := by
  induction copies with
  | nil => simp [eraseCanonicalParentCopy]
  | cons head tail inductionHypothesis =>
      by_cases herase : head.1 == parent && head.2 == 0
      · simp [eraseCanonicalParentCopy, herase]
        exact fun h => Or.inr h
      · simp [eraseCanonicalParentCopy, herase]
        intro h
        rcases h with rfl | htail
        · exact Or.inl rfl
        · exact Or.inr (inductionHypothesis htail)

theorem eraseCanonicalParentCopy_eq_erase (parent : ℕ)
    (copies : List (ℕ × ℕ)) :
    eraseCanonicalParentCopy parent copies = copies.erase (parent, 0) := by
  induction copies with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      by_cases heq : head = (parent, 0)
      · subst head
        simp [eraseCanonicalParentCopy]
      · have hcomponents : ¬(head.1 = parent ∧ head.2 = 0) := by
          intro h
          exact heq (Prod.ext h.1 h.2)
        simp only [eraseCanonicalParentCopy]
        simp [hcomponents, heq, inductionHypothesis]

theorem countP_eraseCanonicalParentCopy (parent : ℕ)
    (copies : List (ℕ × ℕ)) (predicate : (ℕ × ℕ) → Bool) :
    (eraseCanonicalParentCopy parent copies).countP predicate =
      copies.countP predicate -
        if (parent, 0) ∈ copies ∧ predicate (parent, 0) then 1 else 0 := by
  rw [eraseCanonicalParentCopy_eq_erase, List.countP_erase]

theorem countP_rangeMap_atom (count next atom : ℕ) :
    ((List.range count).map fun index => (next, index)).countP
        (fun copy => copy.1 == atom) =
      if next = atom then count else 0 := by
  rw [List.countP_map]
  by_cases heq : next = atom <;> simp [Function.comp_def, heq]

theorem countP_range_ne_zero (count : ℕ) :
    (List.range count).countP (fun index => index != 0) = count - 1 := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      cases count with
      | zero => decide
      | succ count =>
          rw [List.range_succ, List.countP_append, inductionHypothesis]
          simp

theorem countP_rangeMap_atom_nonzero (count next atom : ℕ) :
    ((List.range count).map fun index => (next, index)).countP
        (fun copy => copy.1 == atom && copy.2 != 0) =
      if next = atom then count - 1 else 0 := by
  by_cases heq : next = atom
  · subst next
    rw [List.countP_map]
    simpa [Function.comp_def] using countP_range_ne_zero count
  · simp [heq]

theorem firstNatIndex?_eq_some_imp_getElem?
    (target : ℕ) : ∀ (values : List ℕ) (index : ℕ),
    firstNatIndex? target values = some index → values[index]? = some target
  | [], index, hindex => by simp [firstNatIndex?] at hindex
  | value :: values, index, hindex => by
      unfold firstNatIndex? at hindex
      by_cases heq : value = target
      · simp [heq] at hindex
        subst index
        simp [heq]
      · simp only [heq, ↓reduceIte, Option.map_eq_some_iff] at hindex
        obtain ⟨tailIndex, htailIndex, rfl⟩ := hindex
        simpa using firstNatIndex?_eq_some_imp_getElem? target values tailIndex htailIndex

theorem firstNatIndex?_eq_some_imp_lt_length
    (target : ℕ) (values : List ℕ) (index : ℕ)
    (hindex : firstNatIndex? target values = some index) :
    index < values.length := by
  have hget := firstNatIndex?_eq_some_imp_getElem? target values index hindex
  by_contra hnot
  have hle : values.length ≤ index := by omega
  rw [List.getElem?_eq_none hle] at hget
  simp at hget

/-- Every emitted child copy comes from a concrete raw bond record and lies in the copy-index
range selected for that bond. -/
theorem canonicalChildCopies_source
    (mol : RawMolecule) (node : CanonicalBranchNode) (copy : ℕ × ℕ)
    (hcopy : copy ∈ mol.canonicalChildCopies node) :
    ∃ bond ∈ mol.bonds,
      ((bond.source = node.atom ∧ bond.target = copy.1) ∨
        (bond.target = node.atom ∧ bond.source = copy.1)) ∧
      copy.2 < mol.canonicalBondOrder node copy.1 := by
  unfold canonicalChildCopies at hcopy
  have hseed := mem_of_mem_eraseCanonicalParentCopy node.parent copy _ hcopy
  rw [List.mem_flatMap] at hseed
  rcases hseed with ⟨bond, hbond, hcopy⟩
  by_cases hsource : bond.source == node.atom
  · have hsourceEq : bond.source = node.atom := by simpa using hsource
    simp [hsource] at hcopy
    rcases hcopy with ⟨copyIndex, hindex, hcopyEq⟩
    have hindexLt : copyIndex < mol.canonicalBondOrder node bond.target := by
      simpa using hindex
    cases hcopyEq
    exact ⟨bond, hbond, Or.inl ⟨hsourceEq, rfl⟩, hindexLt⟩
  · by_cases htarget : bond.target == node.atom
    · have htargetEq : bond.target = node.atom := by simpa using htarget
      simp [hsource, htarget] at hcopy
      rcases hcopy with ⟨copyIndex, hindex, hcopyEq⟩
      have hindexLt : copyIndex < mol.canonicalBondOrder node bond.source := by
        simpa using hindex
      cases hcopyEq
      exact ⟨bond, hbond, Or.inr ⟨htargetEq, rfl⟩, hindexLt⟩
    · simp [hsource, htarget] at hcopy

theorem canonicalBondOrder_pos_imp_bondOrder_pos
    (mol : RawMolecule) (node : CanonicalBranchNode) (next : ℕ)
    (hhead : node.history.head? = some node.atom)
    (hpositive : 0 < mol.canonicalBondOrder node next) :
    0 < mol.bondOrder node.atom next := by
  unfold canonicalBondOrder at hpositive
  cases hhistory : node.history with
  | nil => simp [hhistory] at hhead
  | cons current history =>
      cases history with
      | nil => simpa [hhistory] using hpositive
      | cons center rest =>
          cases rest with
          | nil =>
              by_cases hnext : next == center &&
                  mol.isTrigonalPyramidalOxidoRootEdge center current
              · simp [hhistory, hnext] at hpositive
                simp only [Bool.and_eq_true] at hnext
                have hnextEq : next = center := by
                  exact beq_iff_eq.mp hnext.1
                have hoxido := hnext.2
                have hatom : node.atom = current := by
                  simpa [hhistory] using hhead.symm
                unfold isTrigonalPyramidalOxidoRootEdge at hoxido
                split at hoxido <;> simp_all [mol.bondOrder_symm]
              · simpa [hhistory, hnext] using hpositive
          | cons another rest => simpa [hhistory] using hpositive

/-- A production child is always an in-range atom joined to its parent source by a positive bond
in the root-normalized constitutional molecule graph. -/
theorem canonicalChildren_atom_valid_and_adjacent
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (parent child : CanonicalBranchNode)
    (hparentHead : parent.history.head? = some parent.atom)
    (hchild : child ∈ mol.canonicalChildren parent) :
    child.atom < mol.atomCount ∧
      0 < mol.canonicalHierarchyBond center ligand parent.atom child.atom := by
  unfold canonicalChildren at hchild
  by_cases hleaf : parent.forcedLeaf
  · simp [hleaf] at hchild
  · simp only [hleaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hchild
    rcases hchild with ⟨copy, hcopy, hchildEq⟩
    rcases mol.canonicalChildCopies_source parent copy hcopy with
      ⟨bond, hbond, hendpoints, hcopyIndex⟩
    have hok := hwellFormed bond hbond
    have hcopyAtom : copy.1 < mol.atomCount := by
      rcases hendpoints with hendpoints | hendpoints
      · simpa [hendpoints.2] using hok.2.1
      · simpa [hendpoints.2] using hok.1
    have hrawPositive : 0 < mol.bondOrder parent.atom copy.1 :=
      mol.canonicalBondOrder_pos_imp_bondOrder_pos parent copy.1
        hparentHead (Nat.zero_lt_of_lt hcopyIndex)
    have hnormalizedPositive :
        0 < mol.canonicalHierarchyBond center ligand parent.atom copy.1 := by
      unfold canonicalHierarchyBond
      have hne : parent.atom ≠ copy.1 := by
        rcases hendpoints with hendpoints | hendpoints
        · intro heq
          exact hok.2.2 (hendpoints.1.trans (heq.trans hendpoints.2.symm))
        · intro heq
          exact hok.2.2 (hendpoints.2.trans (heq.symm.trans hendpoints.1.symm))
      simp only [hne, ↓reduceIte]
      split
      · omega
      · exact hrawPositive
    subst child
    exact ⟨hcopyAtom, hnormalizedPositive⟩

theorem canonicalChildren_history_head
    (mol : RawMolecule) (parent child : CanonicalBranchNode)
    (hchild : child ∈ mol.canonicalChildren parent) :
    child.history.head? = some child.atom := by
  unfold canonicalChildren at hchild
  by_cases hleaf : parent.forcedLeaf
  · simp [hleaf] at hchild
  · simp only [hleaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hchild
    rcases hchild with ⟨copy, _, rfl⟩
    rfl

theorem canonicalChildren_history
    (mol : RawMolecule) (parent child : CanonicalBranchNode)
    (hchild : child ∈ mol.canonicalChildren parent) :
    child.history = child.atom :: parent.history := by
  unfold canonicalChildren at hchild
  by_cases hleaf : parent.forcedLeaf
  · simp [hleaf] at hchild
  · simp only [hleaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hchild
    obtain ⟨copy, hcopy, rfl⟩ := hchild
    rfl

theorem canonicalChildren_depth
    (mol : RawMolecule) (parent child : CanonicalBranchNode)
    (hchild : child ∈ mol.canonicalChildren parent)
    (hparentHistory : 0 < parent.history.length) :
    child.depth = parent.depth + 1 := by
  rw [CanonicalBranchNode.depth, mol.canonicalChildren_history parent child hchild,
    List.length_cons]
  unfold CanonicalBranchNode.depth
  omega

theorem canonicalChildren_provenance_ne_phantom
    (mol : RawMolecule) (parent child : CanonicalBranchNode)
    (hchild : child ∈ mol.canonicalChildren parent) (distance : ℕ) :
    child.provenance ≠ CanonicalNodeProvenance.phantom distance := by
  unfold canonicalChildren at hchild
  by_cases hleaf : parent.forcedLeaf
  · simp [hleaf] at hchild
  · simp only [hleaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hchild
    obtain ⟨copy, hcopy, rfl⟩ := hchild
    by_cases hmultiple : copy.2 != 0
    · simp [hmultiple]
    · by_cases hring : copy.1 ∈ parent.history
      · simp [hmultiple, hring]
      · simp [hmultiple, hring]

theorem canonicalChildren_multipleBondDuplicate_distance
    (mol : RawMolecule) (parent child : CanonicalBranchNode)
    (hchild : child ∈ mol.canonicalChildren parent) (distance : ℕ)
    (hprovenance : child.provenance =
      CanonicalNodeProvenance.multipleBondDuplicate distance) :
    distance = parent.depth := by
  unfold canonicalChildren at hchild
  by_cases hleaf : parent.forcedLeaf
  · simp [hleaf] at hchild
  · simp only [hleaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hchild
    obtain ⟨copy, hcopy, hchildEq⟩ := hchild
    subst child
    by_cases hmultiple : copy.2 != 0
    · simp [hmultiple] at hprovenance
      exact hprovenance.symm
    · by_cases hring : copy.1 ∈ parent.history
      · simp [hmultiple, hring] at hprovenance
      · simp [hmultiple, hring] at hprovenance

end RawMolecule

namespace RawMolecule.CanonicalBranchKey

/-- Every converted carrier position has a concrete production source node. -/
def SourceComplete (key : CanonicalBranchKey) : Prop :=
  ∀ node : key.HierarchyNode,
    ∃ source, key.sourceNodeAtAddress? node.1 = some source

/-- Every source node retains the branch-history invariant used by the child compiler, and every
atom-carrying source points into the parsed atom table. -/
def SourceCoherent (mol : RawMolecule) (key : CanonicalBranchKey) : Prop :=
  ∀ node : key.HierarchyNode, ∀ source,
    key.sourceNodeAtAddress? node.1 = some source →
    source.history.head? = some source.atom ∧
      match source.provenance with
      | CanonicalNodeProvenance.phantom _ => True
      | _ => source.atom < mol.atomCount

/-- The root source is the exact production ligand root, including its suppressed external
parent in the stored history. -/
def RootedAt (key : CanonicalBranchKey) (center ligand : ℕ) : Prop :=
  key.sourceNodeAtAddress? [] = some (RawMolecule.canonicalRoot center ligand)

/-- Every converted parent--child edge is justified by the production chemical child relation. -/
def ChildrenSound (mol : RawMolecule) (key : CanonicalBranchKey) : Prop :=
  ∀ parent child parentSource childSource,
    key.HierarchyChild parent child →
    key.sourceNodeAtAddress? parent.1 = some parentSource →
    key.sourceNodeAtAddress? child.1 = some childSource →
    childSource ∈ mol.canonicalChildren parentSource

/-- Exact occurrence-level realization of the chemical child list at every converted parent.

The equivalence retains multiple identical duplicate occurrences as distinct child nodes; using
mere list membership here would lose triple-bond multiplicity. -/
def ChildrenExact (mol : RawMolecule) (key : CanonicalBranchKey) : Prop :=
  ∀ parent parentSource,
    key.sourceNodeAtAddress? parent.1 = some parentSource →
    ∃ equivalence :
        {child : key.HierarchyNode // key.HierarchyChild parent child} ≃
          Fin (mol.canonicalChildren parentSource).length,
      ∀ child,
        key.sourceNodeAtAddress? child.1.1 =
          some ((mol.canonicalChildren parentSource).get (equivalence child))

/-- Transport an arbitrary child predicate through exact occurrence realization. -/
theorem childCountWhere_eq_canonicalChildren_countP
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (hexact : key.ChildrenExact mol)
    (parent : key.HierarchyNode) (parentSource : CanonicalBranchNode)
    (hparent : key.sourceNodeAtAddress? parent.1 = some parentSource)
    (nodePredicate : key.HierarchyNode → Prop)
    (sourcePredicate : CanonicalBranchNode → Prop)
    [DecidablePred nodePredicate] [DecidablePred sourcePredicate]
    (hpredicate : ∀ (child :
      {node : key.HierarchyNode // key.HierarchyChild parent node}) source,
      key.sourceNodeAtAddress? child.1.1 = some source →
        (nodePredicate child.1 ↔ sourcePredicate source)) :
    RootedDigraph.ChildCountWhere (key.toDeclarativeDigraph mol) parent nodePredicate =
      (mol.canonicalChildren parentSource).countP fun source =>
        decide (sourcePredicate source) := by
  classical
  unfold RootedDigraph.ChildCountWhere
  change Nat.card {node : key.HierarchyNode //
    key.HierarchyChild parent node ∧ nodePredicate node} = _
  obtain ⟨equivalence, hlookup⟩ := hexact parent parentSource hparent
  rw [card_inter_equiv_countP (mol.canonicalChildren parentSource)
    (fun node : key.HierarchyNode => key.HierarchyChild parent node)
    nodePredicate sourcePredicate equivalence]
  intro child
  exact hpredicate child _ (hlookup child)

theorem sourceComplete_of_root_and_childrenExact
    (mol : RawMolecule) (key : CanonicalBranchKey) (rootSource : CanonicalBranchNode)
    (hroot : key.sourceNodeAtAddress? [] = some rootSource)
    (hexact : key.ChildrenExact mol) :
    key.SourceComplete := by
  intro node
  have hreachable := (key.toDeclarativeDigraph mol).reachable node
  change Relation.ReflTransGen key.HierarchyChild
    ⟨[], key.nil_mem_hierarchyAddresses⟩ node at hreachable
  induction hreachable with
  | refl => exact ⟨rootSource, hroot⟩
  | tail hparent hchild inductionHypothesis =>
      rcases inductionHypothesis with ⟨parentSource, hparentSource⟩
      rcases hexact _ parentSource hparentSource with ⟨equivalence, hlookup⟩
      exact ⟨(mol.canonicalChildren parentSource).get (equivalence ⟨_, hchild⟩),
        hlookup ⟨_, hchild⟩⟩

theorem childrenSound_of_childrenExact
    (mol : RawMolecule) (key : CanonicalBranchKey) (hexact : key.ChildrenExact mol) :
    key.ChildrenSound mol := by
  intro parent child parentSource childSource hchild hparentSource hchildSource
  rcases hexact parent parentSource hparentSource with ⟨equivalence, hlookup⟩
  let occurrence : {node : key.HierarchyNode // key.HierarchyChild parent node} :=
    ⟨child, hchild⟩
  have hsame : childSource =
      (mol.canonicalChildren parentSource).get (equivalence occurrence) := by
    exact Option.some.inj (hchildSource.symm.trans (hlookup occurrence))
  rw [hsame]
  exact List.get_mem _ _

theorem sourceCoherent_of_root_and_childrenExact
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol) :
    key.SourceCoherent mol := by
  have hcomplete := key.sourceComplete_of_root_and_childrenExact mol
    (RawMolecule.canonicalRoot center ligand) hroot hexact
  have coherentAlong : ∀ target : key.HierarchyNode,
      Relation.ReflTransGen key.HierarchyChild
        ⟨[], key.nil_mem_hierarchyAddresses⟩ target →
      ∀ source, key.sourceNodeAtAddress? target.1 = some source →
        source.history.head? = some source.atom ∧
          match source.provenance with
          | CanonicalNodeProvenance.phantom _ => True
          | _ => source.atom < mol.atomCount := by
    intro target reachable
    induction reachable with
    | refl =>
        intro source hsource
        have hsourceEq : source = RawMolecule.canonicalRoot center ligand :=
          Option.some.inj (hsource.symm.trans hroot)
        subst source
        exact ⟨rfl, ligand.isLt⟩
    | tail hparent hchild inductionHypothesis =>
        intro source hsource
        rcases hcomplete _ with ⟨parentSource, hparentSource⟩
        have hparentCoherent := inductionHypothesis parentSource hparentSource
        rcases hexact _ parentSource hparentSource with ⟨equivalence, hlookup⟩
        let generated :=
          (mol.canonicalChildren parentSource).get (equivalence ⟨_, hchild⟩)
        have hgeneratedMem : generated ∈ mol.canonicalChildren parentSource :=
          List.get_mem _ _
        have hgeneratedLookup := hlookup ⟨_, hchild⟩
        have hsourceEq : source = generated :=
          Option.some.inj (hsource.symm.trans hgeneratedLookup)
        subst source
        have hvalid := mol.canonicalChildren_atom_valid_and_adjacent center ligand hwellFormed
          parentSource generated hparentCoherent.1 hgeneratedMem
        refine ⟨mol.canonicalChildren_history_head parentSource generated hgeneratedMem, ?_⟩
        cases generated.provenance <;> simp [hvalid.1]
  intro node source hsource
  exact coherentAlong node ((key.toDeclarativeDigraph mol).reachable node) source hsource

theorem declarativeLabel_eq_of_sourceNodeAtAddress
    (mol : RawMolecule) (key : CanonicalBranchKey) (node : key.HierarchyNode)
    (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source) :
    key.declarativeLabel mol node =
      match source.provenance with
      | .phantom distance => ⟨none, .phantom distance⟩
      | provenance =>
          ⟨atomFin? mol source.atom, declarativeProvenance provenance⟩ := by
  unfold declarativeLabel
  rw [hsource]
  simp
  rfl

theorem declarativeLabel_compatible
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (hcomplete : key.SourceComplete) (hcoherent : key.SourceCoherent mol)
    (node : key.HierarchyNode) :
    RootedDigraph.LabelCompatible (key.declarativeLabel mol node) := by
  rcases hcomplete node with ⟨source, hsource⟩
  have hsourceCoherent := hcoherent node source hsource
  rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol node source hsource]
  cases hprovenance : source.provenance with
  | realAtom =>
      have hbound : source.atom < mol.atomCount := by
        simpa [hprovenance] using hsourceCoherent.2
      refine ⟨⟨source.atom, ?_⟩, ?_⟩
      · exact hbound
      · simp [atomFin?, hbound]
  | multipleBondDuplicate distance =>
      have hbound : source.atom < mol.atomCount := by
        simpa [hprovenance] using hsourceCoherent.2
      refine ⟨⟨source.atom, ?_⟩, ?_⟩
      · exact hbound
      · simp [atomFin?, hbound]
  | ringDuplicate distance =>
      have hbound : source.atom < mol.atomCount := by
        simpa [hprovenance] using hsourceCoherent.2
      refine ⟨⟨source.atom, ?_⟩, ?_⟩
      · exact hbound
      · simp [atomFin?, hbound]
  | phantom distance => rfl

theorem declarativeLabel_root_eq
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hroot : key.RootedAt center ligand) :
    (key.toDeclarativeDigraph mol).label (key.toDeclarativeDigraph mol).root =
      ⟨some ligand, NodeProvenance.realAtom⟩ := by
  unfold RootedAt at hroot
  change key.declarativeLabel mol ⟨[], key.nil_mem_hierarchyAddresses⟩ = _
  rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol
    ⟨[], key.nil_mem_hierarchyAddresses⟩
    (RawMolecule.canonicalRoot center ligand) hroot]
  simp [RawMolecule.canonicalRoot, atomFin?, declarativeProvenance]

theorem provenanceTerminal_has_no_hierarchyChild
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (hcomplete : key.SourceComplete) (hchildren : key.ChildrenSound mol)
    (node : key.HierarchyNode)
    (hterminal : RootedDigraph.ProvenanceTerminal
      (key.declarativeLabel mol node).provenance) :
    ∀ child, ¬key.HierarchyChild node child := by
  intro child hchild
  rcases hcomplete node with ⟨source, hsource⟩
  rcases hcomplete child with ⟨childSource, hchildSource⟩
  have hgenerated := hchildren node child source childSource hchild hsource hchildSource
  rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol node source hsource] at hterminal
  cases hprovenance : source.provenance with
  | realAtom =>
      simp [hprovenance, RootedDigraph.ProvenanceTerminal,
        declarativeProvenance] at hterminal
  | multipleBondDuplicate distance =>
      simp [RawMolecule.canonicalChildren, CanonicalBranchNode.forcedLeaf,
        hprovenance] at hgenerated
  | ringDuplicate distance =>
      simp [RawMolecule.canonicalChildren, CanonicalBranchNode.forcedLeaf,
        hprovenance] at hgenerated
  | phantom distance =>
      simp [RawMolecule.canonicalChildren, CanonicalBranchNode.forcedLeaf,
        hprovenance] at hgenerated

theorem parentSource_real_of_hierarchyChild
    (mol : RawMolecule) (key : CanonicalBranchKey) (hchildren : key.ChildrenSound mol)
    (parent child : key.HierarchyNode) (parentSource childSource : CanonicalBranchNode)
    (hchild : key.HierarchyChild parent child)
    (hparentSource : key.sourceNodeAtAddress? parent.1 = some parentSource)
    (hchildSource : key.sourceNodeAtAddress? child.1 = some childSource) :
    parentSource.provenance = CanonicalNodeProvenance.realAtom := by
  have hgenerated := hchildren parent child parentSource childSource hchild
    hparentSource hchildSource
  cases hprovenance : parentSource.provenance with
  | realAtom => rfl
  | multipleBondDuplicate distance =>
      simp [RawMolecule.canonicalChildren, CanonicalBranchNode.forcedLeaf,
        hprovenance] at hgenerated
  | ringDuplicate distance =>
      simp [RawMolecule.canonicalChildren, CanonicalBranchNode.forcedLeaf,
        hprovenance] at hgenerated
  | phantom distance =>
      simp [RawMolecule.canonicalChildren, CanonicalBranchNode.forcedLeaf,
        hprovenance] at hgenerated

theorem atomFin_eq_of_declarativeLabel_atom_eq
    (mol : RawMolecule) (key : CanonicalBranchKey) (node : key.HierarchyNode)
    (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source)
    (atom : Fin mol.atomCount)
    (hlabel : (key.declarativeLabel mol node).atom? = some atom) :
    atomFin? mol source.atom = some atom := by
  rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol node source hsource] at hlabel
  cases hprovenance : source.provenance <;>
    simp [hprovenance, declarativeProvenance] at hlabel ⊢
  all_goals assumption

theorem hierarchyChild_labels_adjacent
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hcomplete : key.SourceComplete) (hcoherent : key.SourceCoherent mol)
    (hchildren : key.ChildrenSound mol)
    (parent child : key.HierarchyNode) (parentAtom childAtom : Fin mol.atomCount)
    (hchild : key.HierarchyChild parent child)
    (hparentLabel : (key.declarativeLabel mol parent).atom? = some parentAtom)
    (hchildLabel : (key.declarativeLabel mol child).atom? = some childAtom) :
    (mol.canonicalHierarchyMoleculeGraph center ligand).Adj parentAtom childAtom := by
  rcases hcomplete parent with ⟨parentSource, hparentSource⟩
  rcases hcomplete child with ⟨childSource, hchildSource⟩
  have hparentReal := key.parentSource_real_of_hierarchyChild mol hchildren
    parent child parentSource childSource hchild hparentSource hchildSource
  have hgenerated := hchildren parent child parentSource childSource hchild
    hparentSource hchildSource
  have hparentCoherent := hcoherent parent parentSource hparentSource
  have hvalid := mol.canonicalChildren_atom_valid_and_adjacent center ligand hwellFormed
    parentSource childSource hparentCoherent.1 hgenerated
  have hparentBound : parentSource.atom < mol.atomCount := by
    simpa [hparentReal] using hparentCoherent.2
  have hparentAtomFin := key.atomFin_eq_of_declarativeLabel_atom_eq mol parent
    parentSource hparentSource parentAtom hparentLabel
  have hchildAtomFin := key.atomFin_eq_of_declarativeLabel_atom_eq mol child
    childSource hchildSource childAtom hchildLabel
  have hparentEq : (⟨parentSource.atom, hparentBound⟩ : Fin mol.atomCount) = parentAtom := by
    have hsome : some (⟨parentSource.atom, hparentBound⟩ : Fin mol.atomCount) =
        some parentAtom := by
      simpa [atomFin?, hparentBound] using hparentAtomFin
    exact Option.some.inj hsome
  have hchildEq : (⟨childSource.atom, hvalid.1⟩ : Fin mol.atomCount) = childAtom := by
    have hsome : some (⟨childSource.atom, hvalid.1⟩ : Fin mol.atomCount) =
        some childAtom := by
      simpa [atomFin?, hvalid.1] using hchildAtomFin
    exact Option.some.inj hsome
  subst parentAtom
  subst childAtom
  exact hvalid.2

/-- Structural realization plus raw-molecule well-formedness is sufficient for every local clause
of the independent constitutional expansion semantics. -/
theorem locallyAdmissibleExpansion
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hcomplete : key.SourceComplete) (hcoherent : key.SourceCoherent mol)
    (hchildren : key.ChildrenSound mol) :
    RootedDigraph.LocallyAdmissibleExpansion
      (mol.canonicalHierarchyMoleculeGraph center ligand) ligand
      (key.toDeclarativeDigraph mol) := by
  refine ⟨key.declarativeLabel_root_eq mol center ligand hroot,
    key.declarativeLabel_compatible mol hcomplete hcoherent, ?_, ?_⟩
  · intro node hterminal child
    exact key.provenanceTerminal_has_no_hierarchyChild mol hcomplete hchildren
      node hterminal child
  · intro parent child parentAtom childAtom hchild hparentLabel hchildLabel
    exact key.hierarchyChild_labels_adjacent mol center ligand hwellFormed
      hcomplete hcoherent hchildren parent child parentAtom childAtom
      hchild hparentLabel hchildLabel

theorem locallyAdmissibleExpansion_of_childrenExact
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol) :
    RootedDigraph.LocallyAdmissibleExpansion
      (mol.canonicalHierarchyMoleculeGraph center ligand) ligand
      (key.toDeclarativeDigraph mol) := by
  have hcomplete := key.sourceComplete_of_root_and_childrenExact mol
    (RawMolecule.canonicalRoot center ligand) hroot hexact
  have hcoherent := key.sourceCoherent_of_root_and_childrenExact mol center ligand
    hwellFormed hroot hexact
  exact key.locallyAdmissibleExpansion mol center ligand hwellFormed hroot
    hcomplete hcoherent (key.childrenSound_of_childrenExact mol hexact)

theorem atomBearingChildren_of_childrenExact
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol) :
    RootedDigraph.AtomBearingChildren (key.toDeclarativeDigraph mol) := by
  have hcomplete := key.sourceComplete_of_root_and_childrenExact mol
    (RawMolecule.canonicalRoot center ligand) hroot hexact
  have hcoherent := key.sourceCoherent_of_root_and_childrenExact mol center ligand
    hwellFormed hroot hexact
  have hchildren := key.childrenSound_of_childrenExact mol hexact
  intro parent child hedge
  rcases hcomplete parent with ⟨parentSource, hparentSource⟩
  rcases hcomplete child with ⟨childSource, hchildSource⟩
  have hgenerated := hchildren parent child parentSource childSource hedge
    hparentSource hchildSource
  have hchildCoherent := hcoherent child childSource hchildSource
  change ∃ atom, (key.declarativeLabel mol child).atom? = some atom
  rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol child childSource hchildSource]
  cases hprovenance : childSource.provenance with
  | realAtom | multipleBondDuplicate | ringDuplicate =>
      have hbound : childSource.atom < mol.atomCount := by
        simpa [hprovenance] using hchildCoherent.2
      exact ⟨⟨childSource.atom, hbound⟩, by simp [atomFin?, hbound]⟩
  | phantom distance =>
      exact (mol.canonicalChildren_provenance_ne_phantom parentSource childSource
        hgenerated distance hprovenance).elim

theorem source_depth_eq_address_length_succ
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source) :
    source.depth = node.1.length + 1 := by
  have hcomplete := key.sourceComplete_of_root_and_childrenExact mol
    (RawMolecule.canonicalRoot center ligand) hroot hexact
  have hreachable := (key.toDeclarativeDigraph mol).reachable node
  change Relation.ReflTransGen key.HierarchyChild
    ⟨[], key.nil_mem_hierarchyAddresses⟩ node at hreachable
  revert source
  induction hreachable with
  | refl =>
      intro source hsource
      have hsourceEq : source = RawMolecule.canonicalRoot center ligand :=
        Option.some.inj (hsource.symm.trans hroot)
      subst source
      rfl
  | tail hparent hchild inductionHypothesis =>
      intro source hsource
      rcases hcomplete _ with ⟨parentSource, hparentSource⟩
      have hparentDepth := inductionHypothesis parentSource hparentSource
      rcases hexact _ parentSource hparentSource with ⟨equivalence, hlookup⟩
      let generated := (mol.canonicalChildren parentSource).get
        (equivalence ⟨_, hchild⟩)
      have hgeneratedMem : generated ∈ mol.canonicalChildren parentSource :=
        List.get_mem _ _
      have hsourceEq : source = generated :=
        Option.some.inj (hsource.symm.trans (hlookup ⟨_, hchild⟩))
      subst source
      rcases hchild with ⟨slot, haddress⟩
      have hparentHistory : 0 < parentSource.history.length := by
        have hdepthPositive : 0 < parentSource.depth := by omega
        unfold CanonicalBranchNode.depth at hdepthPositive
        omega
      rw [mol.canonicalChildren_depth parentSource generated hgeneratedMem hparentHistory,
        hparentDepth, haddress]
      simp

theorem multipleBondDuplicate_distance_correct_of_childrenExact
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol) :
    ∀ parent child, key.HierarchyChild parent child → ∀ distance,
      (key.declarativeLabel mol child).provenance =
          NodeProvenance.multipleBondDuplicate distance →
        distance = ((key.declarativeAddressing mol).address parent).length + 1 := by
  have hcomplete := key.sourceComplete_of_root_and_childrenExact mol
    (RawMolecule.canonicalRoot center ligand) hroot hexact
  have hchildren := key.childrenSound_of_childrenExact mol hexact
  intro parent child hedge distance hprovenance
  rcases hcomplete parent with ⟨parentSource, hparentSource⟩
  rcases hcomplete child with ⟨childSource, hchildSource⟩
  have hgenerated := hchildren parent child parentSource childSource hedge
    hparentSource hchildSource
  rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol child childSource hchildSource]
    at hprovenance
  have hsourceProvenance : childSource.provenance =
      CanonicalNodeProvenance.multipleBondDuplicate distance := by
    cases hp : childSource.provenance <;>
      simp [hp, declarativeProvenance] at hprovenance ⊢
    exact hprovenance
  have hdistance := mol.canonicalChildren_multipleBondDuplicate_distance
    parentSource childSource hgenerated distance hsourceProvenance
  rw [hdistance]
  exact key.source_depth_eq_address_length_succ mol center ligand hroot hexact
    parent parentSource hparentSource

end RawMolecule.CanonicalBranchKey

namespace RawMolecule

/-! ## Complete compiler derivations -/

/- Semantic derivations retained from a successful *complete* recursive key build.

The mutually inductive list derivation exposes every recursive child proof and every successful
Rule-1a label check to the kernel induction principle.  Unlike a realization assumption, these
relations follow the actual chemical child function and actual priority sort.  Fuel-zero
truncations have no constructor unless the source is genuinely terminal. -/
mutual
  inductive CanonicalCompleteBuild (mol : RawMolecule) :
      CanonicalBranchNode → CanonicalBranchKey → Prop
    | terminal (node : CanonicalBranchNode)
        (hlabel : ∃ label, mol.canonicalRule1aLabel? node = some label)
        (hterminal : mol.canonicalTerminal node = true) :
        CanonicalCompleteBuild mol node (mol.canonicalRootKey node true)
    | branch (node : CanonicalBranchNode)
        (hlabel : ∃ label, mol.canonicalRule1aLabel? node = some label)
        (hterminal : mol.canonicalTerminal node = false)
        (childKeys sorted : List CanonicalBranchKey)
        (hchildren : CanonicalCompleteBuilds mol
          (mol.canonicalChildren node) childKeys)
        (hsorted : sortCanonicalKeys? childKeys = some sorted) :
        CanonicalCompleteBuild mol node
          (assembleCanonicalBranchKey (mol.canonicalRootKey node true) sorted)

  inductive CanonicalCompleteBuilds (mol : RawMolecule) :
      List CanonicalBranchNode → List CanonicalBranchKey → Prop
    | nil : CanonicalCompleteBuilds mol [] []
    | cons {node : CanonicalBranchNode} {key : CanonicalBranchKey}
        {nodes : List CanonicalBranchNode} {keys : List CanonicalBranchKey}
        (head : CanonicalCompleteBuild mol node key)
        (tail : CanonicalCompleteBuilds mol nodes keys) :
        CanonicalCompleteBuilds mol (node :: nodes) (key :: keys)
end

theorem CanonicalCompleteBuild.key_complete
    {mol : RawMolecule} {node : CanonicalBranchNode} {key : CanonicalBranchKey}
    (hbuild : CanonicalCompleteBuild mol node key) : key.complete = true := by
  cases hbuild <;> rfl

/- A recursive source tree realizes the chemical child function occurrence by occurrence and
retains the successful Rule-1a observation at every node.  Child order may be the production
priority order, but it must be a permutation of the complete chemical child list; the mutually
inductive forest relation retains the positional witness through every subtree. -/
mutual
  inductive CanonicalTreeRealizes (mol : RawMolecule) :
      CanonicalBranchNode → CanonicalSourceTree → Prop
    | node (source : CanonicalBranchNode) (children : CanonicalSourceForest)
        (hlabel : ∃ label, mol.canonicalRule1aLabel? source = some label)
        (childSources : List CanonicalBranchNode)
        (hperm : childSources.Perm (mol.canonicalChildren source))
        (hchildren : CanonicalForestRealizes mol childSources children) :
        CanonicalTreeRealizes mol source (.node source children)

  inductive CanonicalForestRealizes (mol : RawMolecule) :
      List CanonicalBranchNode → CanonicalSourceForest → Prop
    | nil : CanonicalForestRealizes mol [] .nil
    | cons {source : CanonicalBranchNode} {tree : CanonicalSourceTree}
        {sources : List CanonicalBranchNode} {trees : CanonicalSourceForest}
        (head : CanonicalTreeRealizes mol source tree)
        (tail : CanonicalForestRealizes mol sources trees) :
        CanonicalForestRealizes mol (source :: sources) (.cons tree trees)
end

theorem canonicalChildren_eq_nil_of_terminal
    (mol : RawMolecule) (node : CanonicalBranchNode)
    (hterminal : mol.canonicalTerminal node = true) :
    mol.canonicalChildren node = [] := by
  unfold canonicalTerminal at hterminal
  by_cases hleaf : node.forcedLeaf = true
  · simp [RawMolecule.canonicalChildren, hleaf]
  · have hleafFalse := Bool.eq_false_of_not_eq_true hleaf
    simp only [hleafFalse, Bool.false_or] at hterminal
    exact List.isEmpty_iff.mp hterminal

private theorem buildCanonicalChildKeys_completeBuild
    (mol : RawMolecule)
    (buildChild : ℕ → CanonicalBranchNode → Option CanonicalBranchKey)
    (hbuildChild : ∀ remaining node key,
      buildChild remaining node = some key → key.complete = true →
        CanonicalCompleteBuild mol node key) :
    ∀ remaining nodes keys,
      buildCanonicalChildKeys buildChild remaining nodes = some keys →
      keys.all (·.complete) = true →
      CanonicalCompleteBuilds mol nodes keys := by
  intro remaining nodes
  induction nodes generalizing remaining with
  | nil =>
      intro keys hkeys _
      simp [buildCanonicalChildKeys] at hkeys
      subst keys
      exact CanonicalCompleteBuilds.nil
  | cons node nodes inductionHypothesis =>
      intro keys hkeys hall
      unfold buildCanonicalChildKeys at hkeys
      cases hkey : buildChild remaining node with
      | none => simp [hkey] at hkeys
      | some key =>
          by_cases hbudget : remaining < key.nodeCount
          · simp [hkey, hbudget] at hkeys
          · simp only [hkey] at hkeys
            cases htail : buildCanonicalChildKeys buildChild
                (remaining - key.nodeCount) nodes with
            | none => simp [htail] at hkeys
            | some tail =>
                simp [htail] at hkeys
                rcases hkeys with ⟨_, rfl⟩
                simp only [List.all_cons, Bool.and_eq_true] at hall
                exact CanonicalCompleteBuilds.cons
                  (hbuildChild remaining node key hkey hall.1)
                  (inductionHypothesis (remaining - key.nodeCount) tail htail hall.2)

/-- Successful complete executable construction yields a semantic complete-build derivation.
In particular, the theorem excludes every fuel-zero truncation without postulating that the chosen
fuel was sufficient. -/
theorem buildCanonicalBranchKey_completeBuild
    (mol : RawMolecule) (cap fuel : ℕ) (node : CanonicalBranchNode)
    (key : CanonicalBranchKey)
    (hkey : mol.buildCanonicalBranchKey cap fuel node = some key)
    (hcomplete : key.complete = true) :
    CanonicalCompleteBuild mol node key := by
  induction fuel generalizing cap node key with
  | zero =>
      unfold buildCanonicalBranchKey at hkey
      cases hlabel : mol.canonicalRule1aLabel? node with
      | none => simp [hlabel] at hkey
      | some label =>
          simp [hlabel] at hkey
          subst key
          have hterminal : mol.canonicalTerminal node = true := by
            simpa [canonicalRootKey] using hcomplete
          simpa [hterminal] using
            CanonicalCompleteBuild.terminal node ⟨label, hlabel⟩ hterminal
  | succ fuel inductionHypothesis =>
      unfold buildCanonicalBranchKey at hkey
      cases hlabel : mol.canonicalRule1aLabel? node with
      | none => simp [hlabel] at hkey
      | some label =>
          by_cases hterminal : mol.canonicalTerminal node = true
          · simp [hlabel, hterminal] at hkey
            subst key
            exact CanonicalCompleteBuild.terminal node ⟨label, hlabel⟩ hterminal
          · have hterminalFalse : mol.canonicalTerminal node = false :=
              Bool.eq_false_of_not_eq_true hterminal
            simp only [hlabel, hterminalFalse, Bool.false_eq_true, ↓reduceIte] at hkey
            by_cases hwidth : 3 < (mol.canonicalChildren node).length
            · simp [hwidth] at hkey
            · simp only [hwidth, ↓reduceIte] at hkey
              cases hchildren : buildCanonicalChildKeys
                  (fun remaining child => mol.buildCanonicalBranchKey remaining fuel child)
                  (cap - 1) (mol.canonicalChildren node) with
              | none => simp [hchildren] at hkey
              | some childKeys =>
                  cases hsorted : sortCanonicalKeys? childKeys with
                  | none => simp [hchildren, hsorted] at hkey
                  | some sorted =>
                      simp [hchildren, hsorted] at hkey
                      rcases hkey with ⟨_, rfl⟩
                      have hallSorted : sorted.all (·.complete) = true := by
                        simpa [assembleCanonicalBranchKey, canonicalRootKey] using hcomplete
                      have hperm : sorted.Perm childKeys :=
                        sortCanonicalKeys?_perm childKeys sorted hsorted
                      have hallChildren : childKeys.all (·.complete) = true := by
                        rw [hperm.all_eq] at hallSorted
                        exact hallSorted
                      have hchildBuilds : CanonicalCompleteBuilds mol
                          (mol.canonicalChildren node) childKeys :=
                        buildCanonicalChildKeys_completeBuild mol
                          (fun remaining child =>
                            mol.buildCanonicalBranchKey remaining fuel child)
                          (fun remaining child childKey hchildKey hchildComplete =>
                            inductionHypothesis remaining child childKey hchildKey hchildComplete)
                          (cap - 1) (mol.canonicalChildren node) childKeys
                          hchildren hallChildren
                      simpa [hallSorted] using
                        CanonicalCompleteBuild.branch node ⟨label, hlabel⟩ hterminalFalse
                          childKeys sorted hchildBuilds hsorted

theorem branchCanonicalKey?_completeBuild
    (mol : RawMolecule) (center ligand : ℕ) (key : CanonicalBranchKey)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true) :
    CanonicalCompleteBuild mol (canonicalRoot center ligand) key := by
  unfold branchCanonicalKey? at hkey
  exact mol.buildCanonicalBranchKey_completeBuild _ _ _ _ hkey hcomplete

private theorem canonicalSourceForest?_exists_of_forall
    (keys : List CanonicalBranchKey)
    (hkeys : ∀ key ∈ keys, ∃ tree, key.sourceTree? = some tree) :
    ∃ forest, canonicalSourceForest? keys = some forest := by
  induction keys with
  | nil => exact ⟨.nil, rfl⟩
  | cons key keys inductionHypothesis =>
      obtain ⟨tree, htree⟩ := hkeys key (by simp)
      obtain ⟨forest, hforest⟩ := inductionHypothesis (by
        intro child hchild
        exact hkeys child (by simp [hchild]))
      exact ⟨.cons tree forest, by simp [canonicalSourceForest?, htree, hforest]⟩

private theorem collectCompleteSourceForest
    (mol : RawMolecule) {sources : List CanonicalBranchNode}
    {keys : List CanonicalBranchKey}
    (hrel : List.Forall₂ (fun source key =>
      ∃ tree, key.sourceTree? = some tree ∧ CanonicalTreeRealizes mol source tree)
      sources keys) :
    ∃ forest, canonicalSourceForest? keys = some forest ∧
      CanonicalForestRealizes mol sources forest := by
  induction hrel with
  | nil => exact ⟨.nil, rfl, .nil⟩
  | cons hhead htail inductionHypothesis =>
      obtain ⟨tree, htree, hrealizes⟩ := hhead
      obtain ⟨forest, hforest, hforestRealizes⟩ := inductionHypothesis
      exact ⟨.cons tree forest,
        by simp [canonicalSourceForest?, htree, hforest],
        .cons hrealizes hforestRealizes⟩

/-- A semantic complete build produces not just a stored tree but an occurrence-preserving
realization of the actual chemical child lists at every node. -/
theorem CanonicalCompleteBuild.sourceTreeRealizes
    {mol : RawMolecule} {node : CanonicalBranchNode} {key : CanonicalBranchKey}
    (hbuild : CanonicalCompleteBuild mol node key) :
    ∃ tree, key.sourceTree? = some tree ∧ CanonicalTreeRealizes mol node tree := by
  let realizesKey := fun (source : CanonicalBranchNode) (sourceKey : CanonicalBranchKey) =>
    ∃ tree, sourceKey.sourceTree? = some tree ∧ CanonicalTreeRealizes mol source tree
  let motiveBuild := fun (source : CanonicalBranchNode) (sourceKey : CanonicalBranchKey)
      (_ : CanonicalCompleteBuild mol source sourceKey) => realizesKey source sourceKey
  let motiveBuilds := fun (sources : List CanonicalBranchNode)
      (sourceKeys : List CanonicalBranchKey)
      (_ : CanonicalCompleteBuilds mol sources sourceKeys) =>
    List.Forall₂ realizesKey sources sourceKeys
  refine CanonicalCompleteBuild.rec (motive_1 := motiveBuild)
    (motive_2 := motiveBuilds) ?_ ?_ ?_ ?_ hbuild
  · intro source hlabel hterminal
    have hchildren : mol.canonicalChildren source = [] :=
      canonicalChildren_eq_nil_of_terminal mol source hterminal
    refine ⟨.node source .nil, rfl, .node source .nil hlabel [] ?_ .nil⟩
    simp [hchildren]
  · intro source hlabel hterminal childKeys sorted hchildren hsorted hchildRealizations
    have hcomp : Relation.Comp
        (List.Forall₂ realizesKey) List.Perm
        (mol.canonicalChildren source) sorted :=
      ⟨childKeys, hchildRealizations,
        (sortCanonicalKeys?_perm childKeys sorted hsorted).symm⟩
    rw [List.forall₂_comp_perm_eq_perm_comp_forall₂] at hcomp
    obtain ⟨sortedSources, hsources, hsortedRealizations⟩ := hcomp
    obtain ⟨forest, hforest, hforestRealizes⟩ :=
      collectCompleteSourceForest mol hsortedRealizations
    refine ⟨.node source forest, ?_,
      .node source forest hlabel sortedSources hsources.symm hforestRealizes⟩
    simp [assembleCanonicalBranchKey, canonicalRootKey, hforest]
  · exact List.Forall₂.nil
  · intro source sourceKey sources sourceKeys head tail hhead htail
    exact List.Forall₂.cons hhead htail

/-- Every semantic complete build retains a recursive source tree rooted at its source node. -/
theorem CanonicalCompleteBuild.sourceTree
    {mol : RawMolecule} {node : CanonicalBranchNode} {key : CanonicalBranchKey}
    (hbuild : CanonicalCompleteBuild mol node key) :
    ∃ children, key.sourceTree? = some (.node node children) := by
  obtain ⟨tree, htree, hrealizes⟩ := hbuild.sourceTreeRealizes
  cases hrealizes with
  | node source children hlabel childSources hperm hchildren =>
      exact ⟨children, htree⟩

@[simp] theorem canonicalCompleteBuild_root_source
    {mol : RawMolecule} {node : CanonicalBranchNode} {key : CanonicalBranchKey}
    (hbuild : CanonicalCompleteBuild mol node key) :
    key.sourceNodeAtAddress? [] = some node := by
  obtain ⟨children, htree⟩ := hbuild.sourceTree
  simp [CanonicalBranchKey.sourceNodeAtAddress?, htree]

/-! ## Recursive-tree address exactness -/

/-- Tree occurrences and recursive subtree lookup describe exactly the same addressed nodes. -/
theorem CanonicalSourceTree.mem_occurrences_iff_subtreeAt
    (tree : CanonicalSourceTree) (address : List ℕ) (source : CanonicalBranchNode) :
    (address, source) ∈ tree.occurrences ↔
      ∃ children, tree.subtreeAt? address = some (.node source children) := by
  let treeMotive := fun tree : CanonicalSourceTree =>
    ∀ address source, (address, source) ∈ tree.occurrences ↔
      ∃ children, tree.subtreeAt? address = some (CanonicalSourceTree.node source children)
  let forestMotive := fun forest : CanonicalSourceForest =>
    ∀ start address source,
      (address, source) ∈ forest.occurrences start ↔
        ∃ offset path children,
          address = (start + offset) :: path ∧
            forest.subtreeAt? offset path = some (CanonicalSourceTree.node source children)
  refine CanonicalSourceTree.rec (motive_1 := treeMotive) (motive_2 := forestMotive)
    ?_ ?_ ?_ tree address source
  · intro root children childrenIH address source
    constructor
    · intro hmem
      simp only [CanonicalSourceTree.occurrences, List.mem_cons] at hmem
      rcases hmem with hroot | hchild
      · have hsource : source = root := (Prod.mk.inj hroot).2
        have haddress : address = [] := (Prod.mk.inj hroot).1
        subst source
        subst address
        exact ⟨children, rfl⟩
      · rw [childrenIH 0 address source] at hchild
        obtain ⟨slot, path, descendants, haddress, hlookup⟩ := hchild
        subst address
        exact ⟨descendants, by simpa using hlookup⟩
    · rintro ⟨descendants, hlookup⟩
      cases address with
      | nil =>
          simp only [CanonicalSourceTree.subtreeAt?] at hlookup
          have heq := Option.some.inj hlookup
          cases heq
          exact List.mem_cons_self
      | cons slot path =>
          simp only [CanonicalSourceTree.subtreeAt?] at hlookup
          have hchild : ((slot :: path), source) ∈ children.occurrences 0 := by
            rw [childrenIH 0 (slot :: path) source]
            exact ⟨slot, path, descendants, by simp, hlookup⟩
          exact List.mem_cons_of_mem _ hchild
  · intro start address source
    constructor
    · simp [CanonicalSourceForest.occurrences]
    · rintro ⟨offset, path, children, haddress, hlookup⟩
      simp [CanonicalSourceForest.subtreeAt?] at hlookup
  · intro head tail headIH tailIH start address source
    constructor
    · intro hmem
      simp only [CanonicalSourceForest.occurrences, List.mem_append,
        List.mem_map] at hmem
      rcases hmem with hhead | htail
      · obtain ⟨entry, hentry, hentryEq⟩ := hhead
        rcases entry with ⟨path, entrySource⟩
        simp only [Prod.mk.injEq] at hentryEq
        obtain ⟨haddress, hsource⟩ := hentryEq
        subst entrySource
        rw [headIH path source] at hentry
        obtain ⟨children, hlookup⟩ := hentry
        exact ⟨0, path, children, by simpa using haddress.symm, by simpa using hlookup⟩
      · rw [tailIH (start + 1) address source] at htail
        obtain ⟨offset, path, children, haddress, hlookup⟩ := htail
        refine ⟨offset + 1, path, children, ?_, by simpa using hlookup⟩
        rw [haddress]
        congr 1
        omega
    · rintro ⟨offset, path, children, haddress, hlookup⟩
      cases offset with
      | zero =>
          simp only [CanonicalSourceForest.subtreeAt?] at hlookup
          simp only [CanonicalSourceForest.occurrences, List.mem_append]
          apply Or.inl
          rw [List.mem_map]
          refine ⟨(path, source), ?_, ?_⟩
          · rw [headIH path source]
            exact ⟨children, hlookup⟩
          · simp [haddress]
      | succ offset =>
          simp only [CanonicalSourceForest.subtreeAt?] at hlookup
          simp only [CanonicalSourceForest.occurrences, List.mem_append]
          apply Or.inr
          rw [tailIH (start + 1) address source]
          refine ⟨offset, path, children, ?_, hlookup⟩
          rw [haddress]
          congr 1
          omega

theorem CanonicalSourceForest.subtreeAt?_eq_get?_bind
    (forest : CanonicalSourceForest) (slot : ℕ) (address : List ℕ) :
    forest.subtreeAt? slot address =
      (forest.toList[slot]?).bind fun tree => tree.subtreeAt? address := by
  induction slot generalizing forest with
  | zero =>
      cases forest <;>
        simp [CanonicalSourceForest.subtreeAt?, CanonicalSourceForest.toList]
  | succ slot inductionHypothesis =>
      cases forest with
      | nil => simp [CanonicalSourceForest.subtreeAt?, CanonicalSourceForest.toList]
      | cons head tail =>
          simpa [CanonicalSourceForest.subtreeAt?, CanonicalSourceForest.toList] using
            inductionHypothesis tail

theorem CanonicalSourceTree.subtreeAt?_append
    (tree : CanonicalSourceTree) (first second : List ℕ) :
    tree.subtreeAt? (first ++ second) =
      (tree.subtreeAt? first).bind fun subtree => subtree.subtreeAt? second := by
  induction first generalizing tree with
  | nil => simp [CanonicalSourceTree.subtreeAt?]
  | cons slot first inductionHypothesis =>
      cases tree with
      | node source forest =>
          change forest.subtreeAt? slot (first ++ second) =
            (forest.subtreeAt? slot first).bind fun subtree => subtree.subtreeAt? second
          rw [forest.subtreeAt?_eq_get?_bind, forest.subtreeAt?_eq_get?_bind]
          simp only [Option.bind_assoc]
          apply Option.bind_congr
          intro child hchild
          exact inductionHypothesis child

theorem CanonicalSourceTree.occurrences_prefix_closed
    (tree : CanonicalSourceTree) (address : List ℕ) (source : CanonicalBranchNode)
    (hmem : (address, source) ∈ tree.occurrences)
    (prefixAddress : List ℕ) (hprefix : prefixAddress <+: address) :
    ∃ prefixSource, (prefixAddress, prefixSource) ∈ tree.occurrences := by
  rcases hprefix with ⟨suffix, rfl⟩
  rw [tree.mem_occurrences_iff_subtreeAt] at hmem
  obtain ⟨children, hlookup⟩ := hmem
  rw [tree.subtreeAt?_append] at hlookup
  cases hprefixLookup : tree.subtreeAt? prefixAddress with
  | none => simp [hprefixLookup] at hlookup
  | some prefixTree =>
      cases prefixTree with
      | node prefixSource prefixChildren =>
          refine ⟨prefixSource, ?_⟩
          rw [tree.mem_occurrences_iff_subtreeAt]
          exact ⟨prefixChildren, hprefixLookup⟩

theorem CanonicalBranchKey.mem_hierarchyAddresses_iff_tree_occurrence
    (key : CanonicalBranchKey) (tree : CanonicalSourceTree)
    (htree : key.sourceTree? = some tree) (address : List ℕ) :
    address ∈ key.hierarchyAddresses ↔
      ∃ source, (address, source) ∈ tree.occurrences := by
  rw [key.mem_hierarchyAddresses_iff]
  constructor
  · rintro (rfl | ⟨entry, hentry, hprefix⟩)
    · cases tree with
      | node source children =>
          exact ⟨source, by simp [CanonicalSourceTree.occurrences]⟩
    · unfold CanonicalBranchKey.addressedNodes at hentry
      rw [List.mem_map] at hentry
      obtain ⟨sourceEntry, hsourceEntry, hentryEq⟩ := hentry
      have hsources : key.addressedSources = tree.occurrences := by
        simp [CanonicalBranchKey.addressedSources, htree]
      rw [hsources] at hsourceEntry
      have hentryAddress : sourceEntry.1 = entry.1 := congrArg Prod.fst hentryEq
      rw [← hentryAddress] at hprefix
      obtain ⟨prefixSource, hprefixSource⟩ :=
        tree.occurrences_prefix_closed sourceEntry.1 sourceEntry.2 hsourceEntry
          address hprefix
      exact ⟨prefixSource, hprefixSource⟩
  · rintro ⟨source, hsource⟩
    apply Or.inr
    refine ⟨(address, (source.atom, source.provenance)), ?_, List.prefix_refl _⟩
    unfold CanonicalBranchKey.addressedNodes
    rw [List.mem_map]
    refine ⟨(address, source), ?_, rfl⟩
    simpa [CanonicalBranchKey.addressedSources, htree] using hsource

@[simp] theorem CanonicalBranchKey.sourceNodeAtAddress?_eq_tree_sourceAt
    (key : CanonicalBranchKey) (tree : CanonicalSourceTree)
    (htree : key.sourceTree? = some tree) (address : List ℕ) :
    key.sourceNodeAtAddress? address = tree.sourceAt? address := by
  simp [CanonicalBranchKey.sourceNodeAtAddress?, htree]

theorem CanonicalForestRealizes.length_eq
    {mol : RawMolecule} {sources : List CanonicalBranchNode}
    {forest : CanonicalSourceForest}
    (hrealizes : CanonicalForestRealizes mol sources forest) :
    forest.toList.length = sources.length := by
  cases hrealizes with
  | nil => rfl
  | @cons source tree sources forest head tail =>
      simp [CanonicalSourceForest.toList, tail.length_eq]
termination_by sources.length

theorem CanonicalForestRealizes.get
    {mol : RawMolecule} {sources : List CanonicalBranchNode}
    {forest : CanonicalSourceForest}
    (hrealizes : CanonicalForestRealizes mol sources forest)
    (slot : ℕ) (hsource : slot < sources.length)
    (htree : slot < forest.toList.length) :
    CanonicalTreeRealizes mol
      (sources.get ⟨slot, hsource⟩) (forest.toList.get ⟨slot, htree⟩) := by
  induction slot generalizing sources forest with
  | zero =>
      cases hrealizes with
      | nil => simp at hsource
      | cons head tail => exact head
  | succ slot inductionHypothesis =>
      cases hrealizes with
      | nil => simp at hsource
      | @cons source tree sources forest head tail =>
          exact inductionHypothesis tail (by simpa using hsource)
            (by simpa [CanonicalSourceForest.toList] using htree)

theorem CanonicalSourceForest.subtreeAt?_nil_isSome_iff
    (forest : CanonicalSourceForest) (slot : ℕ) :
    (forest.subtreeAt? slot []).isSome = true ↔ slot < forest.toList.length := by
  rw [forest.subtreeAt?_eq_get?_bind]
  by_cases hslot : slot < forest.toList.length
  · rw [List.getElem?_eq_getElem hslot]
    simp [CanonicalSourceTree.subtreeAt?, hslot]
  · have hle : forest.toList.length ≤ slot := by omega
    rw [List.getElem?_eq_none hle]
    simp [hslot]

theorem CanonicalTreeRealizes.subtree
    {mol : RawMolecule} {rootSource : CanonicalBranchNode}
    {tree subtree : CanonicalSourceTree}
    (hrealizes : CanonicalTreeRealizes mol rootSource tree)
    (address : List ℕ) (hlookup : tree.subtreeAt? address = some subtree) :
    ∃ source, CanonicalTreeRealizes mol source subtree := by
  induction address generalizing rootSource tree with
  | nil =>
      simp only [CanonicalSourceTree.subtreeAt?] at hlookup
      have hsubtree : tree = subtree := Option.some.inj hlookup
      subst subtree
      exact ⟨rootSource, hrealizes⟩
  | cons slot address inductionHypothesis =>
      cases hrealizes with
      | node source forest hlabel childSources hperm hchildren =>
          change forest.subtreeAt? slot address = some subtree at hlookup
          rw [forest.subtreeAt?_eq_get?_bind] at hlookup
          by_cases hslot : slot < forest.toList.length
          · rw [List.getElem?_eq_getElem hslot] at hlookup
            simp only [Option.bind_some] at hlookup
            have hsourceSlot : slot < childSources.length := by
              rwa [← hchildren.length_eq]
            have hchildRealizes := hchildren.get slot hsourceSlot hslot
            exact inductionHypothesis hchildRealizes hlookup
          · have hle : forest.toList.length ≤ slot := by omega
            rw [List.getElem?_eq_none hle] at hlookup
            simp at hlookup

theorem CanonicalTreeRealizes.tree_eq_node
    {mol : RawMolecule} {source : CanonicalBranchNode} {tree : CanonicalSourceTree}
    (hrealizes : CanonicalTreeRealizes mol source tree) :
    ∃ children, tree = .node source children := by
  cases hrealizes with
  | node source children hlabel childSources hperm hchildren => exact ⟨children, rfl⟩

/-- Every source occurrence in a realized compiler tree retains evidence that its checked
Rule-1a observation was successfully produced. -/
theorem CanonicalTreeRealizes.rule1aLabelSupportedAt
    {mol : RawMolecule} {rootSource source : CanonicalBranchNode}
    {tree : CanonicalSourceTree}
    (hrealizes : CanonicalTreeRealizes mol rootSource tree)
    (address : List ℕ) (hsource : tree.sourceAt? address = some source) :
    ∃ label, mol.canonicalRule1aLabel? source = some label := by
  unfold CanonicalSourceTree.sourceAt? at hsource
  cases hsubtree : tree.subtreeAt? address with
  | none => simp [hsubtree] at hsource
  | some subtree =>
      cases subtree with
      | node stored children =>
          simp only [hsubtree, Option.map_some] at hsource
          have hstored : stored = source := Option.some.inj hsource
          subst stored
          obtain ⟨realizedSource, hsubtreeRealizes⟩ :=
            hrealizes.subtree address hsubtree
          cases hsubtreeRealizes with
          | node source children hlabel childSources hperm hchildren => exact hlabel

/-- Child nodes are canonically the occupied one-step extension slots. -/
noncomputable def hierarchyChildrenEquivSlots
    (key : CanonicalBranchKey) (parent : key.HierarchyNode) :
    {child : key.HierarchyNode // key.HierarchyChild parent child} ≃
      {slot : ℕ // parent.1 ++ [slot] ∈ key.hierarchyAddresses} where
  toFun child := by
    let slot := Classical.choose child.2
    have hslot := Classical.choose_spec child.2
    exact ⟨slot, hslot ▸ child.1.2⟩
  invFun slot := ⟨⟨parent.1 ++ [slot.1], slot.2⟩, ⟨slot.1, rfl⟩⟩
  left_inv child := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Classical.choose_spec child.2).symm
  right_inv slot := by
    apply Subtype.ext
    dsimp
    apply List.singleton_injective
    apply List.append_cancel_left
    let child : {child : key.HierarchyNode // key.HierarchyChild parent child} :=
      ⟨⟨parent.1 ++ [slot.1], slot.2⟩, ⟨slot.1, rfl⟩⟩
    exact (Classical.choose_spec child.2).symm

theorem CanonicalBranchKey.child_address_mem_iff
    (key : CanonicalBranchKey) (tree : CanonicalSourceTree)
    (htree : key.sourceTree? = some tree)
    (parentAddress : List ℕ) (parentSource : CanonicalBranchNode)
    (children : CanonicalSourceForest)
    (hparent : tree.subtreeAt? parentAddress = some (.node parentSource children))
    (slot : ℕ) :
    parentAddress ++ [slot] ∈ key.hierarchyAddresses ↔
      slot < children.toList.length := by
  constructor
  · intro hmem
    rw [key.mem_hierarchyAddresses_iff_tree_occurrence tree htree] at hmem
    obtain ⟨source, hsource⟩ := hmem
    rw [tree.mem_occurrences_iff_subtreeAt] at hsource
    obtain ⟨grandchildren, hchild⟩ := hsource
    rw [tree.subtreeAt?_append, hparent] at hchild
    simp only [Option.bind_some] at hchild
    change children.subtreeAt? slot [] = some (.node source grandchildren) at hchild
    have hisSome : (children.subtreeAt? slot []).isSome = true := by
      rw [hchild]
      rfl
    exact (children.subtreeAt?_nil_isSome_iff slot).mp hisSome
  · intro hslot
    have hisSome := (children.subtreeAt?_nil_isSome_iff slot).mpr hslot
    cases hchild : children.subtreeAt? slot [] with
    | none => simp [hchild] at hisSome
    | some childTree =>
        cases childTree with
        | node childSource grandchildren =>
            rw [key.mem_hierarchyAddresses_iff_tree_occurrence tree htree]
            refine ⟨childSource, ?_⟩
            rw [tree.mem_occurrences_iff_subtreeAt]
            refine ⟨grandchildren, ?_⟩
            rw [tree.subtreeAt?_append, hparent]
            simpa using hchild

noncomputable def occupiedChildSlotsEquivFin
    (key : CanonicalBranchKey) (tree : CanonicalSourceTree)
    (htree : key.sourceTree? = some tree)
    (parentAddress : List ℕ) (parentSource : CanonicalBranchNode)
    (children : CanonicalSourceForest)
    (hparent : tree.subtreeAt? parentAddress = some (.node parentSource children)) :
    {slot : ℕ // parentAddress ++ [slot] ∈ key.hierarchyAddresses} ≃
      Fin children.toList.length where
  toFun slot := ⟨slot.1,
    (key.child_address_mem_iff tree htree parentAddress parentSource children hparent slot).mp
      slot.2⟩
  invFun slot := ⟨slot.1,
    (key.child_address_mem_iff tree htree parentAddress parentSource children hparent slot).mpr
      slot.2⟩
  left_inv slot := by
    apply Subtype.ext
    rfl
  right_inv slot := by
    apply Fin.ext
    rfl

/-- A recursively realized source tree supplies the exact occurrence-level child equivalence used
by the independent hierarchy semantics. -/
theorem CanonicalTreeRealizes.childrenExact
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (rootSource : CanonicalBranchNode) (tree : CanonicalSourceTree)
    (htree : key.sourceTree? = some tree)
    (hrealizes : CanonicalTreeRealizes mol rootSource tree) :
    key.ChildrenExact mol := by
  intro parent parentSource hparentSource
  have hsourceAt : tree.sourceAt? parent.1 = some parentSource := by
    simpa [key.sourceNodeAtAddress?_eq_tree_sourceAt tree htree] using hparentSource
  unfold CanonicalSourceTree.sourceAt? at hsourceAt
  cases hparentTree : tree.subtreeAt? parent.1 with
  | none => simp [hparentTree] at hsourceAt
  | some parentTree =>
      cases parentTree with
      | node storedParent children =>
          simp only [hparentTree, Option.map_some] at hsourceAt
          have hstored : storedParent = parentSource := Option.some.inj hsourceAt
          subst storedParent
          obtain ⟨realizedParent, hparentRealizes⟩ :=
            hrealizes.subtree parent.1 hparentTree
          cases hparentRealizes with
          | node parentSource children hlabel childSources hperm hchildren =>
              obtain ⟨permutationEquiv, hpermutationGet⟩ :=
                TetraStereo.OneCenter.List.Perm.exists_finEquiv_get hperm
              let childSlots := hierarchyChildrenEquivSlots key parent
              let occupiedSlots := occupiedChildSlotsEquivFin key tree htree parent.1
                parentSource children hparentTree
              let sourceSlots : Fin children.toList.length ≃ Fin childSources.length :=
                finCongr hchildren.length_eq
              let equivalence :
                  {child : key.HierarchyNode // key.HierarchyChild parent child} ≃
                    Fin (mol.canonicalChildren parentSource).length :=
                childSlots.trans (occupiedSlots.trans (sourceSlots.trans permutationEquiv))
              refine ⟨equivalence, ?_⟩
              intro child
              let occupied := childSlots child
              let forestIndex := occupiedSlots occupied
              let sourceIndex := sourceSlots forestIndex
              have hforestLookup : children.subtreeAt? forestIndex.1 [] =
                  some (children.toList.get forestIndex) := by
                rw [children.subtreeAt?_eq_get?_bind,
                  List.getElem?_eq_getElem forestIndex.2]
                simp [CanonicalSourceTree.subtreeAt?]
              have hchildRealizes := hchildren.get forestIndex.1 sourceIndex.2 forestIndex.2
              obtain ⟨grandchildren, hchildTree⟩ := hchildRealizes.tree_eq_node
              have haddress : child.1.1 = parent.1 ++ [forestIndex.1] := by
                exact Classical.choose_spec child.2
              have hlookup : key.sourceNodeAtAddress? child.1.1 =
                  some (childSources.get sourceIndex) := by
                rw [key.sourceNodeAtAddress?_eq_tree_sourceAt tree htree]
                unfold CanonicalSourceTree.sourceAt?
                rw [haddress, tree.subtreeAt?_append, hparentTree]
                simp only [Option.bind_some]
                change (children.subtreeAt? forestIndex.1 []).map (fun subtree =>
                  match subtree with
                  | .node source _ => source) = some (childSources.get sourceIndex)
                rw [hforestLookup, hchildTree]
                rfl
              rw [hlookup]
              apply congrArg some
              calc
                childSources.get sourceIndex =
                    (mol.canonicalChildren parentSource).get
                      (permutationEquiv sourceIndex) := hpermutationGet sourceIndex
                _ = (mol.canonicalChildren parentSource).get (equivalence child) := by
                  rfl

/-- The actual complete compiler derivation realizes every declarative child occurrence exactly. -/
theorem CanonicalCompleteBuild.childrenExact
    {mol : RawMolecule} {node : CanonicalBranchNode} {key : CanonicalBranchKey}
    (hbuild : CanonicalCompleteBuild mol node key) :
    key.ChildrenExact mol := by
  obtain ⟨tree, htree, hrealizes⟩ := hbuild.sourceTreeRealizes
  exact hrealizes.childrenExact mol key node tree htree

/-- A complete compiler derivation supports the Rule-1a label of every retained source
occurrence, including identical duplicate occurrences at different addresses. -/
theorem CanonicalCompleteBuild.rule1aLabelSupportedAt
    {mol : RawMolecule} {node source : CanonicalBranchNode}
    {key : CanonicalBranchKey}
    (hbuild : CanonicalCompleteBuild mol node key)
    (address : List ℕ) (hsource : key.sourceNodeAtAddress? address = some source) :
    ∃ label, mol.canonicalRule1aLabel? source = some label := by
  obtain ⟨tree, htree, hrealizes⟩ := hbuild.sourceTreeRealizes
  rw [key.sourceNodeAtAddress?_eq_tree_sourceAt tree htree] at hsource
  exact hrealizes.rule1aLabelSupportedAt address hsource

theorem branchCanonicalKey?_childrenExact
    (mol : RawMolecule) (center ligand : ℕ) (key : CanonicalBranchKey)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true) :
    key.ChildrenExact mol :=
  (mol.branchCanonicalKey?_completeBuild center ligand key hkey hcomplete).childrenExact

/-- Every source occurrence in a successful complete public branch compilation has a checked
Rule-1a label. -/
theorem branchCanonicalKey?_rule1aLabelSupportedAt
    (mol : RawMolecule) (center ligand : ℕ) (key : CanonicalBranchKey)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true) (address : List ℕ)
    (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? address = some source) :
    ∃ label, mol.canonicalRule1aLabel? source = some label :=
  CanonicalCompleteBuild.rule1aLabelSupportedAt
    (mol.branchCanonicalKey?_completeBuild center ligand key hkey hcomplete)
    address hsource

theorem branchCanonicalKey?_locallyAdmissibleExpansion
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (hwellFormed : mol.WellFormed)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true) :
    RootedDigraph.LocallyAdmissibleExpansion
      (mol.canonicalHierarchyMoleculeGraph center ligand) ligand
      (key.toDeclarativeDigraph mol) := by
  have hbuild := mol.branchCanonicalKey?_completeBuild center ligand key hkey hcomplete
  have hroot : key.RootedAt center ligand := canonicalCompleteBuild_root_source hbuild
  exact key.locallyAdmissibleExpansion_of_childrenExact mol center ligand hwellFormed
    hroot hbuild.childrenExact

theorem branchCanonicalKey?_atomBearingChildren
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (hwellFormed : mol.WellFormed)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true) :
    RootedDigraph.AtomBearingChildren (key.toDeclarativeDigraph mol) := by
  have hbuild := mol.branchCanonicalKey?_completeBuild center ligand key hkey hcomplete
  have hroot : key.RootedAt center ligand := canonicalCompleteBuild_root_source hbuild
  exact key.atomBearingChildren_of_childrenExact mol center ligand hwellFormed
    hroot hbuild.childrenExact

theorem CanonicalCompleteBuild.rootedAt
    {mol : RawMolecule} {node : CanonicalBranchNode} {key : CanonicalBranchKey}
    (hbuild : CanonicalCompleteBuild mol node key) :
    key.sourceNodeAtAddress? [] = some node :=
  canonicalCompleteBuild_root_source hbuild

end RawMolecule

end
end OneCenter
end TetraStereo
