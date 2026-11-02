import TetraStereo.OneCenter.LocalizedOuterDigraphActualPriorityFidelity
import TetraStereo.OneCenter.LocalizedConstitutionalObservable
import TetraStereo.OneCenter.LocalizedRealizedTreeCutEmbedding
import TetraStereo.OneCenter.LocalizedRerootRuleMajorKey
import TetraStereo.OneCenter.LocalizedRerootChildrenExecutable
import TetraStereo.KernelOnly

set_option autoImplicit false

universe u

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput



































































variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-! ## A. The finite atom-labelled physical tree -/

/-- A finite atom-labelled rooted tree: a vertex root and an ordered list of child trees.  The
children are ordered lists; their order carries no meaning unless separately constrained by the
independent physical descent predicate. -/
structure PhysicalAtomTree (V : Type u) where
  root : V
  children : List (PhysicalAtomTree V)

namespace PhysicalAtomTree

/-- The subtree at a position (address), if the address is occupied. -/
def subtreeAt? {V : Type u} (tree : PhysicalAtomTree V) : List Nat → Option (PhysicalAtomTree V)
  | [] => some tree
  | slot :: rest => (tree.children[slot]?).bind fun child => subtreeAt? child rest

@[simp] theorem subtreeAt?_nil {V : Type u} (tree : PhysicalAtomTree V) :
    subtreeAt? tree [] = some tree := rfl

@[simp] theorem subtreeAt?_cons {V : Type u} (tree : PhysicalAtomTree V) (slot : Nat)
    (rest : List Nat) :
    subtreeAt? tree (slot :: rest) =
      (tree.children[slot]?).bind fun child => subtreeAt? child rest := rfl

theorem subtreeAt?_append {V : Type u} (tree : PhysicalAtomTree V) (left right : List Nat) :
    subtreeAt? tree (left ++ right) =
      (subtreeAt? tree left).bind fun sub => subtreeAt? sub right := by
  induction left generalizing tree with
  | nil => rfl
  | cons slot rest ih =>
      rw [List.cons_append]
      rw [subtreeAt?_cons, subtreeAt?_cons]
      cases hLookup : tree.children[slot]? with
      | none => rfl
      | some child => exact ih child

/-- Unfold one successful step of the lookup. -/
theorem subtreeAt?_cons_eq_some_iff {V : Type u} (tree : PhysicalAtomTree V) (slot : Nat)
    (rest : List Nat) (sub : PhysicalAtomTree V) :
    subtreeAt? tree (slot :: rest) = some sub ↔
      ∃ child, tree.children[slot]? = some child ∧ subtreeAt? child rest = some sub := by
  rw [subtreeAt?_cons, Option.bind_eq_some_iff]

-- The occupied addresses of a physical tree, in sphere-major address order; the root address
-- `[]` is first, and children are listed by slot with recursively occupied suffixes.  The two
-- functions are mutually recursive so that the well-founded recursion is structural in the spine
-- of the tree.
mutual
  /-- The occupied addresses of a physical tree: the root address first, then every child's
  occupied addresses prefixed by that child's slot. -/
  def occupiedAddresses {V : Type u} : PhysicalAtomTree V → List (List Nat)
    | ⟨_root, children⟩ => [] :: occupiedChildrenAddresses children 0
  termination_by tree => sizeOf tree
  decreasing_by
    simp_wf

  /-- The occupied addresses contributed by a list of children, starting at an absolute slot
  offset. -/
  def occupiedChildrenAddresses {V : Type u} : List (PhysicalAtomTree V) → Nat → List (List Nat)
    | [], _slot => []
    | child :: rest, slot =>
        (occupiedAddresses child).map (fun suffix => slot :: suffix) ++
          occupiedChildrenAddresses rest (slot + 1)
  termination_by children _ => sizeOf children
  decreasing_by
    all_goals (simp_wf <;> omega)
end

/-! ### Unfolding equations

`occupiedAddresses` and `occupiedChildrenAddresses` are defined by well-founded recursion, so
their defining equations are not definitional.  These lemmas record them explicitly. -/

/-- The defining equation of `occupiedAddresses` at one concrete node. -/
theorem occupiedAddresses_mk {V : Type u} (root : V) (children : List (PhysicalAtomTree V)) :
    occupiedAddresses ⟨root, children⟩ = [] :: occupiedChildrenAddresses children 0 := by
  rw [occupiedAddresses]

/-- The defining equation of `occupiedChildrenAddresses` at the empty list. -/
theorem occupiedChildrenAddresses_nil {V : Type u} (slot : Nat) :
    occupiedChildrenAddresses ([] : List (PhysicalAtomTree V)) slot = [] := by
  rw [occupiedChildrenAddresses]

/-- The defining equation of `occupiedChildrenAddresses` at a cons. -/
theorem occupiedChildrenAddresses_cons {V : Type u} (child : PhysicalAtomTree V)
    (rest : List (PhysicalAtomTree V)) (slot : Nat) :
    occupiedChildrenAddresses (child :: rest) slot =
      (occupiedAddresses child).map (fun suffix => slot :: suffix) ++
        occupiedChildrenAddresses rest (slot + 1) := by
  rw [occupiedChildrenAddresses]

private theorem add_succ_swap (offset slot : Nat) :
    (offset + 1) + slot = offset + (slot + 1) := by omega

/-- If a child sits at a slot offset, its occupied addresses prefixed by that absolute slot are
occupied addresses of the children list. -/
theorem mem_occupiedChildrenAddresses_of_getElem? {V : Type u}
    (children : List (PhysicalAtomTree V)) (offset slot : Nat) (child : PhysicalAtomTree V)
    (suffix : List Nat) :
    children[slot]? = some child → suffix ∈ occupiedAddresses child →
      (offset + slot) :: suffix ∈ occupiedChildrenAddresses children offset := by
  intro hLookup hIn
  induction children generalizing offset slot suffix with
  | nil => simp at hLookup
  | cons head tail ih =>
      cases slot with
      | zero =>
          simp at hLookup
          cases hLookup
          rw [occupiedChildrenAddresses_cons]
          exact List.mem_append.mpr (Or.inl (by
            exact List.mem_map.mpr ⟨suffix, hIn, by simp⟩))
      | succ slot' =>
          rw [← add_succ_swap, occupiedChildrenAddresses_cons]
          exact List.mem_append.mpr (Or.inr (ih (offset + 1) slot' suffix hLookup hIn))

/-- An address that is not occupied has no subtree: the observation at it is the absent value. -/
theorem subtreeAt?_none_of_not_mem_occupied {V : Type u} (tree : PhysicalAtomTree V)
    {position : List Nat} (h : position ∉ occupiedAddresses tree) :
    subtreeAt? tree position = none := by
  cases tree with
  | mk root children =>
      induction position generalizing root children with
      | nil => simp [occupiedAddresses] at h
      | cons slot rest ih =>
          rw [subtreeAt?_cons]
          cases hLookup : children[slot]? with
          | none => rfl
          | some child =>
              cases child with
              | mk croot cchildren =>
                  have hrest : rest ∉ occupiedAddresses ⟨croot, cchildren⟩ := by
                    intro hrestIn
                    apply h
                    rw [occupiedAddresses_mk]
                    exact List.mem_cons.mpr (Or.inr (by
                      simpa using mem_occupiedChildrenAddresses_of_getElem?
                        children 0 slot ⟨croot, cchildren⟩ rest hLookup hrestIn))
                  have hnone := ih croot cchildren hrest
                  simpa using hnone

-- The height of a physical tree: one plus the maximum height of its children.  The two functions
-- are mutually recursive so that the well-founded recursion is structural in the spine of the
-- tree.
mutual
  /-- Intrinsic height: one for the root plus the maximum child height. -/
  def height {V : Type u} : PhysicalAtomTree V → Nat
    | ⟨_root, children⟩ => childrenHeights children + 1
  termination_by tree => sizeOf tree
  decreasing_by
    simp_wf

  /-- Maximum intrinsic height over a list of children (`0` for the empty list). -/
  def childrenHeights {V : Type u} : List (PhysicalAtomTree V) → Nat
    | [] => 0
    | child :: rest => max (height child) (childrenHeights rest)
  termination_by children => sizeOf children
  decreasing_by
    all_goals (simp_wf <;> omega)
end

/-! ### Unfolding equations

`height` and `childrenHeights` are defined by well-founded recursion, so their defining equations
are not definitional.  These lemmas record them explicitly. -/

/-- The defining equation of `height` at one concrete node. -/
theorem height_mk {V : Type u} (root : V) (children : List (PhysicalAtomTree V)) :
    height ⟨root, children⟩ = childrenHeights children + 1 := by
  rw [height]

/-- The defining equation of `childrenHeights` at the empty list. -/
theorem childrenHeights_nil {V : Type u} :
    childrenHeights ([] : List (PhysicalAtomTree V)) = 0 := by
  rw [childrenHeights]

/-- The defining equation of `childrenHeights` at a cons. -/
theorem childrenHeights_cons {V : Type u} (child : PhysicalAtomTree V)
    (rest : List (PhysicalAtomTree V)) :
    childrenHeights (child :: rest) = max (height child) (childrenHeights rest) := by
  rw [childrenHeights]

private theorem childrenHeights_le_of_mem {V : Type u}
    (children : List (PhysicalAtomTree V)) :
    ∀ (child : PhysicalAtomTree V), child ∈ children → height child ≤ childrenHeights children := by
  intro child hmem
  induction children with
  | nil => cases hmem
  | cons head tail ih =>
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · rw [childrenHeights_cons]
        exact le_max_left _ _
      · rw [childrenHeights_cons]
        exact (ih hmem').trans (le_max_right _ _)

/-- Every child has strictly smaller height than its parent; the structural fuel bound. -/
theorem height_child_le {V : Type u} (tree : PhysicalAtomTree V) :
    ∀ (child : PhysicalAtomTree V), child ∈ tree.children → height child < height tree := by
  intro child hmem
  cases tree with
  | mk root children =>
      rw [height_mk]
      exact Nat.lt_succ_of_le (childrenHeights_le_of_mem children child hmem)

end PhysicalAtomTree

/-! ## B. Totalized graph-only observation schedule -/

/-- **Totalized physical Rule-1a observation on a physical tree.**  The graph atomic number of the
atom living at a present position; zero at absent positions. -/
def physicalTreeAtomicNumberAt {V : Type u} [Fintype V] [DecidableEq V] (m : MoleculeGraph V)
    (tree : PhysicalAtomTree V) (position : List Nat) : Nat :=
  ((PhysicalAtomTree.subtreeAt? tree position).map fun node => m.atomZ node.root).getD 0

/-- **Totalized physical Rule-1b observation on a physical tree.**  The graph distance from the
fixed original `outerRoot` to the atom living at a present position; zero at absent positions.
Distance may legitimately be zero at a present position (the outer root itself); no positivity is
assumed.  This retains the explicit totalized real-own-sphere profile following the Hanson
2018–proposed outer-digraph totalization; it is never a fresh-root or depth-plus-one distance. -/
noncomputable def physicalTreeOuterRootDistanceAt {V : Type u} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (outerRoot : V) (tree : PhysicalAtomTree V) (position : List Nat) : Nat :=
  ((PhysicalAtomTree.subtreeAt? tree position).map fun node =>
    m.underlyingSimpleGraph.dist outerRoot node.root).getD 0

/-- **Totalized physical Rule-2 observation on a physical tree.**  The graph atom mass of the atom
living at a present position; zero at absent positions.  Mass may legitimately be zero at a
present position; no positivity is assumed. -/
def physicalTreeAtomMassAt {V : Type u} [Fintype V] [DecidableEq V] (m : MoleculeGraph V)
    (tree : PhysicalAtomTree V) (position : List Nat) : Nat :=
  ((PhysicalAtomTree.subtreeAt? tree position).map fun node => m.atomMass node.root).getD 0

/-! ## C. The independent rule-major outcome on physical trees -/

/-- **Graph-only physical rule-major outcome**, mirroring exactly the shape of
`physicalRuleMajorOutcome` (same rule-major nesting `A ∨ (B ∨ C)` and same per-column
first-difference structure), but on arbitrary physical trees without any actual tree, cursor, key,
reader or comparator data:

* equality: the physical Rule-1a, Rule-1b, and Rule-2 first differences all tie;
* strictness: either the physical Rule-1a first difference is strict, or Rule 1a ties and the
  physical Rule-1b first difference is strict, or Rule 1a and Rule 1b tie and the physical Rule-2
  first difference is strict.

Larger Z and mass win; smaller outer-root distance wins. -/
noncomputable def physicalTreeRuleMajorOutcome {V : Type u} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (outerRoot : V) (leftTree rightTree : PhysicalAtomTree V)
    (outcome : Ordering) : Prop :=
  match outcome with
  | Ordering.eq =>
      DeclarativeCIP.FirstDifferenceOutcome
        (fun position result =>
          DeclarativeCIP.DescendingNatOutcome
            (physicalTreeAtomicNumberAt m leftTree position)
            (physicalTreeAtomicNumberAt m rightTree position)
            result)
        Ordering.eq ∧
        DeclarativeCIP.FirstDifferenceOutcome
          (fun position result =>
            DeclarativeCIP.Rule1bDistanceOutcome
              (physicalTreeOuterRootDistanceAt m outerRoot leftTree position)
              (physicalTreeOuterRootDistanceAt m outerRoot rightTree position)
              result)
          Ordering.eq ∧
          DeclarativeCIP.FirstDifferenceOutcome
            (fun position result =>
              DeclarativeCIP.DescendingNatOutcome
                (physicalTreeAtomMassAt m leftTree position)
                (physicalTreeAtomMassAt m rightTree position)
                result)
            Ordering.eq
  | Ordering.lt =>
      DeclarativeCIP.FirstDifferenceOutcome
        (fun position result =>
          DeclarativeCIP.DescendingNatOutcome
            (physicalTreeAtomicNumberAt m leftTree position)
            (physicalTreeAtomicNumberAt m rightTree position)
            result)
        Ordering.lt ∨
        (DeclarativeCIP.FirstDifferenceOutcome
          (fun position result =>
            DeclarativeCIP.DescendingNatOutcome
              (physicalTreeAtomicNumberAt m leftTree position)
              (physicalTreeAtomicNumberAt m rightTree position)
              result)
          Ordering.eq ∧
          DeclarativeCIP.FirstDifferenceOutcome
            (fun position result =>
              DeclarativeCIP.Rule1bDistanceOutcome
                (physicalTreeOuterRootDistanceAt m outerRoot leftTree position)
                (physicalTreeOuterRootDistanceAt m outerRoot rightTree position)
                result)
            Ordering.lt) ∨
          (DeclarativeCIP.FirstDifferenceOutcome
            (fun position result =>
              DeclarativeCIP.DescendingNatOutcome
                (physicalTreeAtomicNumberAt m leftTree position)
                (physicalTreeAtomicNumberAt m rightTree position)
                result)
            Ordering.eq ∧
            DeclarativeCIP.FirstDifferenceOutcome
              (fun position result =>
                DeclarativeCIP.Rule1bDistanceOutcome
                  (physicalTreeOuterRootDistanceAt m outerRoot leftTree position)
                  (physicalTreeOuterRootDistanceAt m outerRoot rightTree position)
                  result)
              Ordering.eq ∧
              DeclarativeCIP.FirstDifferenceOutcome
                (fun position result =>
                  DeclarativeCIP.DescendingNatOutcome
                    (physicalTreeAtomMassAt m leftTree position)
                    (physicalTreeAtomMassAt m rightTree position)
                    result)
                Ordering.lt)
  | Ordering.gt =>
      DeclarativeCIP.FirstDifferenceOutcome
        (fun position result =>
          DeclarativeCIP.DescendingNatOutcome
            (physicalTreeAtomicNumberAt m leftTree position)
            (physicalTreeAtomicNumberAt m rightTree position)
            result)
        Ordering.gt ∨
        (DeclarativeCIP.FirstDifferenceOutcome
          (fun position result =>
            DeclarativeCIP.DescendingNatOutcome
              (physicalTreeAtomicNumberAt m leftTree position)
              (physicalTreeAtomicNumberAt m rightTree position)
              result)
          Ordering.eq ∧
          DeclarativeCIP.FirstDifferenceOutcome
            (fun position result =>
              DeclarativeCIP.Rule1bDistanceOutcome
                (physicalTreeOuterRootDistanceAt m outerRoot leftTree position)
                (physicalTreeOuterRootDistanceAt m outerRoot rightTree position)
                result)
            Ordering.gt) ∨
          (DeclarativeCIP.FirstDifferenceOutcome
            (fun position result =>
              DeclarativeCIP.DescendingNatOutcome
                (physicalTreeAtomicNumberAt m leftTree position)
                (physicalTreeAtomicNumberAt m rightTree position)
                result)
            Ordering.eq ∧
            DeclarativeCIP.FirstDifferenceOutcome
              (fun position result =>
                DeclarativeCIP.Rule1bDistanceOutcome
                  (physicalTreeOuterRootDistanceAt m outerRoot leftTree position)
                  (physicalTreeOuterRootDistanceAt m outerRoot rightTree position)
                  result)
              Ordering.eq ∧
              DeclarativeCIP.FirstDifferenceOutcome
                (fun position result =>
                  DeclarativeCIP.DescendingNatOutcome
                    (physicalTreeAtomMassAt m leftTree position)
                    (physicalTreeAtomMassAt m rightTree position)
                    result)
                Ordering.gt)

/-- The left physical tree is not junior to the right physical tree: it is senior or they tie. -/
noncomputable def physicalTreeRuleMajorNotLt {V : Type u} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (outerRoot : V) (leftTree rightTree : PhysicalAtomTree V) : Prop :=
  physicalTreeRuleMajorOutcome m outerRoot leftTree rightTree Ordering.gt ∨
    physicalTreeRuleMajorOutcome m outerRoot leftTree rightTree Ordering.eq

/-! ## D. Full incoming cuts and recursive physical descent -/

/-- `previous` excludes `w`: `w` may not be the previous vertex when one is given.  The previous
vertex may lie toward or away from the fixed outer root; it is only excluded from the neighbor
inventory. -/
def PhysicalCutExcludes {V : Type u} (previous : Option V) (w : V) : Prop :=
  ∀ p, previous = some p → w ≠ p

/-- **The full incoming-cut tree.**  `PhysicalFullCutTree m previous current tree` says the root
atom is `current`, the child-root atoms are pairwise distinct, child-root membership is exactly
`Adj current w ∧ w ≠ previous` (the exact adjacent-neighbor inventory excluding the previous
vertex), and every child recursively satisfies the corresponding incoming-cut relation from
`current`.  This is a pure graph relation: no actual cursor, key, reader, builder result or
comparator appears anywhere in it.

The recursive field is stated with equality-bound values for the child cut (`previous' = some
current`, `current' = child.root`) so that the kernel accepts the strictly positive nested
occurrence; `PhysicalFullCutTree.children_some` below is the convenient instantiated form. -/
inductive PhysicalFullCutTree {V : Type u} [Fintype V] [DecidableEq V] (m : MoleculeGraph V) :
    Option V → V → PhysicalAtomTree V → Prop where
  | mk (previous : Option V) (current : V) (tree : PhysicalAtomTree V)
      (root : tree.root = current)
      (nodup : (tree.children.map fun child : PhysicalAtomTree V => child.root).Nodup)
      (inventory : ∀ w : V,
        w ∈ tree.children.map (fun child : PhysicalAtomTree V => child.root) ↔
          m.Adj current w ∧ PhysicalCutExcludes previous w)
      (children : ∀ (child : PhysicalAtomTree V), child ∈ tree.children →
        ∀ (previous' : Option V), previous' = some current →
        ∀ (current' : V), current' = child.root →
        PhysicalFullCutTree m previous' current' child) :
      PhysicalFullCutTree m previous current tree

/-- The recursive child cut of a full incoming-cut tree, with the child's previous and current
instantiated: every child satisfies the incoming-cut relation from `current` at `child.root`. -/
theorem PhysicalFullCutTree.children_some {V : Type u} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) {previous : Option V} {current : V} {tree : PhysicalAtomTree V}
    (full : PhysicalFullCutTree m previous current tree)
    {child : PhysicalAtomTree V} (hmem : child ∈ tree.children) :
    PhysicalFullCutTree m (some current) child.root child := by
  cases full with
  | mk _previous _current _tree root nodup inventory children =>
      exact children child hmem (some current) rfl child.root rfl

/-- **Recursive physical sibling descending order.**  Every sibling list is descending for the
physical rule-major outcome (each consecutive pair is not junior left-to-right) and the property
recurses into every child.  This is the independent ordering constraint on child lists; it never
mentions the runtime comparator. -/
inductive PhysicalTreeSiblingDescending {V : Type u} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (outerRoot : V) : PhysicalAtomTree V → Prop where
  | mk (tree : PhysicalAtomTree V)
      (siblings : tree.children.Pairwise fun left right =>
        physicalTreeRuleMajorNotLt m outerRoot left right)
      (children : ∀ child ∈ tree.children,
        PhysicalTreeSiblingDescending m outerRoot child) :
      PhysicalTreeSiblingDescending m outerRoot tree

/-- **Physical admissibility of an incoming-cut tree at a fixed outer root.**  The conjunction of
the full incoming-cut relation and the independent recursive physical descent. -/
structure PhysicalIncomingCutAdmissible {V : Type u} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (outerRoot : V) (previous : Option V) (current : V)
    (tree : PhysicalAtomTree V) : Prop where
  full : PhysicalFullCutTree m previous current tree
  descending : PhysicalTreeSiblingDescending m outerRoot tree

/-- **The canonical physical outcome of two incoming cuts at a fixed outer root.**  There exist
admissible physical expansions of both cuts, and every pair of admissible expansions realizes the
same `outcome` for the physical rule-major outcome. -/
noncomputable def PhysicalTreeCanonicalOutcome {V : Type u} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (outerRoot : V) (previousLeft previousRight : Option V)
    (currentLeft currentRight : V) (outcome : Ordering) : Prop :=
  (∃ leftTree : PhysicalAtomTree V,
    PhysicalIncomingCutAdmissible m outerRoot previousLeft currentLeft leftTree) ∧
  (∃ rightTree : PhysicalAtomTree V,
    PhysicalIncomingCutAdmissible m outerRoot previousRight currentRight rightTree) ∧
  ∀ (leftTree rightTree : PhysicalAtomTree V),
    PhysicalIncomingCutAdmissible m outerRoot previousLeft currentLeft leftTree →
    PhysicalIncomingCutAdmissible m outerRoot previousRight currentRight rightTree →
    physicalTreeRuleMajorOutcome m outerRoot leftTree rightTree outcome

/-! ## E. Single-valuedness and totality of the physical outcome -/

private theorem firstDifferenceColumnFunctional
    {observation : List Nat → Ordering → Prop}
    {first second : Ordering} (hne : first ≠ second)
    (hfirst : DeclarativeCIP.FirstDifferenceOutcome observation first)
    (hsecond : DeclarativeCIP.FirstDifferenceOutcome observation second)
    (localFunctional : ∀ position first second,
      observation position first → observation position second → first = second) :
    False := by
  exact hne (DeclarativeCIP.FirstDifferenceOutcome.functional localFunctional hfirst hsecond)

private theorem physicalTreeRule1aColumnFunctional {V : Type u} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (leftTree rightTree : PhysicalAtomTree V)
    {first second : Ordering} (hne : first ≠ second)
    (hfirst : DeclarativeCIP.FirstDifferenceOutcome
      (fun position result => DeclarativeCIP.DescendingNatOutcome
        (physicalTreeAtomicNumberAt m leftTree position)
        (physicalTreeAtomicNumberAt m rightTree position) result) first)
    (hsecond : DeclarativeCIP.FirstDifferenceOutcome
      (fun position result => DeclarativeCIP.DescendingNatOutcome
        (physicalTreeAtomicNumberAt m leftTree position)
        (physicalTreeAtomicNumberAt m rightTree position) result) second) :
    False := by
  exact firstDifferenceColumnFunctional hne hfirst hsecond
    (fun position first second hfirst hsecond =>
      DeclarativeCIP.DescendingNatOutcome.functional hfirst hsecond)

private theorem physicalTreeRule1bColumnFunctional {V : Type u} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (outerRoot : V) (leftTree rightTree : PhysicalAtomTree V)
    {first second : Ordering} (hne : first ≠ second)
    (hfirst : DeclarativeCIP.FirstDifferenceOutcome
      (fun position result => DeclarativeCIP.Rule1bDistanceOutcome
        (physicalTreeOuterRootDistanceAt m outerRoot leftTree position)
        (physicalTreeOuterRootDistanceAt m outerRoot rightTree position) result) first)
    (hsecond : DeclarativeCIP.FirstDifferenceOutcome
      (fun position result => DeclarativeCIP.Rule1bDistanceOutcome
        (physicalTreeOuterRootDistanceAt m outerRoot leftTree position)
        (physicalTreeOuterRootDistanceAt m outerRoot rightTree position) result) second) :
    False := by
  exact firstDifferenceColumnFunctional hne hfirst hsecond
    (fun position first second hfirst hsecond =>
      DeclarativeCIP.Rule1bDistanceOutcome.functional hfirst hsecond)

private theorem physicalTreeRule2ColumnFunctional {V : Type u} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (leftTree rightTree : PhysicalAtomTree V)
    {first second : Ordering} (hne : first ≠ second)
    (hfirst : DeclarativeCIP.FirstDifferenceOutcome
      (fun position result => DeclarativeCIP.DescendingNatOutcome
        (physicalTreeAtomMassAt m leftTree position)
        (physicalTreeAtomMassAt m rightTree position) result) first)
    (hsecond : DeclarativeCIP.FirstDifferenceOutcome
      (fun position result => DeclarativeCIP.DescendingNatOutcome
        (physicalTreeAtomMassAt m leftTree position)
        (physicalTreeAtomMassAt m rightTree position) result) second) :
    False := by
  exact firstDifferenceColumnFunctional hne hfirst hsecond
    (fun position first second hfirst hsecond =>
      DeclarativeCIP.DescendingNatOutcome.functional hfirst hsecond)

private theorem ordering_ne_lt_eq : Ordering.lt ≠ Ordering.eq := by intro h; cases h
private theorem ordering_ne_lt_gt : Ordering.lt ≠ Ordering.gt := by intro h; cases h
private theorem ordering_ne_eq_lt : Ordering.eq ≠ Ordering.lt := by intro h; cases h
private theorem ordering_ne_eq_gt : Ordering.eq ≠ Ordering.gt := by intro h; cases h
private theorem ordering_ne_gt_lt : Ordering.gt ≠ Ordering.lt := by intro h; cases h
private theorem ordering_ne_gt_eq : Ordering.gt ≠ Ordering.eq := by intro h; cases h

/-- The physical rule-major outcome is single-valued: each pair of physical trees realizes at
most one outcome. -/
theorem physicalTreeRuleMajorOutcome_functional {V : Type u} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (outerRoot : V) (leftTree rightTree : PhysicalAtomTree V)
    {first second : Ordering}
    (hfirst : physicalTreeRuleMajorOutcome m outerRoot leftTree rightTree first)
    (hsecond : physicalTreeRuleMajorOutcome m outerRoot leftTree rightTree second) :
    first = second := by
  cases first <;> cases second
  all_goals try rfl
  · rcases hfirst with h1aLt | ⟨h1aEq, h1bLt⟩ | ⟨h1aEq, h1bEq, h2Lt⟩
    · rcases hsecond with ⟨h1aEq', h1bEq', h2Eq'⟩
      cases physicalTreeRule1aColumnFunctional m leftTree rightTree ordering_ne_lt_eq h1aLt h1aEq'
    · rcases hsecond with ⟨h1aEq', h1bEq', h2Eq'⟩
      cases physicalTreeRule1bColumnFunctional m outerRoot leftTree rightTree ordering_ne_lt_eq
        h1bLt h1bEq'
    · rcases hsecond with ⟨h1aEq', h1bEq', h2Eq'⟩
      cases physicalTreeRule2ColumnFunctional m leftTree rightTree ordering_ne_lt_eq h2Lt h2Eq'
  · rcases hfirst with h1aLt | ⟨h1aEq, h1bLt⟩ | ⟨h1aEq, h1bEq, h2Lt⟩
    · rcases hsecond with h1aGt | ⟨h1aEq', h1bGt⟩ | ⟨h1aEq', h1bEq', h2Gt⟩
      · cases physicalTreeRule1aColumnFunctional m leftTree rightTree ordering_ne_lt_gt h1aLt h1aGt
      · cases physicalTreeRule1aColumnFunctional m leftTree rightTree ordering_ne_lt_eq h1aLt h1aEq'
      · cases physicalTreeRule1aColumnFunctional m leftTree rightTree ordering_ne_lt_eq h1aLt h1aEq'
    · rcases hsecond with h1aGt | ⟨h1aEq', h1bGt⟩ | ⟨h1aEq', h1bEq', h2Gt⟩
      · cases physicalTreeRule1aColumnFunctional m leftTree rightTree ordering_ne_eq_gt h1aEq h1aGt
      · cases physicalTreeRule1bColumnFunctional m outerRoot leftTree rightTree ordering_ne_lt_gt
          h1bLt h1bGt
      · cases physicalTreeRule1bColumnFunctional m outerRoot leftTree rightTree ordering_ne_lt_eq
          h1bLt h1bEq'
    · rcases hsecond with h1aGt | ⟨h1aEq', h1bGt⟩ | ⟨h1aEq', h1bEq', h2Gt⟩
      · cases physicalTreeRule1aColumnFunctional m leftTree rightTree ordering_ne_eq_gt h1aEq h1aGt
      · cases physicalTreeRule1bColumnFunctional m outerRoot leftTree rightTree ordering_ne_eq_gt
          h1bEq h1bGt
      · cases physicalTreeRule2ColumnFunctional m leftTree rightTree ordering_ne_lt_gt h2Lt h2Gt
  · rcases hsecond with h1aLt | ⟨h1aEq, h1bLt⟩ | ⟨h1aEq, h1bEq, h2Lt⟩
    · rcases hfirst with ⟨h1aEq', h1bEq', h2Eq'⟩
      cases physicalTreeRule1aColumnFunctional m leftTree rightTree ordering_ne_lt_eq h1aLt h1aEq'
    · rcases hfirst with ⟨h1aEq', h1bEq', h2Eq'⟩
      cases physicalTreeRule1bColumnFunctional m outerRoot leftTree rightTree ordering_ne_lt_eq
        h1bLt h1bEq'
    · rcases hfirst with ⟨h1aEq', h1bEq', h2Eq'⟩
      cases physicalTreeRule2ColumnFunctional m leftTree rightTree ordering_ne_lt_eq h2Lt h2Eq'
  · rcases hsecond with h1aGt | ⟨h1aEq, h1bGt⟩ | ⟨h1aEq, h1bEq, h2Gt⟩
    · rcases hfirst with ⟨h1aEq', h1bEq', h2Eq'⟩
      cases physicalTreeRule1aColumnFunctional m leftTree rightTree ordering_ne_eq_gt h1aEq' h1aGt
    · rcases hfirst with ⟨h1aEq', h1bEq', h2Eq'⟩
      cases physicalTreeRule1bColumnFunctional m outerRoot leftTree rightTree ordering_ne_eq_gt
        h1bEq' h1bGt
    · rcases hfirst with ⟨h1aEq', h1bEq', h2Eq'⟩
      cases physicalTreeRule2ColumnFunctional m leftTree rightTree ordering_ne_eq_gt h2Eq' h2Gt
  · rcases hfirst with h1aGt | ⟨h1aEq, h1bGt⟩ | ⟨h1aEq, h1bEq, h2Gt⟩
    · rcases hsecond with h1aLt | ⟨h1aEq', h1bLt⟩ | ⟨h1aEq', h1bEq', h2Lt⟩
      · cases physicalTreeRule1aColumnFunctional m leftTree rightTree ordering_ne_gt_lt h1aGt h1aLt
      · cases physicalTreeRule1aColumnFunctional m leftTree rightTree ordering_ne_gt_eq h1aGt h1aEq'
      · cases physicalTreeRule1aColumnFunctional m leftTree rightTree ordering_ne_gt_eq h1aGt h1aEq'
    · rcases hsecond with h1aLt | ⟨h1aEq', h1bLt⟩ | ⟨h1aEq', h1bEq', h2Lt⟩
      · cases physicalTreeRule1aColumnFunctional m leftTree rightTree ordering_ne_eq_lt h1aEq h1aLt
      · cases physicalTreeRule1bColumnFunctional m outerRoot leftTree rightTree ordering_ne_gt_lt
          h1bGt h1bLt
      · cases physicalTreeRule1bColumnFunctional m outerRoot leftTree rightTree ordering_ne_gt_eq
          h1bGt h1bEq'
    · rcases hsecond with h1aLt | ⟨h1aEq', h1bLt⟩ | ⟨h1aEq', h1bEq', h2Lt⟩
      · cases physicalTreeRule1aColumnFunctional m leftTree rightTree ordering_ne_eq_lt h1aEq h1aLt
      · cases physicalTreeRule1bColumnFunctional m outerRoot leftTree rightTree ordering_ne_eq_lt
          h1bEq h1bLt
      · cases physicalTreeRule2ColumnFunctional m leftTree rightTree ordering_ne_gt_lt h2Gt h2Lt
  · rcases hfirst with h1aGt | ⟨h1aEq, h1bGt⟩ | ⟨h1aEq, h1bEq, h2Gt⟩
    · rcases hsecond with ⟨h1aEq', h1bEq', h2Eq'⟩
      cases physicalTreeRule1aColumnFunctional m leftTree rightTree ordering_ne_gt_eq h1aGt h1aEq'
    · rcases hsecond with ⟨h1aEq', h1bEq', h2Eq'⟩
      cases physicalTreeRule1bColumnFunctional m outerRoot leftTree rightTree ordering_ne_gt_eq
        h1bGt h1bEq'
    · rcases hsecond with ⟨h1aEq', h1bEq', h2Eq'⟩
      cases physicalTreeRule2ColumnFunctional m leftTree rightTree ordering_ne_gt_eq h2Gt h2Eq'

/-- The physical rule-major outcome is total on finite physical trees: some outcome is always
realized, with the finite support of occupied addresses. -/
theorem physicalTreeRuleMajorOutcome_total {V : Type u} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (outerRoot : V) (leftTree rightTree : PhysicalAtomTree V) :
    ∃ outcome, physicalTreeRuleMajorOutcome m outerRoot leftTree rightTree outcome := by
  classical
  let support : Finset (List Nat) :=
    (PhysicalAtomTree.occupiedAddresses leftTree).toFinset ∪
      (PhysicalAtomTree.occupiedAddresses rightTree).toFinset
  obtain ⟨outcome1a, h1a⟩ := DeclarativeCIP.FirstDifferenceOutcome.total_of_finite_support
    (fun position => DeclarativeCIP.DescendingNatOutcome.total
      (physicalTreeAtomicNumberAt m leftTree position)
      (physicalTreeAtomicNumberAt m rightTree position))
    support
    (by
      intro position hOutside
      have hleft : PhysicalAtomTree.subtreeAt? leftTree position = none :=
        PhysicalAtomTree.subtreeAt?_none_of_not_mem_occupied leftTree (by
          intro hIn
          exact hOutside (Finset.mem_union.mpr (Or.inl (List.mem_toFinset.mpr hIn))))
      have hright : PhysicalAtomTree.subtreeAt? rightTree position = none :=
        PhysicalAtomTree.subtreeAt?_none_of_not_mem_occupied rightTree (by
          intro hIn
          exact hOutside (Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr hIn))))
      have hleftObs : physicalTreeAtomicNumberAt m leftTree position = 0 := by
        unfold physicalTreeAtomicNumberAt
        rw [hleft]
        rfl
      have hrightObs : physicalTreeAtomicNumberAt m rightTree position = 0 := by
        unfold physicalTreeAtomicNumberAt
        rw [hright]
        rfl
      rw [hleftObs, hrightObs]
      exact DeclarativeCIP.DescendingNatOutcome.eq rfl)
  obtain ⟨outcome1b, h1b⟩ := DeclarativeCIP.FirstDifferenceOutcome.total_of_finite_support
    (fun position => DeclarativeCIP.Rule1bDistanceOutcome.total
      (physicalTreeOuterRootDistanceAt m outerRoot leftTree position)
      (physicalTreeOuterRootDistanceAt m outerRoot rightTree position))
    support
    (by
      intro position hOutside
      have hleft : PhysicalAtomTree.subtreeAt? leftTree position = none :=
        PhysicalAtomTree.subtreeAt?_none_of_not_mem_occupied leftTree (by
          intro hIn
          exact hOutside (Finset.mem_union.mpr (Or.inl (List.mem_toFinset.mpr hIn))))
      have hright : PhysicalAtomTree.subtreeAt? rightTree position = none :=
        PhysicalAtomTree.subtreeAt?_none_of_not_mem_occupied rightTree (by
          intro hIn
          exact hOutside (Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr hIn))))
      have hleftObs : physicalTreeOuterRootDistanceAt m outerRoot leftTree position = 0 := by
        unfold physicalTreeOuterRootDistanceAt
        rw [hleft]
        rfl
      have hrightObs : physicalTreeOuterRootDistanceAt m outerRoot rightTree position = 0 := by
        unfold physicalTreeOuterRootDistanceAt
        rw [hright]
        rfl
      rw [hleftObs, hrightObs]
      exact DeclarativeCIP.Rule1bDistanceOutcome.eq rfl)
  obtain ⟨outcome2, h2⟩ := DeclarativeCIP.FirstDifferenceOutcome.total_of_finite_support
    (fun position => DeclarativeCIP.DescendingNatOutcome.total
      (physicalTreeAtomMassAt m leftTree position)
      (physicalTreeAtomMassAt m rightTree position))
    support
    (by
      intro position hOutside
      have hleft : PhysicalAtomTree.subtreeAt? leftTree position = none :=
        PhysicalAtomTree.subtreeAt?_none_of_not_mem_occupied leftTree (by
          intro hIn
          exact hOutside (Finset.mem_union.mpr (Or.inl (List.mem_toFinset.mpr hIn))))
      have hright : PhysicalAtomTree.subtreeAt? rightTree position = none :=
        PhysicalAtomTree.subtreeAt?_none_of_not_mem_occupied rightTree (by
          intro hIn
          exact hOutside (Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr hIn))))
      have hleftObs : physicalTreeAtomMassAt m leftTree position = 0 := by
        unfold physicalTreeAtomMassAt
        rw [hleft]
        rfl
      have hrightObs : physicalTreeAtomMassAt m rightTree position = 0 := by
        unfold physicalTreeAtomMassAt
        rw [hright]
        rfl
      rw [hleftObs, hrightObs]
      exact DeclarativeCIP.DescendingNatOutcome.eq rfl)
  cases outcome1a with
  | lt => exact ⟨Ordering.lt, Or.inl h1a⟩
  | gt => exact ⟨Ordering.gt, Or.inl h1a⟩
  | eq =>
      cases outcome1b with
      | lt => exact ⟨Ordering.lt, Or.inr (Or.inl ⟨h1a, h1b⟩)⟩
      | gt => exact ⟨Ordering.gt, Or.inr (Or.inl ⟨h1a, h1b⟩)⟩
      | eq =>
          cases outcome2 with
          | lt => exact ⟨Ordering.lt, Or.inr (Or.inr ⟨h1a, h1b, h2⟩)⟩
          | gt => exact ⟨Ordering.gt, Or.inr (Or.inr ⟨h1a, h1b, h2⟩)⟩
          | eq => exact ⟨Ordering.eq, ⟨h1a, h1b, h2⟩⟩

/-! ## F. Erasure of actual full-cut trees into the independent physical inventory -/

mutual
  /-- Erase every actual cursor and comparison decoration of a realized decorated occurrence tree,
  keeping only the physical atom at each node.  The root atom is the physical atom observed by the
  node's actual source cursor; children are erased recursively in the actual sorted sibling order. -/
  def physicalErasure (singleBonded : input.moleculeGraph.SimpleBonded)
      (acyclic : input.moleculeGraph.Acyclic) :
      LocalizedCumulativeDecoratedTree input carrierFuel → PhysicalAtomTree input.Atom
    | ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩ =>
        { root := nodeAtom singleBonded acyclic
            ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩
          children := physicalErasureChildren singleBonded acyclic children }
    termination_by tree => sizeOf tree
    decreasing_by
      simp_wf

  /-- Erase every actual cursor from a list of decorated trees. -/
  def physicalErasureChildren (singleBonded : input.moleculeGraph.SimpleBonded)
      (acyclic : input.moleculeGraph.Acyclic) :
      List (LocalizedCumulativeDecoratedTree input carrierFuel) →
        List (PhysicalAtomTree input.Atom)
    | [] => []
    | child :: children =>
        physicalErasure singleBonded acyclic child ::
          physicalErasureChildren singleBonded acyclic children
    termination_by children => sizeOf children
    decreasing_by
      all_goals (simp_wf <;> omega)
end

/-- The defining equation of `physicalErasure` at one concrete tree. -/
theorem physicalErasure_def (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic) (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    physicalErasure singleBonded acyclic tree =
      { root := nodeAtom singleBonded acyclic tree
        children := physicalErasureChildren singleBonded acyclic tree.children } := by
  cases tree with
  | mk source atomicNumber rule1bDistance isotopeMass label children =>
      rw [physicalErasure]

/-- List erasure is pointwise tree erasure. -/
theorem physicalErasureChildren_eq_map (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    physicalErasureChildren singleBonded acyclic children =
      children.map (fun child => physicalErasure singleBonded acyclic child) := by
  induction children with
  | nil => simp [physicalErasureChildren]
  | cons child rest ih => simp [physicalErasureChildren, ih]

/-- Erasure commutes with subtree lookup: the physical subtree at a position of the erased tree is
the erasure of the actual subtree at that position. -/
theorem subtreeAt?_physicalErasure (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (position : List Nat) :
    (subtreeAt? tree position).map (fun node => physicalErasure singleBonded acyclic node) =
      PhysicalAtomTree.subtreeAt? (physicalErasure singleBonded acyclic tree) position := by
  induction position generalizing tree with
  | nil => rfl
  | cons slot rest ih =>
      rw [subtreeAt?_cons, PhysicalAtomTree.subtreeAt?_cons,
        physicalErasure_def, physicalErasureChildren_eq_map]
      cases hLookup : tree.children[slot]? with
      | none => simp [List.getElem?_map, hLookup]
      | some child => simpa [List.getElem?_map, hLookup] using ih child

/-- The totalized physical Rule-1a observation on an erased tree is the actual physical
Rule-1a observation of the realized tree. -/
theorem physicalTreeAtomicNumberAt_eq_erasure (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (position : List Nat) :
    physicalTreeAtomicNumberAt input.moleculeGraph (physicalErasure singleBonded acyclic tree)
        position =
      physicalAtomicNumberAt singleBonded acyclic tree position := by
  unfold physicalTreeAtomicNumberAt physicalAtomicNumberAt
  rw [← subtreeAt?_physicalErasure singleBonded acyclic tree position]
  simp only [Option.map_map]
  congr 1
  congr 1
  funext node
  simp [physicalErasure_def]

/-- The totalized physical Rule-1b observation on an erased tree is the actual physical
Rule-1b observation of the realized tree, at the same fixed original `outerRoot`. -/
theorem physicalTreeOuterRootDistanceAt_eq_erasure
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
    (outerRoot : input.Atom) (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (position : List Nat) :
    physicalTreeOuterRootDistanceAt input.moleculeGraph outerRoot
        (physicalErasure singleBonded acyclic tree) position =
      physicalOuterRootDistanceAt singleBonded acyclic outerRoot tree position := by
  unfold physicalTreeOuterRootDistanceAt physicalOuterRootDistanceAt
  rw [← subtreeAt?_physicalErasure singleBonded acyclic tree position]
  simp only [Option.map_map]
  congr 1
  congr 1
  funext node
  simp [physicalErasure_def]

/-- The totalized physical Rule-2 observation on an erased tree is the actual physical
Rule-2 observation of the realized tree. -/
theorem physicalTreeAtomMassAt_eq_erasure (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (position : List Nat) :
    physicalTreeAtomMassAt input.moleculeGraph (physicalErasure singleBonded acyclic tree)
        position =
      physicalAtomMassAt singleBonded acyclic tree position := by
  unfold physicalTreeAtomMassAt physicalAtomMassAt
  rw [← subtreeAt?_physicalErasure singleBonded acyclic tree position]
  simp only [Option.map_map]
  congr 1
  congr 1
  funext node
  simp [physicalErasure_def]

/-- The graph-only physical rule-major outcome of two erased realized trees is exactly the actual
physical rule-major outcome of the two realized trees, at the same fixed original `outerRoot` and
every `Ordering`. -/
theorem physicalTreeRuleMajorOutcome_eq_erasure
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
    (outerRoot : input.Atom) (leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (outcome : Ordering) :
    physicalTreeRuleMajorOutcome input.moleculeGraph outerRoot
        (physicalErasure singleBonded acyclic leftTree)
        (physicalErasure singleBonded acyclic rightTree) outcome ↔
      physicalRuleMajorOutcome singleBonded acyclic outerRoot leftTree rightTree outcome := by
  cases outcome <;>
    simp [physicalTreeRuleMajorOutcome, physicalRuleMajorOutcome,
      physicalTreeAtomicNumberAt_eq_erasure, physicalTreeOuterRootDistanceAt_eq_erasure,
      physicalTreeAtomMassAt_eq_erasure]

/-- The graph-only physical non-junior relation of two erased realized trees is exactly the
actual physical non-junior relation of the two realized trees, at the same fixed original
`outerRoot`. -/
theorem physicalTreeRuleMajorNotLt_eq_erasure
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
    (outerRoot : input.Atom) (leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    physicalTreeRuleMajorNotLt input.moleculeGraph outerRoot
        (physicalErasure singleBonded acyclic leftTree)
        (physicalErasure singleBonded acyclic rightTree) ↔
      physicalRuleMajorNotLt singleBonded acyclic leftTree rightTree outerRoot := by
  simp [physicalTreeRuleMajorNotLt, physicalRuleMajorNotLt,
    physicalTreeRuleMajorOutcome_eq_erasure]

/-- Erasure preserves the recursive physical sibling descending order. -/
theorem physicalTreeSiblingDescending_of_erasure
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
    (outerRoot : input.Atom) {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (descending : PhysicalSiblingDescending singleBonded acyclic outerRoot tree) :
    PhysicalTreeSiblingDescending input.moleculeGraph outerRoot
      (physicalErasure singleBonded acyclic tree) := by
  induction descending with
  | mk tree siblings _childrenRoot children ih =>
      rw [physicalErasure_def]
      apply PhysicalTreeSiblingDescending.mk
      · rw [physicalErasureChildren_eq_map]
        refine List.pairwise_map.mpr ?_
        exact List.Pairwise.imp (by
          intro left right h
          exact (physicalTreeRuleMajorNotLt_eq_erasure singleBonded acyclic outerRoot left right).2 h)
          siblings
      · intro child hmem
        rw [physicalErasureChildren_eq_map] at hmem
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hmem
        exact ih c hc








theorem physicalErasure_full
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input r tree)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (previous : Option input.Atom)
    (previousEq : tree.source.previous?.bind (fun p => p.1.node.current?) = previous)
    (current : input.Atom)
    (currentEq : nodeAtom singleBonded acyclic tree = current) :
    PhysicalFullCutTree input.moleculeGraph previous current
      (physicalErasure singleBonded acyclic tree) := by
  induction realizes generalizing previous current with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize ih =>
      have treeRealizes : LocalizedCumulativeTreeRealizes input r
          (localizedRootTree input cursor (r cursor) sortedChildren) :=
        LocalizedCumulativeTreeRealizes.mk cursor children sortedChildren
          childrenComputed sourcePerm childrenRealize
      have hchild_sources : ∀ c, (∃ child ∈ sortedChildren, child.source = c) ↔ c ∈ children := by
        intro c
        have hm : c ∈ sortedChildren.map (fun t => t.source) ↔ c ∈ children := sourcePerm.mem_iff
        exact (List.mem_map).symm.trans hm
      have hnode_mem_iff : ∀ w,
          w ∈ sortedChildren.map (fun child => nodeAtom singleBonded acyclic child) ↔
            ∃ c ∈ children, c.occurrence.1.node.current? = some w := by
        intro w
        rw [List.mem_map]
        constructor
        · rintro ⟨child, hmem, hEq⟩
          refine ⟨child.source, (hchild_sources child.source).mp ⟨child, hmem, rfl⟩, ?_⟩
          rw [nodeAtom_spec singleBonded acyclic child, hEq]
        · rintro ⟨c, hc, hObs⟩
          obtain ⟨child, hmem, hsource⟩ := (hchild_sources c).mpr hc
          refine ⟨child, hmem, ?_⟩
          have spec := nodeAtom_spec singleBonded acyclic child
          rw [hsource] at spec
          exact Option.some.inj (spec.symm.trans hObs)
      have hObserved : cursor.occurrence.1.node.current? =
          some (nodeAtom singleBonded acyclic
            (localizedRootTree input cursor (r cursor) sortedChildren)) :=
        nodeAtom_spec singleBonded acyclic (localizedRootTree input cursor (r cursor) sortedChildren)
      have hroots : sortedChildren.map (fun child => (physicalErasure singleBonded acyclic child).root) =
          sortedChildren.map (fun child => nodeAtom singleBonded acyclic child) := by
        apply List.map_congr_left
        intro child _hmem
        rw [physicalErasure_def]
      rw [physicalErasure_def]
      apply PhysicalFullCutTree.mk
      · exact currentEq
      · rw [physicalErasureChildren_eq_map, List.map_map]
        change (sortedChildren.map (fun child => (physicalErasure singleBonded acyclic child).root)).Nodup
        rw [hroots]
        apply List.nodup_iff_injective_getElem.mpr
        intro i j same
        apply Fin.ext
        apply child_atom_injective singleBonded acyclic treeRealizes
          (by simpa using i.2) (by simpa using j.2)
        simpa [List.getElem_map] using same
      · intro w
        rw [physicalErasureChildren_eq_map, List.map_map]
        change w ∈ sortedChildren.map (fun child => (physicalErasure singleBonded acyclic child).root) ↔
          input.moleculeGraph.Adj current w ∧ PhysicalCutExcludes previous w
        rw [hroots, hnode_mem_iff w]
        cases hPrev : cursor.previous? with
        | none =>
            have hprevious : previous = none := by
              simpa [localizedRootTree, hPrev] using previousEq.symm
            subst hprevious
            have hrootIff := input.localizedRerootChildren?_current_iff_adjacent_root
              singleBonded acyclic enough cursor hPrev hObserved children childrenComputed
            rw [(hrootIff w), currentEq]
            simp [PhysicalCutExcludes]
        | some previousOcc =>
            have hprevious : previous = previousOcc.1.node.current? := by
              simpa [localizedRootTree, hPrev] using previousEq.symm
            subst hprevious
            have hValid : cursor.occurrence.1 ∈
                input.localizedRerootNeighborFrames (fuel := carrierFuel) previousOcc.1 := by
              simpa [localizedRootTree, LocalizedRerootCursorValid, hPrev] using valid
            have hSameRoot : cursor.occurrence.1.root = previousOcc.1.root :=
              ((input.mem_localizedRerootNeighborFrames_iff previousOcc.1 cursor.occurrence.1).mp
                hValid).2.1
            obtain ⟨pAtom, _path, pObserved, _head, _provenance, _simple, _support,
              _penultimate⟩ :=
              input.carrierOccurrence_realPath singleBonded acyclic previousOcc
            have hprevIff := input.localizedRerootChildren?_current_iff_adjacent_of_previous
              singleBonded acyclic enough cursor previousOcc hPrev hSameRoot hObserved pObserved
              children childrenComputed
            rw [(hprevIff w), currentEq, pObserved]
            simp [PhysicalCutExcludes]
      · intro child hchild previous' hprev' current' hcur'
        rw [physicalErasureChildren_eq_map] at hchild
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hchild
        obtain ⟨slot, lookup⟩ := List.mem_iff_getElem?.mp hc
        have hroot : (physicalErasure singleBonded acyclic c).root =
            nodeAtom singleBonded acyclic c := by
          rw [physicalErasure_def]
        rw [hprev', hcur', hroot]
        refine ih c hc (child_valid_of_child treeRealizes lookup) (some current) ?_
          (nodeAtom singleBonded acyclic c) rfl
        rw [child_previous_of_child treeRealizes lookup]
        change (localizedRootTree input cursor (r cursor) sortedChildren).source.occurrence.1.node.current? =
          some current
        rw [nodeAtom_spec singleBonded acyclic (localizedRootTree input cursor (r cursor) sortedChildren)]
        rw [currentEq]




theorem physicalIncomingCutAdmissible_of_erasure
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input r tree)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (outerRoot : input.Atom)
    (descending : PhysicalSiblingDescending singleBonded acyclic outerRoot tree)
    (previous : Option input.Atom)
    (previousEq : tree.source.previous?.bind (fun p => p.1.node.current?) = previous)
    (current : input.Atom)
    (currentEq : nodeAtom singleBonded acyclic tree = current) :
    PhysicalIncomingCutAdmissible input.moleculeGraph outerRoot previous current
      (physicalErasure singleBonded acyclic tree) :=
  { full := physicalErasure_full enough singleBonded acyclic realizes valid previous previousEq
      current currentEq
    descending := physicalTreeSiblingDescending_of_erasure singleBonded acyclic outerRoot
      descending }

/-! ## G. Lift: every independent physical full-cut tree is realized at a valid actual cursor -/

section PhysicalLift

/-- The physical atom currently observed at an actual cursor.  Existence is supplied by the real
carrier provenance (`carrierOccurrence_realPath`), never assumed; this is the cursor-level twin of
`nodeAtom`, and it is the observed atom of every `localizedRootTree` rooted at the cursor. -/
def cursorAtom (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (cursor : input.LocalizedRerootCursor carrierFuel) : input.Atom :=
  (cursor.occurrence.1.node.current?).get (by
    obtain ⟨current, _path, observed, _head, _provenance, _simple, _support, _penultimate⟩ :=
      input.carrierOccurrence_realPath singleBonded acyclic cursor.occurrence
    exact Option.isSome_iff_exists.mpr ⟨current, observed⟩)

/-- The defining equation of `cursorAtom`: the cursor observes its own current atom. -/
theorem cursorAtom_spec (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    cursor.occurrence.1.node.current? = some (cursorAtom singleBonded acyclic cursor) :=
  Option.eq_some_of_isSome _

/-- A cursor observing a given atom carries that atom. -/
theorem cursorAtom_eq_of_observed (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {cursor : input.LocalizedRerootCursor carrierFuel} {atom : input.Atom}
    (observed : cursor.occurrence.1.node.current? = some atom) :
    cursorAtom singleBonded acyclic cursor = atom :=
  Option.some.inj ((cursorAtom_spec singleBonded acyclic cursor).symm.trans observed)






private theorem physicalExecutableChild_iff
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous) :
    ∀ w : input.Atom,
      (∃ c ∈ input.executableLocalizedRerootChildren cursor,
        c.occurrence.1.node.current? = some w) ↔
        input.moleculeGraph.Adj (cursorAtom singleBonded acyclic cursor) w ∧
          PhysicalCutExcludes previous w := by
  intro w
  cases hPrev : cursor.previous? with
  | none =>
      have hprevious : previous = none := by
        simpa [hPrev] using previousEq.symm
      subst hprevious
      rw [input.localizedRerootChildren?_current_iff_adjacent_root singleBonded acyclic enough
        cursor hPrev (cursorAtom_spec singleBonded acyclic cursor)
        (input.executableLocalizedRerootChildren cursor)
        (input.localizedRerootChildren?_eq_some_executable cursor) w]
      constructor
      · intro hAdj
        exact ⟨hAdj, fun p hp => by cases hp⟩
      · intro hAdjEx
        exact hAdjEx.1
  | some previousOcc =>
      have hprevious : previous = previousOcc.1.node.current? := by
        simpa [hPrev] using previousEq.symm
      subst hprevious
      have hValid : cursor.occurrence.1 ∈
          input.localizedRerootNeighborFrames (fuel := carrierFuel) previousOcc.1 := by
        simpa [LocalizedRerootCursorValid, hPrev] using valid
      have hSameRoot : cursor.occurrence.1.root = previousOcc.1.root :=
        ((input.mem_localizedRerootNeighborFrames_iff previousOcc.1 cursor.occurrence.1).mp
          hValid).2.1
      obtain ⟨pAtom, _path, pObserved, _head, _provenance, _simple, _support, _penultimate⟩ :=
        input.carrierOccurrence_realPath singleBonded acyclic previousOcc
      have hprevIff := input.localizedRerootChildren?_current_iff_adjacent_of_previous
        singleBonded acyclic enough cursor previousOcc hPrev hSameRoot
        (cursorAtom_spec singleBonded acyclic cursor) pObserved
        (input.executableLocalizedRerootChildren cursor)
        (input.localizedRerootChildren?_eq_some_executable cursor)
      rw [(hprevIff w)]
      have hExcl : PhysicalCutExcludes (previousOcc.1.node.current?) w ↔ w ≠ pAtom := by
        constructor
        · intro h
          exact h pAtom (by rw [pObserved])
        · intro hne p hp
          rw [pObserved] at hp
          have hpAtom : p = pAtom := (Option.some.inj hp).symm
          simpa [hpAtom] using hne
      rw [hExcl]

/-- A physical child of a full incoming-cut tree has an actual executable child cursor with that
child root as its current atom. -/
private theorem physicalChildCursor_exists
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (child : PhysicalAtomTree input.Atom)
    (hAdjEx : input.moleculeGraph.Adj (cursorAtom singleBonded acyclic cursor) child.root ∧
      PhysicalCutExcludes previous child.root) :
    ∃ childCursor : input.LocalizedRerootCursor carrierFuel,
      childCursor.occurrence.1.node.current? = some child.root ∧
        childCursor ∈ input.executableLocalizedRerootChildren cursor := by
  rcases (physicalExecutableChild_iff enough singleBonded acyclic cursor valid previous previousEq
    child.root).mpr hAdjEx with ⟨childCursor, hmem, hObserved⟩
  exact ⟨childCursor, hObserved, hmem⟩

/-- The chosen actual executable child cursor for one physical child of a full incoming-cut
tree. -/
noncomputable def physicalChildCursor
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (child : PhysicalAtomTree input.Atom)
    (hAdjEx : input.moleculeGraph.Adj (cursorAtom singleBonded acyclic cursor) child.root ∧
      PhysicalCutExcludes previous child.root) :
    input.LocalizedRerootCursor carrierFuel :=
  Classical.choose (physicalChildCursor_exists enough singleBonded acyclic cursor valid previous
    previousEq child hAdjEx)

/-- The chosen child cursor observes the physical child root. -/
theorem physicalChildCursor_observed
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (child : PhysicalAtomTree input.Atom)
    (hAdjEx : input.moleculeGraph.Adj (cursorAtom singleBonded acyclic cursor) child.root ∧
      PhysicalCutExcludes previous child.root) :
    (physicalChildCursor enough singleBonded acyclic cursor valid previous previousEq child hAdjEx).occurrence.1.node.current? =
      some child.root :=
  (Classical.choose_spec (physicalChildCursor_exists enough singleBonded acyclic cursor valid
    previous previousEq child hAdjEx)).1

/-- The chosen child cursor is an actual executable child of the parent cursor. -/
theorem physicalChildCursor_mem
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (child : PhysicalAtomTree input.Atom)
    (hAdjEx : input.moleculeGraph.Adj (cursorAtom singleBonded acyclic cursor) child.root ∧
      PhysicalCutExcludes previous child.root) :
    physicalChildCursor enough singleBonded acyclic cursor valid previous previousEq child hAdjEx ∈
      input.executableLocalizedRerootChildren cursor :=
  (Classical.choose_spec (physicalChildCursor_exists enough singleBonded acyclic cursor valid
    previous previousEq child hAdjEx)).2

/-- Accessor: the root equation of a full incoming-cut tree. -/
theorem PhysicalFullCutTree.root_eq {V : Type u} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) {previous : Option V} {current : V} {tree : PhysicalAtomTree V}
    (full : PhysicalFullCutTree m previous current tree) :
    tree.root = current := by
  cases full with
  | mk _previous _current _tree root _nodup _inventory _children =>
      exact root

/-- Accessor: the child roots of a full incoming-cut tree are duplicate-free. -/
theorem PhysicalFullCutTree.nodup_roots {V : Type u} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) {previous : Option V} {current : V} {tree : PhysicalAtomTree V}
    (full : PhysicalFullCutTree m previous current tree) :
    (tree.children.map (fun child : PhysicalAtomTree V => child.root)).Nodup := by
  cases full with
  | mk _previous _current _tree _root nodup _inventory _children =>
      exact nodup

/-- Accessor: the exact neighbor inventory of a full incoming-cut tree. -/
theorem PhysicalFullCutTree.inventory_iff {V : Type u} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) {previous : Option V} {current : V} {tree : PhysicalAtomTree V}
    (full : PhysicalFullCutTree m previous current tree) :
    ∀ w : V, w ∈ tree.children.map (fun child : PhysicalAtomTree V => child.root) ↔
      m.Adj current w ∧ PhysicalCutExcludes previous w := by
  cases full with
  | mk _previous _current _tree _root _nodup inventory _children =>
      exact inventory

/-- The adjacency-and-exclusion inventory entry of one physical child of a full incoming-cut
tree. -/
theorem physicalChildAdjEx (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (cursor : input.LocalizedRerootCursor carrierFuel) (previous : Option input.Atom)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree)
    (child : PhysicalAtomTree input.Atom) (hmem : child ∈ tree.children) :
    input.moleculeGraph.Adj (cursorAtom singleBonded acyclic cursor) child.root ∧
      PhysicalCutExcludes previous child.root :=
  (PhysicalFullCutTree.inventory_iff input.moleculeGraph full child.root).mp
    (List.mem_map.mpr ⟨child, hmem, rfl⟩)

/-- The chosen child cursor for one physical child of the full incoming-cut tree at the parent
cursor. -/
noncomputable def physicalLiftChildCursor
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree)
    (child : PhysicalAtomTree input.Atom) (hmem : child ∈ tree.children) :
    input.LocalizedRerootCursor carrierFuel :=
  physicalChildCursor enough singleBonded acyclic cursor valid previous previousEq child
    (physicalChildAdjEx singleBonded acyclic cursor previous tree full child hmem)

/-- The chosen child cursor is path-valid. -/
theorem physicalLiftChildValid
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree)
    (child : PhysicalAtomTree input.Atom) (hmem : child ∈ tree.children) :
    input.LocalizedRerootCursorValid (physicalLiftChildCursor enough singleBonded acyclic cursor
      valid previous previousEq tree full child hmem) :=
  input.localizedRerootChild_valid cursor
    (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq tree full
      child hmem)
    (input.executableLocalizedRerootChildren cursor)
    (input.executableLocalizedRerootChildren_declarative cursor)
    (physicalChildCursor_mem enough singleBonded acyclic cursor valid previous previousEq child
      (physicalChildAdjEx singleBonded acyclic cursor previous tree full child hmem))

/-- The chosen child cursor records the parent occurrence as its previous coordinate, so its bound
previous atom is the parent's current atom. -/
theorem physicalLiftChildPrevEq
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree)
    (child : PhysicalAtomTree input.Atom) (hmem : child ∈ tree.children) :
    (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq tree full
      child hmem).previous?.bind (fun p => p.1.node.current?) =
      some (cursorAtom singleBonded acyclic cursor) := by
  rw [input.executableLocalizedRerootChildren_previous cursor
    (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq tree full
      child hmem)
    (physicalChildCursor_mem enough singleBonded acyclic cursor valid previous previousEq child
      (physicalChildAdjEx singleBonded acyclic cursor previous tree full child hmem))]
  exact cursorAtom_spec singleBonded acyclic cursor

/-- The physical child of a full incoming-cut tree is itself a full incoming-cut tree from the
parent's current atom at the chosen child cursor. -/
theorem physicalLiftChildFull
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree)
    (child : PhysicalAtomTree input.Atom) (hmem : child ∈ tree.children) :
    PhysicalFullCutTree input.moleculeGraph (some (cursorAtom singleBonded acyclic cursor))
      (cursorAtom singleBonded acyclic (physicalLiftChildCursor enough singleBonded acyclic cursor
        valid previous previousEq tree full child hmem)) child := by
  have hCurrent : cursorAtom singleBonded acyclic (physicalLiftChildCursor enough singleBonded
      acyclic cursor valid previous previousEq tree full child hmem) = child.root :=
    cursorAtom_eq_of_observed singleBonded acyclic
      (physicalChildCursor_observed enough singleBonded acyclic cursor valid previous previousEq
        child (physicalChildAdjEx singleBonded acyclic cursor previous tree full child hmem))
  exact hCurrent.symm ▸ (PhysicalFullCutTree.children_some input.moleculeGraph full hmem)

noncomputable section

mutual
  /-- **The physical lift.**  At a valid actual incoming cursor whose recorded previous atom
  matches the physical previous, every full incoming-cut physical tree is realized as an actual
  decorated tree: the actual root is `localizedRootTree` at the cursor with the reader's actual
  value, and the children are the recursively lifted physical children, each attached at the
  chosen executable child cursor whose current atom is that child's root. -/
  def physicalLift
      (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
      (singleBonded : input.moleculeGraph.SimpleBonded)
      (acyclic : input.moleculeGraph.Acyclic)
      (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
      (cursor : input.LocalizedRerootCursor carrierFuel)
      (valid : input.LocalizedRerootCursorValid cursor)
      (previous : Option input.Atom)
      (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
      (tree : PhysicalAtomTree input.Atom)
      (full : PhysicalFullCutTree input.moleculeGraph previous
        (cursorAtom singleBonded acyclic cursor) tree) :
      LocalizedCumulativeDecoratedTree input carrierFuel :=
    match tree with
    | ⟨root, children⟩ =>
        localizedRootTree input cursor (r cursor)
          (physicalLiftList enough singleBonded acyclic r cursor valid previous previousEq
            ⟨root, children⟩ full children (fun _ h => h))
  termination_by sizeOf tree
  decreasing_by
    simp_wf

  /-- Lift a list of physical children of one full incoming-cut tree, preserving physical child
  order. -/
  def physicalLiftList
      (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
      (singleBonded : input.moleculeGraph.SimpleBonded)
      (acyclic : input.moleculeGraph.Acyclic)
      (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
      (cursor : input.LocalizedRerootCursor carrierFuel)
      (valid : input.LocalizedRerootCursorValid cursor)
      (previous : Option input.Atom)
      (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
      (tree : PhysicalAtomTree input.Atom)
      (full : PhysicalFullCutTree input.moleculeGraph previous
        (cursorAtom singleBonded acyclic cursor) tree)
      (children : List (PhysicalAtomTree input.Atom))
      (hchildren : ∀ child ∈ children, child ∈ tree.children) :
      List (LocalizedCumulativeDecoratedTree input carrierFuel) :=
    match children, hchildren with
    | [], _ => []
    | child :: rest, hchildren =>
        let hmem : child ∈ tree.children := hchildren child (by simp)
        physicalLift enough singleBonded acyclic r
          (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
            tree full child hmem)
          (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq tree
            full child hmem)
          (some (cursorAtom singleBonded acyclic cursor))
          (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq tree
            full child hmem)
          child
          (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq tree
            full child hmem) ::
          physicalLiftList enough singleBonded acyclic r cursor valid previous previousEq tree full
            rest (fun c hc => hchildren c (by simp [hc]))
  termination_by sizeOf children
  decreasing_by
    all_goals (simp_wf <;> omega)
end

end

/-- The source cursor of a lifted tree is the cursor it was lifted at. -/
theorem physicalLift_source
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree) :
    (physicalLift enough singleBonded acyclic r cursor valid previous previousEq tree full).source =
      cursor := by
  cases tree with
  | mk root children =>
      rw [physicalLift]
      simp [localizedRootTree]

/-- The children of a lifted tree are the lifts of the physical children, in physical order. -/
theorem physicalLift_children
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree) :
    (physicalLift enough singleBonded acyclic r cursor valid previous previousEq tree full).children =
      physicalLiftList enough singleBonded acyclic r cursor valid previous previousEq tree full
        tree.children (fun _ h => h) := by
  cases tree with
  | mk root children =>
      rw [physicalLift]
      simp [localizedRootTree]

/-- The source cursors of the lifted child list are the chosen executable child cursors, in
physical child order. -/
theorem physicalLiftList_sources
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree)
    (children : List (PhysicalAtomTree input.Atom))
    (hchildren : ∀ child ∈ children, child ∈ tree.children) :
    (physicalLiftList enough singleBonded acyclic r cursor valid previous previousEq tree full
      children hchildren).map (fun t => t.source) =
      children.attach.map (fun c =>
        physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq tree
          full c.1 (hchildren c.1 c.2)) := by
  induction children with
  | nil =>
      simp [physicalLiftList]
  | cons child rest ih =>
      rw [physicalLiftList]
      simp only [List.map_cons, List.attach_cons]
      congr 1
      · rw [physicalLift_source enough singleBonded acyclic r
          (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
            tree full child (hchildren child (by simp)))
          (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq tree
            full child (hchildren child (by simp)))
          (some (cursorAtom singleBonded acyclic cursor))
          (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
            tree full child (hchildren child (by simp)))
          child
          (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq tree
            full child (hchildren child (by simp)))]
      · simpa using ih (fun c hc => hchildren c (by simp [hc]))

/-- **The lifted sorted children permute the actual executable child frame.**  The lifted child
sources are duplicate-free (distinct physical child roots pick distinct executable cursors, and
full-cut child roots are duplicate-free) and carry exactly the executable child cursors (each
executable child's current atom is a physical child root by the exact neighbor inventory), so they
are a permutation of the executable list. -/
theorem physicalLiftList_sourcePerm
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree) :
    List.Perm
      ((physicalLiftList enough singleBonded acyclic r cursor valid previous previousEq tree full
        tree.children (fun _ h => h)).map (fun t => t.source))
      (input.executableLocalizedRerootChildren cursor) := by
  classical
  rw [physicalLiftList_sources enough singleBonded acyclic r cursor valid previous previousEq tree
    full tree.children (fun _ h => h)]
  have hChildrenNodup : tree.children.Nodup :=
    List.Nodup.of_map (fun t : PhysicalAtomTree input.Atom => t.root)
      (PhysicalFullCutTree.nodup_roots input.moleculeGraph full)
  have hChosenNodup : (tree.children.attach.map (fun c =>
      physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq tree
        full c.1 c.2)).Nodup := by
    have hPmap : (tree.children.pmap (fun child hmem =>
        physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq tree
          full child hmem) (fun _ h => h)).Nodup :=
      List.Nodup.pmap (fun a ha b hb hEq => by
        have hLeft := physicalChildCursor_observed enough singleBonded acyclic cursor valid previous
          previousEq a (physicalChildAdjEx singleBonded acyclic cursor previous tree full a ha)
        have hRight := physicalChildCursor_observed enough singleBonded acyclic cursor valid previous
          previousEq b (physicalChildAdjEx singleBonded acyclic cursor previous tree full b hb)
        have hCur : (physicalChildCursor enough singleBonded acyclic cursor valid previous previousEq
            a (physicalChildAdjEx singleBonded acyclic cursor previous tree full a ha)).occurrence.1.node.current? =
            (physicalChildCursor enough singleBonded acyclic cursor valid previous previousEq b
              (physicalChildAdjEx singleBonded acyclic cursor previous tree full b hb)).occurrence.1.node.current? := by
          simpa [physicalLiftChildCursor] using congrArg
            (fun c : input.LocalizedRerootCursor carrierFuel => c.occurrence.1.node.current?) hEq
        have hRootEq : a.root = b.root := by
          rw [hLeft] at hCur
          rw [hRight] at hCur
          exact Option.some.inj hCur
        exact List.inj_on_of_nodup_map
          (PhysicalFullCutTree.nodup_roots input.moleculeGraph full) ha hb hRootEq) hChildrenNodup
    simpa [List.pmap_eq_map_attach] using hPmap
  exact (List.perm_ext_iff_of_nodup hChosenNodup
    (input.executableLocalizedRerootChildren_nodup cursor)).mpr (by
    intro c
    constructor
    · rw [List.mem_map]
      rintro ⟨x, hx, hEq⟩
      exact hEq ▸ (physicalChildCursor_mem enough singleBonded acyclic cursor valid previous
        previousEq x.1 (physicalChildAdjEx singleBonded acyclic cursor previous tree full x.1 x.2))
    · intro hmemC
      have hAdjEx : input.moleculeGraph.Adj (cursorAtom singleBonded acyclic cursor)
          (cursorAtom singleBonded acyclic c) ∧
          PhysicalCutExcludes previous (cursorAtom singleBonded acyclic c) :=
        (physicalExecutableChild_iff enough singleBonded acyclic cursor valid previous previousEq
          (cursorAtom singleBonded acyclic c)).mp ⟨c, hmemC, cursorAtom_spec singleBonded acyclic c⟩
      have hRootMem : cursorAtom singleBonded acyclic c ∈
          tree.children.map (fun child : PhysicalAtomTree input.Atom => child.root) :=
        (PhysicalFullCutTree.inventory_iff input.moleculeGraph full
          (cursorAtom singleBonded acyclic c)).mpr hAdjEx
      rw [List.mem_map] at hRootMem
      obtain ⟨child, hChildMem, hRoot⟩ := hRootMem
      have hObserved' : (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous
          previousEq tree full child hChildMem).occurrence.1.node.current? =
            some (cursorAtom singleBonded acyclic c) := by
        show (physicalChildCursor enough singleBonded acyclic cursor valid previous previousEq child
          (physicalChildAdjEx singleBonded acyclic cursor previous tree full child hChildMem)).occurrence.1.node.current? =
            some (cursorAtom singleBonded acyclic c)
        rw [physicalChildCursor_observed enough singleBonded acyclic cursor valid previous
          previousEq child (physicalChildAdjEx singleBonded acyclic cursor previous tree full child
            hChildMem)]
        rw [hRoot]
      have c'Mem : physicalLiftChildCursor enough singleBonded acyclic cursor valid previous
          previousEq tree full child hChildMem ∈
            input.executableLocalizedRerootChildren cursor :=
        physicalChildCursor_mem enough singleBonded acyclic cursor valid previous previousEq child
          (physicalChildAdjEx singleBonded acyclic cursor previous tree full child hChildMem)
      have hCurEq : c.occurrence.1.node.current? =
          (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
            tree full child hChildMem).occurrence.1.node.current? := by
        have hC := cursorAtom_spec singleBonded acyclic c
        exact hC.trans hObserved'.symm
      have cEqC' : c = physicalLiftChildCursor enough singleBonded acyclic cursor valid previous
          previousEq tree full child hChildMem :=
        input.localizedRerootChildren?_current_injective singleBonded acyclic cursor
          (input.executableLocalizedRerootChildren cursor)
          (input.localizedRerootChildren?_eq_some_executable cursor) _ hmemC _ c'Mem hCurEq
      rw [List.mem_map]
      exact ⟨⟨child, hChildMem⟩, by simp, by
        simpa [physicalLiftChildCursor] using cEqC'.symm⟩)

/-- Every lift in a sublist of the children realizes its physical child, given the realization
fact for each physical child.  The parent `tree`/`full` stay fixed through the list induction. -/
theorem physicalLiftList_realizes
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree)
    (children : List (PhysicalAtomTree input.Atom))
    (hchildren : ∀ c ∈ children, c ∈ tree.children)
    (childRealize : ∀ (child : PhysicalAtomTree input.Atom) (hmem : child ∈ tree.children),
      LocalizedCumulativeTreeRealizes input r
        (physicalLift enough singleBonded acyclic r
          (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
            tree full child hmem)
          (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
            tree full child hmem)
          (some (cursorAtom singleBonded acyclic cursor))
          (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
            tree full child hmem)
          child
          (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
            tree full child hmem))) :
    ∀ t : LocalizedCumulativeDecoratedTree input carrierFuel,
      t ∈ physicalLiftList enough singleBonded acyclic r cursor valid previous previousEq tree
        full children hchildren →
      LocalizedCumulativeTreeRealizes input r t := by
  intro t hmem
  induction children with
  | nil =>
      simp [physicalLiftList] at hmem
  | cons child rest ihList =>
      rw [physicalLiftList] at hmem
      simp only [List.mem_cons] at hmem
      obtain hEq | hTail := hmem
      · rw [hEq]
        exact childRealize child (hchildren child (by simp))
      · exact ihList (fun c hc => hchildren c (by simp [hc])) hTail

/-- Erasure inverts the lift on a sublist of the children, given the round trip for each physical
child.  The parent `tree`/`full` stay fixed through the list induction. -/
theorem physicalErasure_physicalLiftList
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree)
    (children : List (PhysicalAtomTree input.Atom))
    (hchildren : ∀ c ∈ children, c ∈ tree.children)
    (childErasure : ∀ (child : PhysicalAtomTree input.Atom) (hmem : child ∈ tree.children),
      physicalErasure singleBonded acyclic
          (physicalLift enough singleBonded acyclic r
            (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
              tree full child hmem)
            (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
              tree full child hmem)
            (some (cursorAtom singleBonded acyclic cursor))
            (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
              tree full child hmem)
            child
            (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
              tree full child hmem)) =
        child) :
    physicalErasureChildren singleBonded acyclic
        (physicalLiftList enough singleBonded acyclic r cursor valid previous previousEq tree
          full children hchildren) =
      children := by
  induction children with
  | nil =>
      simp [physicalLiftList, physicalErasureChildren]
  | cons child rest ihList =>
      rw [physicalLiftList]
      simp only [physicalErasureChildren]
      congr
      · exact childErasure child (hchildren child (by simp))
      · exact ihList (fun c hc => hchildren c (by simp [hc]))

/-- **The lifted tree realizes the physical tree.**  The actual decorated tree produced by
`physicalLift` is a `LocalizedCumulativeTreeRealizes` tree: its source is the cursor, its children
are executable-permuting, and every lifted child recursively realizes its physical child. -/
theorem physicalLift_realizes
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree) :
    LocalizedCumulativeTreeRealizes input r
      (physicalLift enough singleBonded acyclic r cursor valid previous previousEq tree full) := by
  have main : ∀ n : Nat, ∀ candidate : PhysicalAtomTree input.Atom,
      PhysicalAtomTree.height candidate ≤ n →
      ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      ∀ valid : input.LocalizedRerootCursorValid cursor,
      ∀ previous : Option input.Atom,
      ∀ previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous,
      ∀ full : PhysicalFullCutTree input.moleculeGraph previous
        (cursorAtom singleBonded acyclic cursor) candidate,
      LocalizedCumulativeTreeRealizes input r
        (physicalLift enough singleBonded acyclic r cursor valid previous previousEq candidate
          full) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k inductionHypothesis candidate bound cursor valid previous previousEq full
    cases candidate with
    | mk root children =>
        rw [physicalLift]
        apply LocalizedCumulativeTreeRealizes.mk cursor
          (input.executableLocalizedRerootChildren cursor)
          (physicalLiftList enough singleBonded acyclic r cursor valid previous previousEq
            ⟨root, children⟩ full children (fun _ h => h))
          (input.localizedRerootChildren?_eq_some_executable cursor)
          (physicalLiftList_sourcePerm enough singleBonded acyclic r cursor valid previous
            previousEq ⟨root, children⟩ full)
        · intro t hmem
          exact physicalLiftList_realizes enough singleBonded acyclic r cursor valid previous
            previousEq ⟨root, children⟩ full children (fun _ h => h)
            (by
              intro child hmemChild
              have hlt : PhysicalAtomTree.height child < k := by
                have hle := PhysicalAtomTree.height_child_le ⟨root, children⟩ child hmemChild
                omega
              exact inductionHypothesis (PhysicalAtomTree.height child) hlt child (le_refl _)
                (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous
                  previousEq ⟨root, children⟩ full child hmemChild)
                (physicalLiftChildValid enough singleBonded acyclic cursor valid previous
                  previousEq ⟨root, children⟩ full child hmemChild)
                (some (cursorAtom singleBonded acyclic cursor))
                (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous
                  previousEq ⟨root, children⟩ full child hmemChild)
                (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
                  ⟨root, children⟩ full child hmemChild))
            t hmem
  exact main (PhysicalAtomTree.height tree) tree (le_refl _) cursor valid previous previousEq full

/-- **Erasure inverts the lift.**  Erasing the lifted tree recovers the original physical tree
exactly, with its root atom, child order and subtree structure. -/
theorem physicalErasure_physicalLift
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree) :
    physicalErasure singleBonded acyclic
        (physicalLift enough singleBonded acyclic r cursor valid previous previousEq tree full) =
      tree := by
  have main : ∀ n : Nat, ∀ candidate : PhysicalAtomTree input.Atom,
      PhysicalAtomTree.height candidate ≤ n →
      ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      ∀ valid : input.LocalizedRerootCursorValid cursor,
      ∀ previous : Option input.Atom,
      ∀ previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous,
      ∀ full : PhysicalFullCutTree input.moleculeGraph previous
        (cursorAtom singleBonded acyclic cursor) candidate,
      physicalErasure singleBonded acyclic
          (physicalLift enough singleBonded acyclic r cursor valid previous previousEq candidate
            full) =
        candidate := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k inductionHypothesis candidate bound cursor valid previous previousEq full
    cases candidate with
    | mk root children =>
        rw [physicalErasure_def singleBonded acyclic
          (physicalLift enough singleBonded acyclic r cursor valid previous previousEq
            ⟨root, children⟩ full)]
        congr
        · apply nodeAtom_eq_of_observed singleBonded acyclic
          rw [physicalLift_source enough singleBonded acyclic r cursor valid previous previousEq
            ⟨root, children⟩ full]
          rw [cursorAtom_spec singleBonded acyclic cursor]
          exact congrArg some (PhysicalFullCutTree.root_eq input.moleculeGraph full).symm
        · rw [physicalLift_children enough singleBonded acyclic r cursor valid previous previousEq
            ⟨root, children⟩ full]
          exact physicalErasure_physicalLiftList enough singleBonded acyclic r cursor valid
            previous previousEq ⟨root, children⟩ full children (fun _ h => h)
            (by
              intro child hmemChild
              have hlt : PhysicalAtomTree.height child < k := by
                have hle := PhysicalAtomTree.height_child_le ⟨root, children⟩ child hmemChild
                omega
              exact inductionHypothesis (PhysicalAtomTree.height child) hlt child (le_refl _)
                (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous
                  previousEq ⟨root, children⟩ full child hmemChild)
                (physicalLiftChildValid enough singleBonded acyclic cursor valid previous
                  previousEq ⟨root, children⟩ full child hmemChild)
                (some (cursorAtom singleBonded acyclic cursor))
                (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous
                  previousEq ⟨root, children⟩ full child hmemChild)
                (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
                  ⟨root, children⟩ full child hmemChild))
  exact main (PhysicalAtomTree.height tree) tree (le_refl _) cursor valid previous previousEq full

/-- **The physical outcome of two physical trees equals the actual outcome of their lifts.** -/
theorem physicalTreeRuleMajorOutcome_eq_lift
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (outerRoot : input.Atom)
    (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursorLeft : input.LocalizedRerootCursor carrierFuel)
    (validLeft : input.LocalizedRerootCursorValid cursorLeft)
    (previousLeft : Option input.Atom)
    (previousEqLeft : cursorLeft.previous?.bind (fun p => p.1.node.current?) = previousLeft)
    (treeLeft : PhysicalAtomTree input.Atom)
    (fullLeft : PhysicalFullCutTree input.moleculeGraph previousLeft
      (cursorAtom singleBonded acyclic cursorLeft) treeLeft)
    (cursorRight : input.LocalizedRerootCursor carrierFuel)
    (validRight : input.LocalizedRerootCursorValid cursorRight)
    (previousRight : Option input.Atom)
    (previousEqRight : cursorRight.previous?.bind (fun p => p.1.node.current?) = previousRight)
    (treeRight : PhysicalAtomTree input.Atom)
    (fullRight : PhysicalFullCutTree input.moleculeGraph previousRight
      (cursorAtom singleBonded acyclic cursorRight) treeRight)
    (outcome : Ordering) :
    physicalTreeRuleMajorOutcome input.moleculeGraph outerRoot treeLeft treeRight outcome ↔
      physicalRuleMajorOutcome singleBonded acyclic outerRoot
        (physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft previousEqLeft
          treeLeft fullLeft)
        (physicalLift enough singleBonded acyclic r cursorRight validRight previousRight
          previousEqRight treeRight fullRight) outcome := by
  rw [← physicalTreeRuleMajorOutcome_eq_erasure singleBonded acyclic outerRoot
    (physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft previousEqLeft
      treeLeft fullLeft)
    (physicalLift enough singleBonded acyclic r cursorRight validRight previousRight previousEqRight
      treeRight fullRight) outcome]
  rw [physicalErasure_physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft
    previousEqLeft treeLeft fullLeft,
    physicalErasure_physicalLift enough singleBonded acyclic r cursorRight validRight previousRight
    previousEqRight treeRight fullRight]

/-- The physical non-junior relation of two physical trees equals the actual non-junior relation
of their lifts. -/
theorem physicalTreeRuleMajorNotLt_eq_lift
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (outerRoot : input.Atom)
    (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursorLeft : input.LocalizedRerootCursor carrierFuel)
    (validLeft : input.LocalizedRerootCursorValid cursorLeft)
    (previousLeft : Option input.Atom)
    (previousEqLeft : cursorLeft.previous?.bind (fun p => p.1.node.current?) = previousLeft)
    (treeLeft : PhysicalAtomTree input.Atom)
    (fullLeft : PhysicalFullCutTree input.moleculeGraph previousLeft
      (cursorAtom singleBonded acyclic cursorLeft) treeLeft)
    (cursorRight : input.LocalizedRerootCursor carrierFuel)
    (validRight : input.LocalizedRerootCursorValid cursorRight)
    (previousRight : Option input.Atom)
    (previousEqRight : cursorRight.previous?.bind (fun p => p.1.node.current?) = previousRight)
    (treeRight : PhysicalAtomTree input.Atom)
    (fullRight : PhysicalFullCutTree input.moleculeGraph previousRight
      (cursorAtom singleBonded acyclic cursorRight) treeRight) :
    physicalTreeRuleMajorNotLt input.moleculeGraph outerRoot treeLeft treeRight ↔
      physicalRuleMajorNotLt singleBonded acyclic
        (physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft previousEqLeft
          treeLeft fullLeft)
        (physicalLift enough singleBonded acyclic r cursorRight validRight previousRight
          previousEqRight treeRight fullRight) outerRoot := by
  simp [physicalTreeRuleMajorNotLt, physicalRuleMajorNotLt, physicalTreeRuleMajorOutcome_eq_lift
    enough singleBonded acyclic outerRoot r cursorLeft validLeft previousLeft previousEqLeft
    treeLeft fullLeft cursorRight validRight previousRight previousEqRight treeRight fullRight]

/-- Lift an admissible physical incoming-cut tree at a valid actual cursor whose observed current
atom is identified with the physical current by `hcurrent`.  The independent descending constraint
is retained by the admissible hypothesis but is not needed to build the actual tree. -/
noncomputable def physicalLift_of_admissible
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (outerRoot : input.Atom)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (current : input.Atom)
    (hcurrent : current = cursorAtom singleBonded acyclic cursor)
    (tree : PhysicalAtomTree input.Atom)
    (admissible : PhysicalIncomingCutAdmissible input.moleculeGraph outerRoot previous current tree) :
    LocalizedCumulativeDecoratedTree input carrierFuel :=
  physicalLift enough singleBonded acyclic r cursor valid previous previousEq tree
    (hcurrent.symm ▸ admissible.full)

/-! ## H. Internal declarative keys from independent physical descent

The internal derivation device: from an independent physical descending full-cut tree at a valid
actual incoming cursor, build a `DeclarativeLocalizedRerootRuleMajorKey` (fuel = structural
height) whose `constitutionalObservable` is exactly the lifted tree's table observable.  This is
used only inside `physicalTreeRuleMajorOutcome_admissible_congr` and the export iff; the public
criterion stays graph-only. -/

/-- The private merge-observation combinator, copied exactly from
`LocalizedConstitutionalObservable` (which keeps it private). -/
private def mergeObserved {α : Type*}
    (children : List (List (List (OfficialSparseEntry α)))) :
    List (List (OfficialSparseEntry α)) :=
  let count := children.foldl (fun longest child => max longest child.length) 0
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2 (child.1.getD depth [])

/-- The merge step of `OfficialRuleMajorKey.assemble` is exactly the observed merge. -/
private theorem mergeChildren_eq_observed {V α : Type*}
    (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α))) :
    OfficialRuleMajorKey.mergeChildren children layers = mergeObserved (children.map layers) := by
  simp only [OfficialRuleMajorKey.mergeChildren, OfficialRuleMajorKey.childLayerCount,
    mergeObserved, List.foldl_map, List.zipIdx_map, List.flatMap_map]
  rfl

/-- The localized cumulative-table merge is the same observed merge. -/
private theorem mergeLocalizedTreeChildTables_eq_observed {α : Type*}
    (tables : List (List (List (OfficialSparseEntry α)))) :
    LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables tables = mergeObserved tables := by
  simp only [LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables,
    LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount, SparseAddress.mergePairTable,
    SparseAddress.mergePairs, mergeObserved, id_eq]

/-- Every tree in a lifted child list is the lift of some physical child of that sublist, at its
chosen executable child cursor. -/
private theorem physicalLiftList_mem
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree) :
    ∀ (children : List (PhysicalAtomTree input.Atom))
      (hchildren : ∀ child ∈ children, child ∈ tree.children),
      ∀ t : LocalizedCumulativeDecoratedTree input carrierFuel,
      t ∈ physicalLiftList enough singleBonded acyclic r cursor valid previous previousEq tree
        full children hchildren →
      ∃ (child : PhysicalAtomTree input.Atom) (hmem : child ∈ children),
        t = physicalLift enough singleBonded acyclic r
          (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
            tree full child (hchildren child hmem))
          (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
            tree full child (hchildren child hmem))
          (some (cursorAtom singleBonded acyclic cursor))
          (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
            tree full child (hchildren child hmem))
          child
          (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
            tree full child (hchildren child hmem)) := by
  intro children
  induction children with
  | nil =>
      intro hchildren t hmem
      simp [physicalLiftList] at hmem
  | cons child rest ih =>
      intro hchildren t hmem
      rw [physicalLiftList] at hmem
      simp only [List.mem_cons] at hmem
      obtain hEq | hTail := hmem
      · exact ⟨child, by simp, hEq⟩
      · rcases ih (fun c hc => hchildren c (by simp [hc])) t hTail with ⟨c, hc, hEq⟩
        exact ⟨c, by simp [hc], hEq⟩

/-- The stored occurrence root of a chosen physical child cursor is the original `outerRoot`. -/
private theorem physicalLiftChildRoot_eq
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (outerRoot : input.Atom)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (rootEq : cursor.occurrence.1.root = outerRoot)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree)
    (child : PhysicalAtomTree input.Atom)
    (hmem : child ∈ tree.children) :
    (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq tree
      full child hmem).occurrence.1.root = outerRoot := by
  rw [input.localizedRerootChildren?_root_eq cursor
    (input.executableLocalizedRerootChildren cursor)
    (input.localizedRerootChildren?_eq_some_executable cursor)
    (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq tree
      full child hmem)
    (physicalChildCursor_mem enough singleBonded acyclic cursor valid previous previousEq child
      (physicalChildAdjEx singleBonded acyclic cursor previous tree full child hmem))]
  exact rootEq

/-- Non-junior physical comparison of two physical children transports to non-junior comparison
of their lifted trees' constitutional-table observables, at the original `outerRoot`. -/
private theorem compare_not_lt_of_lift_physical_notLt
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (outerRoot : input.Atom)
    (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (rootEq : cursor.occurrence.1.root = outerRoot)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree)
    (rootLeft rootRight : PhysicalAtomTree input.Atom)
    (hmemLeft : rootLeft ∈ tree.children) (hmemRight : rootRight ∈ tree.children)
    (notLt : physicalTreeRuleMajorNotLt input.moleculeGraph outerRoot rootLeft rootRight) :
    OfficialRuleMajorKey.compare
      (constitutionalTablesKey [] true
        (physicalLift enough singleBonded acyclic r
          (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
            tree full rootLeft hmemLeft)
          (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
            tree full rootLeft hmemLeft)
          (some (cursorAtom singleBonded acyclic cursor))
          (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
            tree full rootLeft hmemLeft)
          rootLeft
          (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
            tree full rootLeft hmemLeft)))
      (constitutionalTablesKey [] true
        (physicalLift enough singleBonded acyclic r
          (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
            tree full rootRight hmemRight)
          (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
            tree full rootRight hmemRight)
          (some (cursorAtom singleBonded acyclic cursor))
          (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
            tree full rootRight hmemRight)
          rootRight
          (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
            tree full rootRight hmemRight))) ≠ Ordering.lt := by
  have hNotLtActual : physicalRuleMajorNotLt singleBonded acyclic
      (physicalLift enough singleBonded acyclic r
        (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
          tree full rootLeft hmemLeft)
        (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq tree
          full rootLeft hmemLeft)
        (some (cursorAtom singleBonded acyclic cursor))
        (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq tree
          full rootLeft hmemLeft)
        rootLeft
        (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq tree
          full rootLeft hmemLeft))
      (physicalLift enough singleBonded acyclic r
        (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
          tree full rootRight hmemRight)
        (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq tree
          full rootRight hmemRight)
        (some (cursorAtom singleBonded acyclic cursor))
        (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq tree
          full rootRight hmemRight)
        rootRight
        (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq tree
          full rootRight hmemRight)) outerRoot :=
    (physicalTreeRuleMajorNotLt_eq_lift enough singleBonded acyclic outerRoot r
      (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq tree
        full rootLeft hmemLeft)
      (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq tree
        full rootLeft hmemLeft)
      (some (cursorAtom singleBonded acyclic cursor))
      (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq tree
        full rootLeft hmemLeft)
      rootLeft
      (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq tree
        full rootLeft hmemLeft)
      (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq tree
        full rootRight hmemRight)
      (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq tree
        full rootRight hmemRight)
      (some (cursorAtom singleBonded acyclic cursor))
      (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq tree
        full rootRight hmemRight)
      rootRight
      (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq tree
        full rootRight hmemRight)).mp notLt
  rcases (show
      physicalRuleMajorOutcome singleBonded acyclic outerRoot
          (physicalLift enough singleBonded acyclic r
            (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            (some (cursorAtom singleBonded acyclic cursor))
            (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            rootLeft
            (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft))
          (physicalLift enough singleBonded acyclic r
            (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            (some (cursorAtom singleBonded acyclic cursor))
            (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            rootRight
            (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)) Ordering.gt ∨
        physicalRuleMajorOutcome singleBonded acyclic outerRoot
          (physicalLift enough singleBonded acyclic r
            (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            (some (cursorAtom singleBonded acyclic cursor))
            (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            rootLeft
            (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft))
          (physicalLift enough singleBonded acyclic r
            (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            (some (cursorAtom singleBonded acyclic cursor))
            (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            rootRight
            (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)) Ordering.eq from by
    simpa [physicalRuleMajorNotLt] using hNotLtActual) with hGt | hEq
  · have hRealizesLeft : LocalizedCumulativeTreeRealizes input r
        (physicalLift enough singleBonded acyclic r
          (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
            tree full rootLeft hmemLeft)
          (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
            tree full rootLeft hmemLeft)
          (some (cursorAtom singleBonded acyclic cursor))
          (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
            tree full rootLeft hmemLeft)
          rootLeft
          (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
            tree full rootLeft hmemLeft)) :=
      physicalLift_realizes enough singleBonded acyclic r
        (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq tree
          full rootLeft hmemLeft)
        (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq tree
          full rootLeft hmemLeft)
        (some (cursorAtom singleBonded acyclic cursor))
        (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq tree
          full rootLeft hmemLeft)
        rootLeft
        (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq tree
          full rootLeft hmemLeft)
    have hRealizesRight : LocalizedCumulativeTreeRealizes input r
        (physicalLift enough singleBonded acyclic r
          (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
            tree full rootRight hmemRight)
          (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
            tree full rootRight hmemRight)
          (some (cursorAtom singleBonded acyclic cursor))
          (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
            tree full rootRight hmemRight)
          rootRight
          (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
            tree full rootRight hmemRight)) :=
      physicalLift_realizes enough singleBonded acyclic r
        (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq tree
          full rootRight hmemRight)
        (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq tree
          full rootRight hmemRight)
        (some (cursorAtom singleBonded acyclic cursor))
        (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq tree
          full rootRight hmemRight)
        rootRight
        (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq tree
          full rootRight hmemRight)
    have hCompareGt : OfficialRuleMajorKey.compare
        (constitutionalTablesKey [] true
          (physicalLift enough singleBonded acyclic r
            (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            (some (cursorAtom singleBonded acyclic cursor))
            (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            rootLeft
            (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)))
        (constitutionalTablesKey [] true
          (physicalLift enough singleBonded acyclic r
            (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            (some (cursorAtom singleBonded acyclic cursor))
            (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            rootRight
            (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight))) = Ordering.gt :=
      (compare_tables_eq_iff_physicalRuleMajorOutcome singleBonded acyclic hRealizesLeft
        hRealizesRight outerRoot
        (by
          rw [physicalLift_source enough singleBonded acyclic r
            (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            (some (cursorAtom singleBonded acyclic cursor))
            (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            rootLeft
            (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)]
          exact physicalLiftChildRoot_eq enough singleBonded acyclic outerRoot cursor valid
            previous previousEq rootEq tree full rootLeft hmemLeft)
        (by
          rw [physicalLift_source enough singleBonded acyclic r
            (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            (some (cursorAtom singleBonded acyclic cursor))
            (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            rootRight
            (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)]
          exact physicalLiftChildRoot_eq enough singleBonded acyclic outerRoot cursor valid
            previous previousEq rootEq tree full rootRight hmemRight) Ordering.gt).mpr hGt
    intro hLt
    cases hCompareGt.symm.trans hLt
  · have hRealizesLeft : LocalizedCumulativeTreeRealizes input r
        (physicalLift enough singleBonded acyclic r
          (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
            tree full rootLeft hmemLeft)
          (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
            tree full rootLeft hmemLeft)
          (some (cursorAtom singleBonded acyclic cursor))
          (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
            tree full rootLeft hmemLeft)
          rootLeft
          (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
            tree full rootLeft hmemLeft)) :=
      physicalLift_realizes enough singleBonded acyclic r
        (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq tree
          full rootLeft hmemLeft)
        (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq tree
          full rootLeft hmemLeft)
        (some (cursorAtom singleBonded acyclic cursor))
        (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq tree
          full rootLeft hmemLeft)
        rootLeft
        (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq tree
          full rootLeft hmemLeft)
    have hRealizesRight : LocalizedCumulativeTreeRealizes input r
        (physicalLift enough singleBonded acyclic r
          (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
            tree full rootRight hmemRight)
          (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
            tree full rootRight hmemRight)
          (some (cursorAtom singleBonded acyclic cursor))
          (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
            tree full rootRight hmemRight)
          rootRight
          (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
            tree full rootRight hmemRight)) :=
      physicalLift_realizes enough singleBonded acyclic r
        (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq tree
          full rootRight hmemRight)
        (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq tree
          full rootRight hmemRight)
        (some (cursorAtom singleBonded acyclic cursor))
        (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq tree
          full rootRight hmemRight)
        rootRight
        (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq tree
          full rootRight hmemRight)
    have hCompareEq : OfficialRuleMajorKey.compare
        (constitutionalTablesKey [] true
          (physicalLift enough singleBonded acyclic r
            (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            (some (cursorAtom singleBonded acyclic cursor))
            (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            rootLeft
            (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)))
        (constitutionalTablesKey [] true
          (physicalLift enough singleBonded acyclic r
            (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            (some (cursorAtom singleBonded acyclic cursor))
            (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            rootRight
            (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight))) = Ordering.eq :=
      (compare_tables_eq_iff_physicalRuleMajorOutcome singleBonded acyclic hRealizesLeft
        hRealizesRight outerRoot
        (by
          rw [physicalLift_source enough singleBonded acyclic r
            (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            (some (cursorAtom singleBonded acyclic cursor))
            (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)
            rootLeft
            (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
              tree full rootLeft hmemLeft)]
          exact physicalLiftChildRoot_eq enough singleBonded acyclic outerRoot cursor valid
            previous previousEq rootEq tree full rootLeft hmemLeft)
        (by
          rw [physicalLift_source enough singleBonded acyclic r
            (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            (some (cursorAtom singleBonded acyclic cursor))
            (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)
            rootRight
            (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq
              tree full rootRight hmemRight)]
          exact physicalLiftChildRoot_eq enough singleBonded acyclic outerRoot cursor valid
            previous previousEq rootEq tree full rootRight hmemRight) Ordering.eq).mpr hEq
    intro hLt
    cases hCompareEq.symm.trans hLt

/-- The terminal declarative key's observable is exactly the lifted terminal tree's table
observable. -/
private theorem terminalKey_observable_eq_lift
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel) :
    CertifiedLocalizedCIPInput.constitutionalObservable
        (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true) =
      CertifiedLocalizedCIPInput.constitutionalObservable
        (constitutionalTablesKey [] true (localizedRootTree input cursor label [])) := by
  simp only [CertifiedLocalizedCIPInput.constitutionalObservable, constitutionalTablesKey]
  congr
  · rw [LocalizedCumulativeDecoratedTree.table_eq_root_merge
      (fun node => node.atomicNumber) (localizedRootTree input cursor label [])]
    congr 1
  · rw [LocalizedCumulativeDecoratedTree.table_eq_root_merge
      (fun node => node.rule1bDistance) (localizedRootTree input cursor label [])]
    congr 1
  · rw [LocalizedCumulativeDecoratedTree.table_eq_root_merge
      (fun node => node.isotopeMass) (localizedRootTree input cursor label [])]
    congr 1

/-- The branch-assembled declarative key's observable is exactly the lifted branch tree's table
observable, provided the merge keys' observables match the lifted child trees in physical order. -/
private theorem assembled_observable_eq_liftTables
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel)
    (keys : List (OfficialRuleMajorKey input.Atom))
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel))
    (mapEq : children.map (fun t =>
      CertifiedLocalizedCIPInput.constitutionalObservable
        (constitutionalTablesKey [] true t)) =
      keys.map CertifiedLocalizedCIPInput.constitutionalObservable) :
    CertifiedLocalizedCIPInput.constitutionalObservable
        (OfficialRuleMajorKey.assemble
          (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false) keys) =
      CertifiedLocalizedCIPInput.constitutionalObservable
        (constitutionalTablesKey [] true (localizedRootTree input cursor label children)) := by
  simp only [CertifiedLocalizedCIPInput.constitutionalObservable, constitutionalTablesKey,
    OfficialRuleMajorKey.assemble]
  congr
  · rw [LocalizedCumulativeDecoratedTree.table_eq_root_merge
      (fun node => node.atomicNumber) (localizedRootTree input cursor label children)]
    congr 1
    rw [mergeChildren_eq_observed, mergeLocalizedTreeChildTables_eq_observed]
    have h1a := congrArg (List.map (fun o : LocalizedConstitutionalObservable => o.rule1a))
      mapEq
    apply congrArg mergeObserved
    simpa only [List.map_map, Function.comp_def,
      CertifiedLocalizedCIPInput.constitutionalObservable, constitutionalTablesKey]
      using h1a.symm
  · rw [LocalizedCumulativeDecoratedTree.table_eq_root_merge
      (fun node => node.rule1bDistance) (localizedRootTree input cursor label children)]
    congr 1
    rw [mergeChildren_eq_observed, mergeLocalizedTreeChildTables_eq_observed]
    have h1b := congrArg (List.map (fun o : LocalizedConstitutionalObservable => o.rule1b))
      mapEq
    apply congrArg mergeObserved
    simpa only [List.map_map, Function.comp_def,
      CertifiedLocalizedCIPInput.constitutionalObservable, constitutionalTablesKey]
      using h1b.symm
  · rw [LocalizedCumulativeDecoratedTree.table_eq_root_merge
      (fun node => node.isotopeMass) (localizedRootTree input cursor label children)]
    congr 1
    rw [mergeChildren_eq_observed, mergeLocalizedTreeChildTables_eq_observed]
    have h2 := congrArg (List.map (fun o : LocalizedConstitutionalObservable => o.rule2)) mapEq
    apply congrArg mergeObserved
    simpa only [List.map_map, Function.comp_def,
      CertifiedLocalizedCIPInput.constitutionalObservable, constitutionalTablesKey]
      using h2.symm

/-- Declarative key lists transport along a permutation of the cursor frame, keeping the key
order: the transported derivation is at the new frame and the key list permutes accordingly. -/
private theorem declarativeKeyList_transport {fuel : Nat} :
    ∀ {left right : List (input.LocalizedRerootCursor carrierFuel)},
      left.Perm right →
      ∀ (keysLeft : List (OfficialRuleMajorKey input.Atom)),
        input.DeclarativeLocalizedRerootRuleMajorKeyList fuel left keysLeft →
        ∃ keysRight : List (OfficialRuleMajorKey input.Atom),
          input.DeclarativeLocalizedRerootRuleMajorKeyList fuel right keysRight ∧
          keysLeft.Perm keysRight := by
  intro left right permutation
  induction permutation with
  | nil =>
      intro keysLeft derivations
      cases derivations with
      | nil => exact ⟨[], DeclarativeLocalizedRerootRuleMajorKeyList.nil fuel, List.Perm.nil⟩
  | cons a perm ih =>
      intro keysLeft derivations
      cases derivations with
      | @cons _ _ _ key keys head tail =>
          rcases ih keys tail with ⟨keysRight, derivationsRight, keysPerm⟩
          exact ⟨key :: keysRight,
            DeclarativeLocalizedRerootRuleMajorKeyList.cons head derivationsRight,
            List.Perm.cons key keysPerm⟩
  | swap a b l =>
      intro keysLeft derivations
      cases derivations with
      | @cons _ _ _ key keys ka tail =>
          cases tail with
          | @cons _ _ _ key' keys' kb ktail =>
              exact ⟨key' :: key :: keys',
                DeclarativeLocalizedRerootRuleMajorKeyList.cons kb
                  (DeclarativeLocalizedRerootRuleMajorKeyList.cons ka ktail),
                (List.Perm.swap key key' keys').symm⟩
  | trans perm₁ perm₂ ih₁ ih₂ =>
      intro keysLeft derivations
      rcases ih₁ keysLeft derivations with ⟨keysMid, derivationsMid, keysPerm₁⟩
      rcases ih₂ keysMid derivationsMid with ⟨keysRight, derivationsRight, keysPerm₂⟩
      exact ⟨keysRight, derivationsRight, keysPerm₁.trans keysPerm₂⟩

/-- Pointwise internal declarative keys for a lifted child list, from per-child internal keys
given for every physical child in the parent's full child inventory.  The keys are non-junior in
physical merge order and their observables match the physical child lifts. -/
private theorem exists_declarativeKeyList_of_physicalLiftList
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (outerRoot : input.Atom)
    (rootEq : cursor.occurrence.1.root = outerRoot)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree)
    (fuel : Nat)
    (childKey : ∀ (child : PhysicalAtomTree input.Atom) (hmem : child ∈ tree.children),
      ∃ key : OfficialRuleMajorKey input.Atom,
        input.DeclarativeLocalizedRerootRuleMajorKey fuel
          (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
            tree full child hmem) key ∧
        CertifiedLocalizedCIPInput.constitutionalObservable key =
          CertifiedLocalizedCIPInput.constitutionalObservable
            (constitutionalTablesKey [] true
              (physicalLift enough singleBonded acyclic r
                (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous
                  previousEq tree full child hmem)
                (physicalLiftChildValid enough singleBonded acyclic cursor valid previous
                  previousEq tree full child hmem)
                (some (cursorAtom singleBonded acyclic cursor))
                (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous
                  previousEq tree full child hmem)
                child
                (physicalLiftChildFull enough singleBonded acyclic cursor valid previous
                  previousEq tree full child hmem)))) :
    ∀ (children : List (PhysicalAtomTree input.Atom))
      (hchildren : ∀ child ∈ children, child ∈ tree.children)
      (_childrenDescending : children.Pairwise (fun left right =>
        physicalTreeRuleMajorNotLt input.moleculeGraph outerRoot left right)),
      ∃ keys : List (OfficialRuleMajorKey input.Atom),
        input.DeclarativeLocalizedRerootRuleMajorKeyList fuel
          ((physicalLiftList enough singleBonded acyclic r cursor valid previous previousEq tree
            full children hchildren).map (fun t => t.source)) keys ∧
        (physicalLiftList enough singleBonded acyclic r cursor valid previous previousEq tree full
          children hchildren).map (fun t =>
            CertifiedLocalizedCIPInput.constitutionalObservable
              (constitutionalTablesKey [] true t)) =
          keys.map CertifiedLocalizedCIPInput.constitutionalObservable ∧
        OfficialRuleMajorKey.Descending keys := by
  intro children
  induction children with
  | nil =>
      intro hchildren _childrenDescending
      rw [physicalLiftList]
      exact ⟨[], DeclarativeLocalizedRerootRuleMajorKeyList.nil fuel, rfl, List.Pairwise.nil⟩
  | cons child rest ihList =>
      intro hchildren childrenDescending
      obtain ⟨hHeadRel, hTailPairwise⟩ := List.pairwise_cons.mp childrenDescending
      rcases childKey child (hchildren child (by simp)) with ⟨headKey, headDeriv, headObs⟩
      rcases ihList (fun c hc => hchildren c (by simp [hc])) hTailPairwise with
        ⟨restKeys, restDeriv, restObs, restDescending⟩
      rw [physicalLiftList]
      simp only [List.map_cons]
      rw [physicalLift_source enough singleBonded acyclic r
        (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous previousEq
          tree full child (hchildren child (by simp)))
        (physicalLiftChildValid enough singleBonded acyclic cursor valid previous previousEq tree
          full child (hchildren child (by simp)))
        (some (cursorAtom singleBonded acyclic cursor))
        (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous previousEq
          tree full child (hchildren child (by simp)))
        child
        (physicalLiftChildFull enough singleBonded acyclic cursor valid previous previousEq tree
          full child (hchildren child (by simp)))]
      refine ⟨headKey :: restKeys, ?_, ?_, ?_⟩
      · exact DeclarativeLocalizedRerootRuleMajorKeyList.cons headDeriv restDeriv
      · exact congrArg₂ List.cons headObs.symm restObs
      · refine List.Pairwise.cons ?_ restDescending
        intro restKey hrestKey
        have hObsMem : CertifiedLocalizedCIPInput.constitutionalObservable restKey ∈
            (physicalLiftList enough singleBonded acyclic r cursor valid previous previousEq tree
              full rest (fun c hc => hchildren c (by simp [hc]))).map (fun t =>
              CertifiedLocalizedCIPInput.constitutionalObservable
                (constitutionalTablesKey [] true t)) := by
          rw [restObs]
          exact List.mem_map.mpr ⟨restKey, hrestKey, rfl⟩
        rw [List.mem_map] at hObsMem
        rcases hObsMem with ⟨restTree, hrestTree, hObsEq⟩
        rcases physicalLiftList_mem enough singleBonded acyclic r cursor valid previous
          previousEq tree full rest (fun c hc => hchildren c (by simp [hc])) restTree hrestTree
          with ⟨c, hc, hrestTreeEq⟩
        have hRightObs : CertifiedLocalizedCIPInput.constitutionalObservable restKey =
            CertifiedLocalizedCIPInput.constitutionalObservable
              (constitutionalTablesKey [] true
                (physicalLift enough singleBonded acyclic r
                  (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous
                    previousEq tree full c (hchildren c (by simp [hc])))
                  (physicalLiftChildValid enough singleBonded acyclic cursor valid previous
                    previousEq tree full c (hchildren c (by simp [hc])))
                  (some (cursorAtom singleBonded acyclic cursor))
                  (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous
                    previousEq tree full c (hchildren c (by simp [hc])))
                  c
                  (physicalLiftChildFull enough singleBonded acyclic cursor valid previous
                    previousEq tree full c (hchildren c (by simp [hc]))))) := by
          rw [← hObsEq]
          rw [hrestTreeEq]
        have hCompareC : OfficialRuleMajorKey.compare headKey restKey =
            OfficialRuleMajorKey.compare
              (constitutionalTablesKey [] true
                (physicalLift enough singleBonded acyclic r
                  (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous
                    previousEq tree full child (hchildren child (by simp)))
                  (physicalLiftChildValid enough singleBonded acyclic cursor valid previous
                    previousEq tree full child (hchildren child (by simp)))
                  (some (cursorAtom singleBonded acyclic cursor))
                  (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous
                    previousEq tree full child (hchildren child (by simp)))
                  child
                  (physicalLiftChildFull enough singleBonded acyclic cursor valid previous
                    previousEq tree full child (hchildren child (by simp)))))
              (constitutionalTablesKey [] true
                (physicalLift enough singleBonded acyclic r
                  (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous
                    previousEq tree full c (hchildren c (by simp [hc])))
                  (physicalLiftChildValid enough singleBonded acyclic cursor valid previous
                    previousEq tree full c (hchildren c (by simp [hc])))
                  (some (cursorAtom singleBonded acyclic cursor))
                  (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous
                    previousEq tree full c (hchildren c (by simp [hc])))
                  c
                  (physicalLiftChildFull enough singleBonded acyclic cursor valid previous
                    previousEq tree full c (hchildren c (by simp [hc]))))) :=
          CertifiedLocalizedCIPInput.ruleMajor_compare_congr headKey restKey
            (constitutionalTablesKey [] true
              (physicalLift enough singleBonded acyclic r
                (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous
                  previousEq tree full child (hchildren child (by simp)))
                (physicalLiftChildValid enough singleBonded acyclic cursor valid previous
                  previousEq tree full child (hchildren child (by simp)))
                (some (cursorAtom singleBonded acyclic cursor))
                (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous
                  previousEq tree full child (hchildren child (by simp)))
                child
                (physicalLiftChildFull enough singleBonded acyclic cursor valid previous
                  previousEq tree full child (hchildren child (by simp)))))
            (constitutionalTablesKey [] true
              (physicalLift enough singleBonded acyclic r
                (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous
                  previousEq tree full c (hchildren c (by simp [hc])))
                (physicalLiftChildValid enough singleBonded acyclic cursor valid previous
                  previousEq tree full c (hchildren c (by simp [hc])))
                (some (cursorAtom singleBonded acyclic cursor))
                (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous
                  previousEq tree full c (hchildren c (by simp [hc])))
                c
                (physicalLiftChildFull enough singleBonded acyclic cursor valid previous
                  previousEq tree full c (hchildren c (by simp [hc])))))
            headObs hRightObs
        have hCompareNotLt : OfficialRuleMajorKey.compare
            (constitutionalTablesKey [] true
              (physicalLift enough singleBonded acyclic r
                (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous
                  previousEq tree full child (hchildren child (by simp)))
                (physicalLiftChildValid enough singleBonded acyclic cursor valid previous
                  previousEq tree full child (hchildren child (by simp)))
                (some (cursorAtom singleBonded acyclic cursor))
                (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous
                  previousEq tree full child (hchildren child (by simp)))
                child
                (physicalLiftChildFull enough singleBonded acyclic cursor valid previous
                  previousEq tree full child (hchildren child (by simp)))))
            (constitutionalTablesKey [] true
              (physicalLift enough singleBonded acyclic r
                (physicalLiftChildCursor enough singleBonded acyclic cursor valid previous
                  previousEq tree full c (hchildren c (by simp [hc])))
                (physicalLiftChildValid enough singleBonded acyclic cursor valid previous
                  previousEq tree full c (hchildren c (by simp [hc])))
                (some (cursorAtom singleBonded acyclic cursor))
                (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid previous
                  previousEq tree full c (hchildren c (by simp [hc])))
                c
                (physicalLiftChildFull enough singleBonded acyclic cursor valid previous
                  previousEq tree full c (hchildren c (by simp [hc]))))) ≠ Ordering.lt :=
          compare_not_lt_of_lift_physical_notLt enough singleBonded acyclic outerRoot r cursor
            valid previous previousEq rootEq tree full child c (hchildren child (by simp))
            (hchildren c (by simp [hc])) (hHeadRel c hc)
        exact fun hLt => hCompareNotLt (hCompareC.symm.trans hLt)

/-- **Internal declarative keys from independent physical descent.**  At a valid actual incoming
cursor over the original `outerRoot`, every full descending physical incoming-cut tree at that
cursor (with the bound previous atom) admits, for any fuel at least its height, an internal
`DeclarativeLocalizedRerootRuleMajorKey` whose constitutional observable is exactly the lifted
tree's table observable.  The internal key is used only to transfer uniqueness; the public
criterion remains graph-only. -/
theorem exists_declarativeKey_of_physicalLift
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (outerRoot : input.Atom)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : Option input.Atom)
    (previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous)
    (rootEq : cursor.occurrence.1.root = outerRoot)
    (tree : PhysicalAtomTree input.Atom)
    (full : PhysicalFullCutTree input.moleculeGraph previous
      (cursorAtom singleBonded acyclic cursor) tree)
    (descending : PhysicalTreeSiblingDescending input.moleculeGraph outerRoot tree)
    (fuel : Nat) (hfuel : PhysicalAtomTree.height tree ≤ fuel) :
    ∃ key : OfficialRuleMajorKey input.Atom,
      input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key ∧
      CertifiedLocalizedCIPInput.constitutionalObservable key =
        CertifiedLocalizedCIPInput.constitutionalObservable
          (constitutionalTablesKey [] true
            (physicalLift enough singleBonded acyclic r cursor valid previous previousEq tree
              full)) := by
  have main : ∀ outerRoot : input.Atom, ∀ n : Nat, ∀ candidate : PhysicalAtomTree input.Atom,
      PhysicalAtomTree.height candidate ≤ n →
      ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      ∀ valid : input.LocalizedRerootCursorValid cursor,
      ∀ previous : Option input.Atom,
      ∀ previousEq : cursor.previous?.bind (fun p => p.1.node.current?) = previous,
      ∀ rootEq : cursor.occurrence.1.root = outerRoot,
      ∀ full : PhysicalFullCutTree input.moleculeGraph previous
        (cursorAtom singleBonded acyclic cursor) candidate,
      ∀ descending : PhysicalTreeSiblingDescending input.moleculeGraph outerRoot candidate,
      ∀ fuel : Nat, PhysicalAtomTree.height candidate ≤ fuel →
      ∃ key : OfficialRuleMajorKey input.Atom,
        input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key ∧
        CertifiedLocalizedCIPInput.constitutionalObservable key =
          CertifiedLocalizedCIPInput.constitutionalObservable
            (constitutionalTablesKey [] true
              (physicalLift enough singleBonded acyclic r cursor valid previous previousEq
                candidate full)) := by
    intro outerRoot n
    refine Nat.strong_induction_on n ?_
    intro k inductionHypothesis candidate bound cursor valid previous previousEq rootEq full
      descending fuel hfuel
    cases fuel with
    | zero =>
        cases candidate with
        | mk root children =>
            rw [PhysicalAtomTree.height_mk] at hfuel
            omega
    | succ fuel' =>
        cases candidate with
        | mk root children =>
            have hChildrenHeights : PhysicalAtomTree.childrenHeights children ≤ fuel' := by
              rw [PhysicalAtomTree.height_mk] at hfuel
              omega
            have childBounds : ∀ (child : PhysicalAtomTree input.Atom), child ∈ children →
                PhysicalAtomTree.height child ≤ fuel' := by
              intro child hmem
              exact (PhysicalAtomTree.childrenHeights_le_of_mem children child hmem).trans
                hChildrenHeights
            cases children with
            | nil =>
                have hExecEmpty : input.executableLocalizedRerootChildren cursor = [] := by
                  have hPerm : List.Perm
                      ((physicalLiftList enough singleBonded acyclic r cursor valid previous
                        previousEq ⟨root, []⟩ full [] (fun _ h => h)).map (fun t => t.source))
                      (input.executableLocalizedRerootChildren cursor) :=
                    physicalLiftList_sourcePerm enough singleBonded acyclic r cursor valid
                      previous previousEq ⟨root, []⟩ full
                  rw [physicalLiftList] at hPerm
                  exact List.Perm.eq_nil hPerm.symm
                refine ⟨input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node
                  true, ?_, ?_⟩
                · exact DeclarativeLocalizedRerootRuleMajorKey.terminal
                    (input.localizedRerootChildren?_sound cursor
                      (input.executableLocalizedRerootChildren cursor)
                      (input.localizedRerootChildren?_eq_some_executable cursor)) hExecEmpty
                · rw [physicalLift]
                  simp only [physicalLiftList]
                  exact terminalKey_observable_eq_lift cursor (r cursor)
            | cons child rest =>
                cases descending with
                | mk _tree siblings childDescending =>
                    have hPhysPermFrame : List.Perm
                        ((physicalLiftList enough singleBonded acyclic r cursor valid previous
                          previousEq ⟨root, child :: rest⟩ full (child :: rest)
                          (fun _ h => h)).map (fun t => t.source))
                        (input.executableLocalizedRerootChildren cursor) :=
                      physicalLiftList_sourcePerm enough singleBonded acyclic r cursor valid
                        previous previousEq ⟨root, child :: rest⟩ full
                    obtain ⟨keysPhys, derivationsPhys, obsMapPhys, hKeysDescending⟩ :=
                      exists_declarativeKeyList_of_physicalLiftList enough singleBonded acyclic r
                        cursor valid previous previousEq outerRoot rootEq ⟨root, child :: rest⟩
                        full fuel'
                        (fun descendant hmem =>
                          inductionHypothesis (PhysicalAtomTree.height descendant)
                            (by
                              have hle := PhysicalAtomTree.height_child_le
                                ⟨root, child :: rest⟩ descendant hmem
                              omega)
                            descendant (le_refl _)
                            (physicalLiftChildCursor enough singleBonded acyclic cursor valid
                              previous previousEq ⟨root, child :: rest⟩ full descendant hmem)
                            (physicalLiftChildValid enough singleBonded acyclic cursor valid
                              previous previousEq ⟨root, child :: rest⟩ full descendant hmem)
                            (some (cursorAtom singleBonded acyclic cursor))
                            (physicalLiftChildPrevEq enough singleBonded acyclic cursor valid
                              previous previousEq ⟨root, child :: rest⟩ full descendant hmem)
                            (physicalLiftChildRoot_eq enough singleBonded acyclic outerRoot cursor
                              valid previous previousEq rootEq ⟨root, child :: rest⟩ full
                              descendant hmem)
                            (physicalLiftChildFull enough singleBonded acyclic cursor valid
                              previous previousEq ⟨root, child :: rest⟩ full descendant hmem)
                            (childDescending descendant hmem) fuel'
                            (childBounds descendant hmem))
                        (child :: rest) (fun _ h => h) siblings
                    obtain ⟨keysFrame, derivationsFrame, keysPerm⟩ :=
                      declarativeKeyList_transport hPhysPermFrame keysPhys derivationsPhys
                    have hExecNonempty : input.executableLocalizedRerootChildren cursor ≠ [] := by
                      intro hExecNil
                      have hPermEmpty : List.Perm
                          ((physicalLiftList enough singleBonded acyclic r cursor valid previous
                            previousEq ⟨root, child :: rest⟩ full (child :: rest)
                            (fun _ h => h)).map (fun t => t.source)) [] := by
                        simpa only [hExecNil] using hPhysPermFrame
                      rw [physicalLiftList] at hPermEmpty
                      simp only [List.map_cons] at hPermEmpty
                      cases List.Perm.eq_nil hPermEmpty
                    refine ⟨OfficialRuleMajorKey.assemble
                        (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node
                          false) keysPhys, ?_, ?_⟩
                    · exact DeclarativeLocalizedRerootRuleMajorKey.branch
                        (input.localizedRerootChildren?_sound cursor
                          (input.executableLocalizedRerootChildren cursor)
                          (input.localizedRerootChildren?_eq_some_executable cursor))
                        hExecNonempty derivationsFrame keysPerm hKeysDescending
                    · rw [physicalLift]
                      exact assembled_observable_eq_liftTables cursor (r cursor) keysPhys
                        (physicalLiftList enough singleBonded acyclic r cursor valid previous
                          previousEq ⟨root, child :: rest⟩ full (child :: rest) (fun _ h => h))
                        obsMapPhys
  exact main outerRoot (PhysicalAtomTree.height tree) tree (le_refl _) cursor valid previous
    previousEq rootEq full descending fuel hfuel







theorem physicalTreeRuleMajorOutcome_admissible_congr
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (r : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (outerRoot : input.Atom)
    (cursorLeft cursorRight : input.LocalizedRerootCursor carrierFuel)
    (validLeft : input.LocalizedRerootCursorValid cursorLeft)
    (validRight : input.LocalizedRerootCursorValid cursorRight)
    (previousLeft previousRight : Option input.Atom)
    (previousEqLeft : cursorLeft.previous?.bind (fun p => p.1.node.current?) = previousLeft)
    (previousEqRight : cursorRight.previous?.bind (fun p => p.1.node.current?) = previousRight)
    (rootEqLeft : cursorLeft.occurrence.1.root = outerRoot)
    (rootEqRight : cursorRight.occurrence.1.root = outerRoot)
    (treeLeft treeLeft' : PhysicalAtomTree input.Atom)
    (fullLeft : PhysicalFullCutTree input.moleculeGraph previousLeft
      (cursorAtom singleBonded acyclic cursorLeft) treeLeft)
    (descendingLeft : PhysicalTreeSiblingDescending input.moleculeGraph outerRoot treeLeft)
    (fullLeft' : PhysicalFullCutTree input.moleculeGraph previousLeft
      (cursorAtom singleBonded acyclic cursorLeft) treeLeft')
    (descendingLeft' : PhysicalTreeSiblingDescending input.moleculeGraph outerRoot treeLeft')
    (treeRight treeRight' : PhysicalAtomTree input.Atom)
    (fullRight : PhysicalFullCutTree input.moleculeGraph previousRight
      (cursorAtom singleBonded acyclic cursorRight) treeRight)
    (descendingRight : PhysicalTreeSiblingDescending input.moleculeGraph outerRoot treeRight)
    (fullRight' : PhysicalFullCutTree input.moleculeGraph previousRight
      (cursorAtom singleBonded acyclic cursorRight) treeRight')
    (descendingRight' : PhysicalTreeSiblingDescending input.moleculeGraph outerRoot treeRight') :
    ∀ outcome : Ordering,
      physicalTreeRuleMajorOutcome input.moleculeGraph outerRoot treeLeft treeRight outcome ↔
        physicalTreeRuleMajorOutcome input.moleculeGraph outerRoot treeLeft' treeRight' outcome := by
  intro outcome
  rcases exists_declarativeKey_of_physicalLift enough singleBonded acyclic r outerRoot cursorLeft
      validLeft previousLeft previousEqLeft rootEqLeft treeLeft fullLeft descendingLeft
      (PhysicalAtomTree.height treeLeft + PhysicalAtomTree.height treeRight +
        PhysicalAtomTree.height treeLeft' + PhysicalAtomTree.height treeRight')
      (by omega) with ⟨keyLeft, derivLeft, obsLeft⟩
  rcases exists_declarativeKey_of_physicalLift enough singleBonded acyclic r outerRoot cursorLeft
      validLeft previousLeft previousEqLeft rootEqLeft treeLeft' fullLeft' descendingLeft'
      (PhysicalAtomTree.height treeLeft + PhysicalAtomTree.height treeRight +
        PhysicalAtomTree.height treeLeft' + PhysicalAtomTree.height treeRight')
      (by omega) with ⟨keyLeft', derivLeft', obsLeft'⟩
  rcases exists_declarativeKey_of_physicalLift enough singleBonded acyclic r outerRoot
      cursorRight validRight previousRight previousEqRight rootEqRight treeRight fullRight
      descendingRight
      (PhysicalAtomTree.height treeLeft + PhysicalAtomTree.height treeRight +
        PhysicalAtomTree.height treeLeft' + PhysicalAtomTree.height treeRight')
      (by omega) with ⟨keyRight, derivRight, obsRight⟩
  rcases exists_declarativeKey_of_physicalLift enough singleBonded acyclic r outerRoot
      cursorRight validRight previousRight previousEqRight rootEqRight treeRight' fullRight'
      descendingRight'
      (PhysicalAtomTree.height treeLeft + PhysicalAtomTree.height treeRight +
        PhysicalAtomTree.height treeLeft' + PhysicalAtomTree.height treeRight')
      (by omega) with ⟨keyRight', derivRight', obsRight'⟩
  have hLeftObs : CertifiedLocalizedCIPInput.constitutionalObservable keyLeft =
      CertifiedLocalizedCIPInput.constitutionalObservable keyLeft' :=
    input.declarative_constitutional_observable_unique
      (PhysicalAtomTree.height treeLeft + PhysicalAtomTree.height treeRight +
        PhysicalAtomTree.height treeLeft' + PhysicalAtomTree.height treeRight')
      (PhysicalAtomTree.height treeLeft + PhysicalAtomTree.height treeRight +
        PhysicalAtomTree.height treeLeft' + PhysicalAtomTree.height treeRight')
      cursorLeft keyLeft keyLeft' derivLeft derivLeft'
  have hRightObs : CertifiedLocalizedCIPInput.constitutionalObservable keyRight =
      CertifiedLocalizedCIPInput.constitutionalObservable keyRight' :=
    input.declarative_constitutional_observable_unique
      (PhysicalAtomTree.height treeLeft + PhysicalAtomTree.height treeRight +
        PhysicalAtomTree.height treeLeft' + PhysicalAtomTree.height treeRight')
      (PhysicalAtomTree.height treeLeft + PhysicalAtomTree.height treeRight +
        PhysicalAtomTree.height treeLeft' + PhysicalAtomTree.height treeRight')
      cursorRight keyRight keyRight' derivRight derivRight'
  have hKeyCompare : OfficialRuleMajorKey.compare keyLeft keyRight =
      OfficialRuleMajorKey.compare keyLeft' keyRight' :=
    CertifiedLocalizedCIPInput.ruleMajor_compare_congr keyLeft keyRight keyLeft' keyRight'
      hLeftObs hRightObs
  have hLeftTree : OfficialRuleMajorKey.compare keyLeft keyRight =
      OfficialRuleMajorKey.compare
        (constitutionalTablesKey [] true
          (physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft
            previousEqLeft treeLeft fullLeft))
        (constitutionalTablesKey [] true
          (physicalLift enough singleBonded acyclic r cursorRight validRight previousRight
            previousEqRight treeRight fullRight)) :=
    CertifiedLocalizedCIPInput.ruleMajor_compare_congr keyLeft keyRight
      (constitutionalTablesKey [] true
        (physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft
          previousEqLeft treeLeft fullLeft))
      (constitutionalTablesKey [] true
        (physicalLift enough singleBonded acyclic r cursorRight validRight previousRight
          previousEqRight treeRight fullRight)) obsLeft obsRight
  have hLeftTree' : OfficialRuleMajorKey.compare keyLeft' keyRight' =
      OfficialRuleMajorKey.compare
        (constitutionalTablesKey [] true
          (physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft
            previousEqLeft treeLeft' fullLeft'))
        (constitutionalTablesKey [] true
          (physicalLift enough singleBonded acyclic r cursorRight validRight previousRight
            previousEqRight treeRight' fullRight')) :=
    CertifiedLocalizedCIPInput.ruleMajor_compare_congr keyLeft' keyRight'
      (constitutionalTablesKey [] true
        (physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft
          previousEqLeft treeLeft' fullLeft'))
      (constitutionalTablesKey [] true
        (physicalLift enough singleBonded acyclic r cursorRight validRight previousRight
          previousEqRight treeRight' fullRight')) obsLeft' obsRight'
  have hCompareTransfer : OfficialRuleMajorKey.compare
      (constitutionalTablesKey [] true
        (physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft
          previousEqLeft treeLeft fullLeft))
      (constitutionalTablesKey [] true
        (physicalLift enough singleBonded acyclic r cursorRight validRight previousRight
          previousEqRight treeRight fullRight)) =
    OfficialRuleMajorKey.compare
      (constitutionalTablesKey [] true
        (physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft
          previousEqLeft treeLeft' fullLeft'))
      (constitutionalTablesKey [] true
        (physicalLift enough singleBonded acyclic r cursorRight validRight previousRight
          previousEqRight treeRight' fullRight')) :=
    (hLeftTree.symm.trans hKeyCompare).trans hLeftTree'
  constructor
  · intro hTree
    have hTreeLift : physicalRuleMajorOutcome singleBonded acyclic outerRoot
        (physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft
          previousEqLeft treeLeft fullLeft)
        (physicalLift enough singleBonded acyclic r cursorRight validRight previousRight
          previousEqRight treeRight fullRight) outcome :=
      (physicalTreeRuleMajorOutcome_eq_lift enough singleBonded acyclic outerRoot r
        cursorLeft validLeft previousLeft previousEqLeft treeLeft fullLeft
        cursorRight validRight previousRight previousEqRight treeRight fullRight outcome).mp hTree
    have hTables : OfficialRuleMajorKey.compare
        (constitutionalTablesKey [] true
          (physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft
            previousEqLeft treeLeft fullLeft))
        (constitutionalTablesKey [] true
          (physicalLift enough singleBonded acyclic r cursorRight validRight previousRight
            previousEqRight treeRight fullRight)) = outcome :=
      (compare_tables_eq_iff_physicalRuleMajorOutcome singleBonded acyclic
        (physicalLift_realizes enough singleBonded acyclic r cursorLeft validLeft previousLeft
          previousEqLeft treeLeft fullLeft)
        (physicalLift_realizes enough singleBonded acyclic r cursorRight validRight previousRight
          previousEqRight treeRight fullRight)
        outerRoot
        (by
          rw [physicalLift_source enough singleBonded acyclic r cursorLeft validLeft previousLeft
            previousEqLeft treeLeft fullLeft]
          exact rootEqLeft)
        (by
          rw [physicalLift_source enough singleBonded acyclic r cursorRight validRight
            previousRight previousEqRight treeRight fullRight]
          exact rootEqRight) outcome).mpr hTreeLift
    have hTables' : OfficialRuleMajorKey.compare
        (constitutionalTablesKey [] true
          (physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft
            previousEqLeft treeLeft' fullLeft'))
        (constitutionalTablesKey [] true
          (physicalLift enough singleBonded acyclic r cursorRight validRight previousRight
            previousEqRight treeRight' fullRight')) = outcome :=
      hCompareTransfer.symm.trans hTables
    have hTreeLift' : physicalRuleMajorOutcome singleBonded acyclic outerRoot
        (physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft
          previousEqLeft treeLeft' fullLeft')
        (physicalLift enough singleBonded acyclic r cursorRight validRight previousRight
          previousEqRight treeRight' fullRight') outcome :=
      (compare_tables_eq_iff_physicalRuleMajorOutcome singleBonded acyclic
        (physicalLift_realizes enough singleBonded acyclic r cursorLeft validLeft previousLeft
          previousEqLeft treeLeft' fullLeft')
        (physicalLift_realizes enough singleBonded acyclic r cursorRight validRight previousRight
          previousEqRight treeRight' fullRight')
        outerRoot
        (by
          rw [physicalLift_source enough singleBonded acyclic r cursorLeft validLeft previousLeft
            previousEqLeft treeLeft' fullLeft']
          exact rootEqLeft)
        (by
          rw [physicalLift_source enough singleBonded acyclic r cursorRight validRight
            previousRight previousEqRight treeRight' fullRight']
          exact rootEqRight) outcome).mp hTables'
    exact (physicalTreeRuleMajorOutcome_eq_lift enough singleBonded acyclic outerRoot r
      cursorLeft validLeft previousLeft previousEqLeft treeLeft' fullLeft'
      cursorRight validRight previousRight previousEqRight treeRight' fullRight'
      outcome).mpr hTreeLift'
  · intro hTree'
    have hTreeLift' : physicalRuleMajorOutcome singleBonded acyclic outerRoot
        (physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft
          previousEqLeft treeLeft' fullLeft')
        (physicalLift enough singleBonded acyclic r cursorRight validRight previousRight
          previousEqRight treeRight' fullRight') outcome :=
      (physicalTreeRuleMajorOutcome_eq_lift enough singleBonded acyclic outerRoot r
        cursorLeft validLeft previousLeft previousEqLeft treeLeft' fullLeft'
        cursorRight validRight previousRight previousEqRight treeRight' fullRight'
        outcome).mp hTree'
    have hTables' : OfficialRuleMajorKey.compare
        (constitutionalTablesKey [] true
          (physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft
            previousEqLeft treeLeft' fullLeft'))
        (constitutionalTablesKey [] true
          (physicalLift enough singleBonded acyclic r cursorRight validRight previousRight
            previousEqRight treeRight' fullRight')) = outcome :=
      (compare_tables_eq_iff_physicalRuleMajorOutcome singleBonded acyclic
        (physicalLift_realizes enough singleBonded acyclic r cursorLeft validLeft previousLeft
          previousEqLeft treeLeft' fullLeft')
        (physicalLift_realizes enough singleBonded acyclic r cursorRight validRight previousRight
          previousEqRight treeRight' fullRight')
        outerRoot
        (by
          rw [physicalLift_source enough singleBonded acyclic r cursorLeft validLeft previousLeft
            previousEqLeft treeLeft' fullLeft']
          exact rootEqLeft)
        (by
          rw [physicalLift_source enough singleBonded acyclic r cursorRight validRight
            previousRight previousEqRight treeRight' fullRight']
          exact rootEqRight) outcome).mpr hTreeLift'
    have hTables : OfficialRuleMajorKey.compare
        (constitutionalTablesKey [] true
          (physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft
            previousEqLeft treeLeft fullLeft))
        (constitutionalTablesKey [] true
          (physicalLift enough singleBonded acyclic r cursorRight validRight previousRight
            previousEqRight treeRight fullRight)) = outcome :=
      hCompareTransfer.trans hTables'
    have hTreeLift : physicalRuleMajorOutcome singleBonded acyclic outerRoot
        (physicalLift enough singleBonded acyclic r cursorLeft validLeft previousLeft
          previousEqLeft treeLeft fullLeft)
        (physicalLift enough singleBonded acyclic r cursorRight validRight previousRight
          previousEqRight treeRight fullRight) outcome :=
      (compare_tables_eq_iff_physicalRuleMajorOutcome singleBonded acyclic
        (physicalLift_realizes enough singleBonded acyclic r cursorLeft validLeft previousLeft
          previousEqLeft treeLeft fullLeft)
        (physicalLift_realizes enough singleBonded acyclic r cursorRight validRight previousRight
          previousEqRight treeRight fullRight)
        outerRoot
        (by
          rw [physicalLift_source enough singleBonded acyclic r cursorLeft validLeft previousLeft
            previousEqLeft treeLeft fullLeft]
          exact rootEqLeft)
        (by
          rw [physicalLift_source enough singleBonded acyclic r cursorRight validRight previousRight
            previousEqRight treeRight fullRight]
          exact rootEqRight) outcome).mp hTables
    exact (physicalTreeRuleMajorOutcome_eq_lift enough singleBonded acyclic outerRoot r
      cursorLeft validLeft previousLeft previousEqLeft treeLeft fullLeft
      cursorRight validRight previousRight previousEqRight treeRight fullRight
      outcome).mpr hTreeLift

/-! ## I. Actual evaluator agreement export -/










theorem physicalTreeCanonicalOutcome_iff_actualComparison
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (outerRoot : input.Atom)
    (cursorLeft cursorRight : input.LocalizedRerootCursor carrierFuel)
    (validLeft : input.LocalizedRerootCursorValid cursorLeft)
    (validRight : input.LocalizedRerootCursorValid cursorRight)
    (rootEqLeft : cursorLeft.occurrence.1.root = outerRoot)
    (rootEqRight : cursorRight.occurrence.1.root = outerRoot)
    (leftKey rightKey : input.LocalizedRerootCumulativeRule45Key)
    (leftBuilt : input.buildLocalizedRerootCumulativeRule45Key? stage target view
      (2 * (carrierFuel + 1)) cursorLeft = some leftKey)
    (rightBuilt : input.buildLocalizedRerootCumulativeRule45Key? stage target view
      (2 * (carrierFuel + 1)) cursorRight = some rightKey) :
    ∀ outcome : Ordering,
      OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional = outcome ↔
        PhysicalTreeCanonicalOutcome input.moleculeGraph outerRoot
          (cursorLeft.previous?.bind (fun p => p.1.node.current?))
          (cursorRight.previous?.bind (fun p => p.1.node.current?))
          (cursorAtom singleBonded acyclic cursorLeft)
          (cursorAtom singleBonded acyclic cursorRight) outcome := by
  intro outcome
  have leftWithRead : input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
      (fun occurrence => input.localizedDependencyLabel target view occurrence)
      (2 * (carrierFuel + 1)) cursorLeft = some leftKey := by
    rw [input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel stage
      target view]
    exact leftBuilt
  have rightWithRead : input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
      (fun occurrence => input.localizedDependencyLabel target view occurrence)
      (2 * (carrierFuel + 1)) cursorRight = some rightKey := by
    rw [input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel stage
      target view]
    exact rightBuilt
  rcases exists_trace_of_buildWithRead input stage
      (fun occurrence => input.localizedDependencyLabel target view occurrence)
      (2 * (carrierFuel + 1)) cursorLeft leftKey leftWithRead with
    ⟨leftTree, leftSource, leftTrace⟩
  rcases exists_trace_of_buildWithRead input stage
      (fun occurrence => input.localizedDependencyLabel target view occurrence)
      (2 * (carrierFuel + 1)) cursorRight rightKey rightWithRead with
    ⟨rightTree, rightSource, rightTrace⟩
  have leftRealizes : LocalizedCumulativeTreeRealizes input
      (fun occurrence => input.localizedDependencyLabel target view occurrence) leftTree :=
    LocalizedActualRecursiveSortTrace.realizes_of_trace leftTrace
  have rightRealizes : LocalizedCumulativeTreeRealizes input
      (fun occurrence => input.localizedDependencyLabel target view occurrence) rightTree :=
    LocalizedActualRecursiveSortTrace.realizes_of_trace rightTrace
  have leftDescending : PhysicalSiblingDescending singleBonded acyclic outerRoot leftTree :=
    physicalSiblingDescending_of_trace singleBonded acyclic outerRoot
      (2 * (carrierFuel + 1)) leftTree leftKey (by simpa [leftSource] using rootEqLeft) leftTrace
  have rightDescending : PhysicalSiblingDescending singleBonded acyclic outerRoot rightTree :=
    physicalSiblingDescending_of_trace singleBonded acyclic outerRoot
      (2 * (carrierFuel + 1)) rightTree rightKey (by simpa [rightSource] using rootEqRight)
      rightTrace
  have leftAdmissible : PhysicalIncomingCutAdmissible input.moleculeGraph outerRoot
      (cursorLeft.previous?.bind (fun p => p.1.node.current?))
      (cursorAtom singleBonded acyclic cursorLeft)
      (physicalErasure singleBonded acyclic leftTree) :=
    physicalIncomingCutAdmissible_of_erasure enough singleBonded acyclic leftRealizes
      (by rw [leftSource]; exact validLeft) outerRoot leftDescending
      (cursorLeft.previous?.bind (fun p => p.1.node.current?)) (by rw [leftSource])
      (cursorAtom singleBonded acyclic cursorLeft)
      (by
        apply nodeAtom_eq_of_observed singleBonded acyclic
        rw [leftSource]
        exact cursorAtom_spec singleBonded acyclic cursorLeft)
  have rightAdmissible : PhysicalIncomingCutAdmissible input.moleculeGraph outerRoot
      (cursorRight.previous?.bind (fun p => p.1.node.current?))
      (cursorAtom singleBonded acyclic cursorRight)
      (physicalErasure singleBonded acyclic rightTree) :=
    physicalIncomingCutAdmissible_of_erasure enough singleBonded acyclic rightRealizes
      (by rw [rightSource]; exact validRight) outerRoot rightDescending
      (cursorRight.previous?.bind (fun p => p.1.node.current?)) (by rw [rightSource])
      (cursorAtom singleBonded acyclic cursorRight)
      (by
        apply nodeAtom_eq_of_observed singleBonded acyclic
        rw [rightSource]
        exact cursorAtom_spec singleBonded acyclic cursorRight)
  constructor
  · intro hCompare
    have hPhysical : physicalTreeRuleMajorOutcome input.moleculeGraph outerRoot
        (physicalErasure singleBonded acyclic leftTree)
        (physicalErasure singleBonded acyclic rightTree) outcome := by
      apply (physicalTreeRuleMajorOutcome_eq_erasure singleBonded acyclic outerRoot leftTree
        rightTree outcome).mpr
      apply (compare_eq_iff_physicalRuleMajorOutcome singleBonded acyclic
        (LocalizedActualRecursiveSortTrace.fullMatch_of_trace leftTrace).tableMatch
        (LocalizedActualRecursiveSortTrace.fullMatch_of_trace rightTrace).tableMatch
        leftRealizes rightRealizes outerRoot
        (by simpa [leftSource] using rootEqLeft)
        (by simpa [rightSource] using rootEqRight) outcome).mp
      exact hCompare
    refine ⟨⟨physicalErasure singleBonded acyclic leftTree, leftAdmissible⟩,
      ⟨physicalErasure singleBonded acyclic rightTree, rightAdmissible⟩, ?_⟩
    intro leftTreeP rightTreeP leftAdmissibleP rightAdmissibleP
    have hTransfer := physicalTreeRuleMajorOutcome_admissible_congr enough singleBonded acyclic
      (fun occurrence => input.localizedDependencyLabel target view occurrence) outerRoot
      cursorLeft cursorRight validLeft validRight
      (cursorLeft.previous?.bind (fun p => p.1.node.current?))
      (cursorRight.previous?.bind (fun p => p.1.node.current?))
      rfl rfl rootEqLeft rootEqRight
      leftTreeP (physicalErasure singleBonded acyclic leftTree)
      leftAdmissibleP.full leftAdmissibleP.descending leftAdmissible.full leftAdmissible.descending
      rightTreeP (physicalErasure singleBonded acyclic rightTree)
      rightAdmissibleP.full rightAdmissibleP.descending rightAdmissible.full
      rightAdmissible.descending
    exact (hTransfer outcome).mpr hPhysical
  · intro hCanonical
    rcases hCanonical with ⟨⟨leftTreeP, leftAdmissibleP⟩, ⟨rightTreeP, rightAdmissibleP⟩, hAll⟩
    have hPhysical : physicalTreeRuleMajorOutcome input.moleculeGraph outerRoot
        (physicalErasure singleBonded acyclic leftTree)
        (physicalErasure singleBonded acyclic rightTree) outcome :=
      hAll (physicalErasure singleBonded acyclic leftTree)
        (physicalErasure singleBonded acyclic rightTree) leftAdmissible rightAdmissible
    have hActual : physicalRuleMajorOutcome singleBonded acyclic outerRoot leftTree rightTree
        outcome :=
      (physicalTreeRuleMajorOutcome_eq_erasure singleBonded acyclic outerRoot leftTree rightTree
        outcome).mp hPhysical
    exact (compare_eq_iff_physicalRuleMajorOutcome singleBonded acyclic
      (LocalizedActualRecursiveSortTrace.fullMatch_of_trace leftTrace).tableMatch
      (LocalizedActualRecursiveSortTrace.fullMatch_of_trace rightTrace).tableMatch
      leftRealizes rightRealizes outerRoot
      (by simpa [leftSource] using rootEqLeft)
      (by simpa [rightSource] using rootEqRight) outcome).mpr hActual









theorem exists_physicalTreeCanonicalOutcome_iff_actualComparison
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (outerRoot : input.Atom)
    (cursorLeft cursorRight : input.LocalizedRerootCursor carrierFuel)
    (validLeft : input.LocalizedRerootCursorValid cursorLeft)
    (validRight : input.LocalizedRerootCursorValid cursorRight)
    (rootEqLeft : cursorLeft.occurrence.1.root = outerRoot)
    (rootEqRight : cursorRight.occurrence.1.root = outerRoot) :
    ∃ leftKey rightKey,
      input.buildLocalizedRerootCumulativeRule45Key? stage target view
        (2 * (carrierFuel + 1)) cursorLeft = some leftKey ∧
      input.buildLocalizedRerootCumulativeRule45Key? stage target view
        (2 * (carrierFuel + 1)) cursorRight = some rightKey ∧
      ∀ outcome : Ordering,
        OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional = outcome ↔
          PhysicalTreeCanonicalOutcome input.moleculeGraph outerRoot
            (cursorLeft.previous?.bind (fun p => p.1.node.current?))
            (cursorRight.previous?.bind (fun p => p.1.node.current?))
            (cursorAtom singleBonded acyclic cursorLeft)
            (cursorAtom singleBonded acyclic cursorRight) outcome := by
  rcases input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice stage target view
    cursorLeft validLeft with ⟨leftKey, leftBuilt⟩
  rcases input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice stage target view
    cursorRight validRight with ⟨rightKey, rightBuilt⟩
  exact ⟨leftKey, rightKey, leftBuilt, rightBuilt, fun outcome =>
    physicalTreeCanonicalOutcome_iff_actualComparison enough singleBonded acyclic stage target
      view outerRoot cursorLeft cursorRight validLeft validRight rootEqLeft rootEqRight leftKey
      rightKey leftBuilt rightBuilt outcome⟩

end PhysicalLift

/-! ## Kernel guards -/

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.subtreeAt?
assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.subtreeAt?_nil
assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.subtreeAt?_cons
assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.subtreeAt?_append
assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.subtreeAt?_cons_eq_some_iff
assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.occupiedAddresses
assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.occupiedChildrenAddresses
assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.occupiedAddresses_mk
assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.occupiedChildrenAddresses_nil
assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.occupiedChildrenAddresses_cons
assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.mem_occupiedChildrenAddresses_of_getElem?
assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.subtreeAt?_none_of_not_mem_occupied
assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.height
assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.childrenHeights
assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.height_mk
assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.childrenHeights_nil
assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.childrenHeights_cons
assert_kernel_only TetraStereo.OneCenter.PhysicalAtomTree.height_child_le
assert_kernel_only TetraStereo.OneCenter.physicalTreeAtomicNumberAt
assert_kernel_only TetraStereo.OneCenter.physicalTreeOuterRootDistanceAt
assert_kernel_only TetraStereo.OneCenter.physicalTreeAtomMassAt
assert_kernel_only TetraStereo.OneCenter.physicalTreeRuleMajorOutcome
assert_kernel_only TetraStereo.OneCenter.physicalTreeRuleMajorNotLt
assert_kernel_only TetraStereo.OneCenter.PhysicalCutExcludes
assert_kernel_only TetraStereo.OneCenter.PhysicalFullCutTree
assert_kernel_only TetraStereo.OneCenter.PhysicalFullCutTree.children_some
assert_kernel_only TetraStereo.OneCenter.PhysicalTreeSiblingDescending
assert_kernel_only TetraStereo.OneCenter.PhysicalIncomingCutAdmissible
assert_kernel_only TetraStereo.OneCenter.PhysicalTreeCanonicalOutcome
assert_kernel_only TetraStereo.OneCenter.physicalTreeRuleMajorOutcome_functional
assert_kernel_only TetraStereo.OneCenter.physicalTreeRuleMajorOutcome_total
assert_kernel_only TetraStereo.OneCenter.physicalErasure
assert_kernel_only TetraStereo.OneCenter.physicalErasureChildren
assert_kernel_only TetraStereo.OneCenter.physicalErasure_def
assert_kernel_only TetraStereo.OneCenter.physicalErasureChildren_eq_map
assert_kernel_only TetraStereo.OneCenter.subtreeAt?_physicalErasure
assert_kernel_only TetraStereo.OneCenter.physicalTreeAtomicNumberAt_eq_erasure
assert_kernel_only TetraStereo.OneCenter.physicalTreeOuterRootDistanceAt_eq_erasure
assert_kernel_only TetraStereo.OneCenter.physicalTreeAtomMassAt_eq_erasure
assert_kernel_only TetraStereo.OneCenter.physicalTreeRuleMajorOutcome_eq_erasure
assert_kernel_only TetraStereo.OneCenter.physicalTreeRuleMajorNotLt_eq_erasure
assert_kernel_only TetraStereo.OneCenter.physicalTreeSiblingDescending_of_erasure
assert_kernel_only TetraStereo.OneCenter.physicalErasure_full
assert_kernel_only TetraStereo.OneCenter.physicalIncomingCutAdmissible_of_erasure
assert_kernel_only TetraStereo.OneCenter.cursorAtom
assert_kernel_only TetraStereo.OneCenter.cursorAtom_spec
assert_kernel_only TetraStereo.OneCenter.cursorAtom_eq_of_observed
assert_kernel_only TetraStereo.OneCenter.physicalChildCursor
assert_kernel_only TetraStereo.OneCenter.physicalChildCursor_observed
assert_kernel_only TetraStereo.OneCenter.physicalChildCursor_mem
assert_kernel_only TetraStereo.OneCenter.physicalChildAdjEx
assert_kernel_only TetraStereo.OneCenter.physicalLiftChildCursor
assert_kernel_only TetraStereo.OneCenter.physicalLiftChildValid
assert_kernel_only TetraStereo.OneCenter.physicalLiftChildPrevEq
assert_kernel_only TetraStereo.OneCenter.physicalLiftChildFull
assert_kernel_only TetraStereo.OneCenter.physicalLift
assert_kernel_only TetraStereo.OneCenter.physicalLiftList
assert_kernel_only TetraStereo.OneCenter.physicalLift_source
assert_kernel_only TetraStereo.OneCenter.physicalLift_children
assert_kernel_only TetraStereo.OneCenter.PhysicalFullCutTree.root_eq
assert_kernel_only TetraStereo.OneCenter.PhysicalFullCutTree.nodup_roots
assert_kernel_only TetraStereo.OneCenter.PhysicalFullCutTree.inventory_iff
assert_kernel_only TetraStereo.OneCenter.physicalLiftList_sources
assert_kernel_only TetraStereo.OneCenter.physicalLiftList_sourcePerm
assert_kernel_only TetraStereo.OneCenter.physicalLiftList_realizes
assert_kernel_only TetraStereo.OneCenter.physicalErasure_physicalLiftList
assert_kernel_only TetraStereo.OneCenter.physicalLift_realizes
assert_kernel_only TetraStereo.OneCenter.physicalErasure_physicalLift
assert_kernel_only TetraStereo.OneCenter.physicalTreeRuleMajorOutcome_eq_lift
assert_kernel_only TetraStereo.OneCenter.physicalTreeRuleMajorNotLt_eq_lift
assert_kernel_only TetraStereo.OneCenter.physicalLift_of_admissible
assert_kernel_only TetraStereo.OneCenter.exists_declarativeKey_of_physicalLift
assert_kernel_only TetraStereo.OneCenter.physicalTreeRuleMajorOutcome_admissible_congr
assert_kernel_only TetraStereo.OneCenter.physicalTreeCanonicalOutcome_iff_actualComparison
assert_kernel_only TetraStereo.OneCenter.exists_physicalTreeCanonicalOutcome_iff_actualComparison
