import TetraStereo.OneCenter.LocalizedAcyclicBranchCarrier
import TetraStereo.OneCenter.LocalizedAcyclicCarrierInjectivity
import TetraStereo.KernelOnly
import Mathlib.Combinatorics.SimpleGraph.Walks.Traversal

set_option autoImplicit false







































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-- A molecule graph has no positive self-bond, so it has no loop. -/
theorem moleculeGraph_not_adj_self {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (v : V) : ¬ m.Adj v v := by
  intro h
  unfold MoleculeGraph.Adj at h
  rw [m.bond_self] at h
  exact Nat.lt_irrefl 0 h

/-- The graph induced on the atoms other than the chosen centre.  Its acyclicity is the honest
hypothesis behind `CenterDeletedComponentTreeAt`: the ligand arm lives in this graph, while the
full molecule may have arbitrary rings through the deleted centre. -/
def centerDeletedGraph {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (center : V) : SimpleGraph {v : V // v ≠ center} where
  Adj u v := m.Adj u.1 v.1
  symm := fun _ _ h => m.adj_symm.mpr h
  loopless := ⟨fun u h => moleculeGraph_not_adj_self m u.1 h⟩

/-- **The centre-deleted component is a tree at the fixed ligand.**  Every two simple adjacency
chains that start at the same ligand, avoid the centre, and end at the same atom coincide.

This is deliberately stated on lists: the executable official node stores its history as a list of
atoms, and the carrier arguments below consume lists directly.  It is implied by acyclicity of
`centerDeletedGraph` at the ligand's component (two distinct root-avoiding chains would give two
distinct simple paths between the same pair of vertices in that graph); the reverse implication is
not needed and is not claimed.  `G` itself may contain rings through `center`; those do not affect
this predicate. -/
def CenterDeletedComponentTreeAt (input : CertifiedLocalizedCIPInput)
    (center ligand : input.Atom) : Prop :=
  ∀ {target : input.Atom} (left right : List input.Atom),
    left.head? = some ligand →
    right.head? = some ligand →
    left.Nodup → right.Nodup →
    left.IsChain input.moleculeGraph.Adj → right.IsChain input.moleculeGraph.Adj →
    center ∉ left → center ∉ right →
    left.getLast? = some target → right.getLast? = some target →
    left = right

/-- The actual chemical domain of the rooted arm reconstruction: single bonds and a centre-deleted
component that is a tree at the canonical ligand.  No acyclicity of the whole molecule and no
multiple-bond exclusion beyond `SimpleBonded` are assumed; rings through the centre remain. -/
structure CenterDeletedArmDomain (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) : Prop where
  singleBonded : input.moleculeGraph.SimpleBonded
  tree : input.CenterDeletedComponentTreeAt center.1
    (input.canonicalLigandAtom center index)

/-- The head of a cons into a list does not depend on the tail.  This tiny rewrite is used to
identify the reversed history of two candidate root paths. -/
theorem head?_append_cons_eq_append_singleton {α : Type*} (l : List α) (a : α) (r : List α) :
    (l ++ a :: r).head? = (l ++ [a]).head? := by
  cases l <;> rfl










theorem centerArm_history_eq_of_current_eq
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (tree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {left right : OfficialCIPNode input.Atom}
    (leftReal : input.RealPathNode center.1 left)
    (rightReal : input.RealPathNode center.1 right)
    (leftSuffix : [input.canonicalLigandAtom center index, center.1] <:+ left.history)
    (rightSuffix : [input.canonicalLigandAtom center index, center.1] <:+ right.history)
    (sameCurrent : left.current? = right.current?) :
    left.history = right.history := by
  obtain ⟨leftCurrent, leftPath, leftObserved, leftHead, _leftProvenance, leftSimple,
    leftSupport, _leftPenultimate⟩ := leftReal
  obtain ⟨rightCurrent, rightPath, rightObserved, rightHead, _rightProvenance, rightSimple,
    rightSupport, _rightPenultimate⟩ := rightReal
  have sameAtom : leftCurrent = rightCurrent :=
    Option.some.inj (leftObserved.symm.trans (sameCurrent.trans rightObserved))
  subst rightCurrent
  obtain ⟨leftPre, leftPreEq⟩ := leftSuffix
  obtain ⟨rightPre, rightPreEq⟩ := rightSuffix
  -- The two reversed supports, split after the common first step `centre → ligand`.
  have leftRev : leftPath.support = left.history.reverse := by
    have := congrArg List.reverse leftSupport
    simpa using this
  have rightRev : rightPath.support = right.history.reverse := by
    have := congrArg List.reverse rightSupport
    simpa using this
  have leftSupportForm : leftPath.support =
      [center.1, input.canonicalLigandAtom center index] ++ leftPre.reverse := by
    rw [leftRev, ← leftPreEq, List.reverse_append]
    simp
  have rightSupportForm : rightPath.support =
      [center.1, input.canonicalLigandAtom center index] ++ rightPre.reverse := by
    rw [rightRev, ← rightPreEq, List.reverse_append]
    simp
  have leftConsForm : leftPath.support =
      center.1 :: (input.canonicalLigandAtom center index :: leftPre.reverse) := by
    rw [leftSupportForm]
    rfl
  have rightConsForm : rightPath.support =
      center.1 :: (input.canonicalLigandAtom center index :: rightPre.reverse) := by
    rw [rightSupportForm]
    rfl
  have leftTailForm : leftPath.support.tail =
      input.canonicalLigandAtom center index :: leftPre.reverse := by
    rw [leftConsForm]
    rfl
  have rightTailForm : rightPath.support.tail =
      input.canonicalLigandAtom center index :: rightPre.reverse := by
    rw [rightConsForm]
    rfl
  have leftNodup : leftPath.support.Nodup :=
    (SimpleGraph.Walk.isPath_def leftPath).mp leftSimple
  have rightNodup : rightPath.support.Nodup :=
    (SimpleGraph.Walk.isPath_def rightPath).mp rightSimple
  have leftChain : leftPath.support.IsChain input.moleculeGraph.Adj :=
    SimpleGraph.Walk.isChain_adj_support leftPath
  have rightChain : rightPath.support.IsChain input.moleculeGraph.Adj :=
    SimpleGraph.Walk.isChain_adj_support rightPath
  -- The tails are simple rooted chains at the ligand that avoid the centre.
  have leftTailHead : leftPath.support.tail.head? =
      some (input.canonicalLigandAtom center index) := by
    rw [leftTailForm]
    rfl
  have rightTailHead : rightPath.support.tail.head? =
      some (input.canonicalLigandAtom center index) := by
    rw [rightTailForm]
    rfl
  have leftTailNodup : leftPath.support.tail.Nodup := by
    have h := (List.nodup_cons.mp (leftConsForm ▸ leftNodup)).2
    simpa [leftTailForm] using h
  have rightTailNodup : rightPath.support.tail.Nodup := by
    have h := (List.nodup_cons.mp (rightConsForm ▸ rightNodup)).2
    simpa [rightTailForm] using h
  have leftTailChain : leftPath.support.tail.IsChain input.moleculeGraph.Adj :=
    leftChain.tail
  have rightTailChain : rightPath.support.tail.IsChain input.moleculeGraph.Adj :=
    rightChain.tail
  have leftTailCenter : center.1 ∉ leftPath.support.tail := by
    have h := (List.nodup_cons.mp (leftConsForm ▸ leftNodup)).1
    simpa [leftTailForm] using h
  have rightTailCenter : center.1 ∉ rightPath.support.tail := by
    have h := (List.nodup_cons.mp (rightConsForm ▸ rightNodup)).1
    simpa [rightTailForm] using h
  have leftLast : leftPath.support.getLast? = some leftCurrent := by
    calc leftPath.support.getLast? = leftPath.support.reverse.head? := by
          rw [List.head?_reverse]
      _ = left.history.head? := by rw [leftSupport]
      _ = some leftCurrent := leftHead
  have rightLast : rightPath.support.getLast? = some leftCurrent := by
    calc rightPath.support.getLast? = rightPath.support.reverse.head? := by
          rw [List.head?_reverse]
      _ = right.history.head? := by rw [rightSupport]
      _ = some leftCurrent := rightHead
  have leftTailLast : leftPath.support.tail.getLast? = some leftCurrent := by
    have h := leftLast
    rw [leftConsForm, List.getLast?_cons_cons, ← leftTailForm] at h
    exact h
  have rightTailLast : rightPath.support.tail.getLast? = some leftCurrent := by
    have h := rightLast
    rw [rightConsForm, List.getLast?_cons_cons, ← rightTailForm] at h
    exact h
  have tailsEq : leftPath.support.tail = rightPath.support.tail :=
    tree leftPath.support.tail rightPath.support.tail
      leftTailHead rightTailHead leftTailNodup rightTailNodup
      leftTailChain rightTailChain leftTailCenter rightTailCenter
      leftTailLast rightTailLast
  have preEq : leftPre.reverse = rightPre.reverse := by
    have h := tailsEq
    rw [leftTailForm, rightTailForm] at h
    exact (List.cons_inj_right (input.canonicalLigandAtom center index)).mp h
  have supportEq : leftPath.support = rightPath.support := by
    rw [leftSupportForm, rightSupportForm, preEq]
  rw [← leftSupport, ← rightSupport, supportEq]

/-- An arm history of the shape `… ++ [ligand, centre]` is long enough to have a stored parent. -/
theorem exists_parent_of_suffix
    (input : CertifiedLocalizedCIPInput)
    {ligand centerAtom : input.Atom} {node : OfficialCIPNode input.Atom}
    (suffixHist : [ligand, centerAtom] <:+ node.history) :
    ∃ parent, node.parent? = some parent := by
  have hlen : 2 ≤ node.history.length := by
    simpa using suffixHist.length_le
  cases hh : node.history with
  | nil => rw [hh] at hlen; exact absurd hlen (by simp)
  | cons first rest =>
    cases rest with
    | nil => rw [hh] at hlen; exact absurd hlen (by simp)
    | cons second tail => exact ⟨second, by simp [OfficialCIPNode.parent?, hh]⟩

/-- The ring distance stored for the original centre on an arm is zero: the centre is the last
entry of the stored history, hence the first entry of its reverse. -/
theorem arm_duplicateRootDistance_center
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {node : OfficialCIPNode input.Atom}
    (suffixHist : [input.canonicalLigandAtom center index, center.1] <:+ node.history) :
    node.duplicateRootDistance center.1 = 0 := by
  obtain ⟨t, ht⟩ := suffixHist
  have hrev : node.history.reverse =
      center.1 :: (input.canonicalLigandAtom center index :: t.reverse) := by
    rw [← ht, List.reverse_append]
    simp
  unfold OfficialCIPNode.duplicateRootDistance
  rw [hrev]
  simp

/-- **The only ring closure seen from a real arm node is the original centre.**  If `next` is a
neighbour of the observed current atom that already occurred on the stored branch, and it is not
the stored parent, then it must be the centre.

The proof compares the actual root path with the path obtained by jumping from the first
occurrence of `next` directly to `current`: both are simple paths from the centre whose tails avoid
the centre, so the tree hypothesis forces their tails to coincide, which would make `next` the
stored parent. -/
theorem centerArm_visited_eq_center
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (tree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {node : OfficialCIPNode input.Atom} {current next : input.Atom}
    (real : input.RealPathNode center.1 node)
    (suffixHist : [input.canonicalLigandAtom center index, center.1] <:+ node.history)
    (currentObserved : node.current? = some current)
    (visited : next ∈ node.history)
    (adjacent : input.moleculeGraph.Adj current next)
    (notParent : node.parent? ≠ some next) :
    next = center.1 := by
  obtain ⟨current', path, currentObserved', headObserved, _provenance, pathIsPath,
    supportReverse, _penultimateEq⟩ := real
  have currentEq : current = current' :=
    Option.some.inj (currentObserved.symm.trans currentObserved')
  subst current'
  have nodupS : path.support.Nodup := (SimpleGraph.Walk.isPath_def path).mp pathIsPath
  have chainS : path.support.IsChain input.moleculeGraph.Adj :=
    SimpleGraph.Walk.isChain_adj_support path
  have supportEq : path.support = node.history.reverse := by
    have := congrArg List.reverse supportReverse
    simpa using this
  obtain ⟨t, ht⟩ := suffixHist
  have headCenter : path.support.head? = some center.1 := by
    rw [supportEq, List.head?_reverse, ← ht, List.getLast?_append_cons]
    rfl
  have tailHeadLigand : path.support.tail.head? =
      some (input.canonicalLigandAtom center index) := by
    have h2 : path.support =
        [center.1, input.canonicalLigandAtom center index] ++ t.reverse := by
      rw [supportEq, ← ht, List.reverse_append]
      simp
    rw [h2]
    rfl
  have lastSupport : path.support.getLast? = some current := by
    calc path.support.getLast? = path.support.reverse.head? := by rw [List.head?_reverse]
      _ = node.history.head? := by rw [supportReverse]
      _ = some current := headObserved
  have inSupport : next ∈ path.support := by
    have h : next ∈ path.support.reverse := by rw [supportReverse]; exact visited
    simpa using h
  obtain ⟨A, B, splitEq⟩ := List.mem_iff_append.mp inSupport
  by_cases nextCenter : next = center.1
  · exact nextCenter
  · cases A with
    | nil =>
        rw [splitEq] at headCenter
        exact Option.some.inj (by simpa using headCenter)
    | cons a A' =>
        have aEq : a = center.1 := by
          have h := headCenter
          rw [splitEq] at h
          simpa using h
        subst a
        have splitEq' : path.support = center.1 :: (A' ++ next :: B) := by
          simpa using splitEq
        have nodupS' : (center.1 :: (A' ++ next :: B)).Nodup := by
          rwa [← splitEq']
        have nodupParts := List.nodup_append'.mp (splitEq ▸ nodupS)
        have nodupA : (center.1 :: A').Nodup := nodupParts.1
        have disjointAB : List.Disjoint (center.1 :: A') (next :: B) := nodupParts.2.2
        have lastB : (next :: B).getLast? = some current := by
          have h := lastSupport
          rw [splitEq, List.getLast?_append_cons] at h
          exact h
        have currentInB : current ∈ next :: B :=
          List.mem_of_mem_getLast? (by rw [lastB]; simp)
        have nextNeCurrent : next ≠ current := by
          intro h
          exact moleculeGraph_not_adj_self input.moleculeGraph current (h ▸ adjacent)
        have nodupPair : (next :: [current]).Nodup := by
          rw [List.nodup_cons]
          exact ⟨by simpa using nextNeCurrent, by simp⟩
        have disjointPair : List.Disjoint (center.1 :: A') (next :: [current]) := by
          intro x hx hx'
          rcases List.mem_cons.mp hx' with rfl | hx''
          · exact disjointAB hx (by simp)
          · have hxEq : x = current := by simpa using hx''
            rw [hxEq] at hx
            exact disjointAB hx currentInB
        have nodupS₂ : (center.1 :: (A' ++ next :: [current])).Nodup := by
          rw [← List.cons_append]
          exact List.Nodup.append nodupA nodupPair disjointPair
        have tailNodup₁ : (A' ++ next :: B).Nodup := (List.nodup_cons.mp nodupS').2
        have tailNodup₂ : (A' ++ next :: [current]).Nodup :=
          (List.nodup_cons.mp nodupS₂).2
        have tailHead₁ : (A' ++ next :: B).head? =
            some (input.canonicalLigandAtom center index) := by
          have h := tailHeadLigand
          rw [splitEq'] at h
          simpa using h
        have tailHead₂ : (A' ++ next :: [current]).head? =
            some (input.canonicalLigandAtom center index) := by
          have h := tailHead₁
          rw [head?_append_cons_eq_append_singleton (l := A') (a := next) (r := B)] at h
          rwa [head?_append_cons_eq_append_singleton (l := A') (a := next) (r := [current])]
        have tailChain₁ : (A' ++ next :: B).IsChain input.moleculeGraph.Adj := by
          have h := chainS
          rw [splitEq'] at h
          exact h.tail
        have tailChain₂ : (A' ++ next :: [current]).IsChain input.moleculeGraph.Adj := by
          have chainA : (center.1 :: A').IsChain input.moleculeGraph.Adj := by
            have h := chainS
            rw [splitEq] at h
            exact h.left_of_append
          have hb : ∀ x ∈ (center.1 :: A').getLast?,
              ∀ y ∈ (next :: B).head?, input.moleculeGraph.Adj x y :=
            (List.isChain_append.mp (splitEq ▸ chainS)).2.2
          have boundary : ∀ x ∈ (center.1 :: A').getLast?,
              ∀ y ∈ (next :: [current]).head?, input.moleculeGraph.Adj x y := by
            intro x hx y hy
            exact hb x hx y (by simpa using hy)
          have pair : (next :: [current]).IsChain input.moleculeGraph.Adj :=
            List.IsChain.cons_cons (input.moleculeGraph.adj_symm.mpr adjacent)
              (List.IsChain.singleton current)
          exact (List.IsChain.append chainA pair boundary).tail
        have centerNotTail₁ : center.1 ∉ A' ++ next :: B :=
          (List.nodup_cons.mp nodupS').1
        have centerNotTail₂ : center.1 ∉ A' ++ next :: [current] :=
          (List.nodup_cons.mp nodupS₂).1
        have tailLast₁ : (A' ++ next :: B).getLast? = some current := by
          rw [List.getLast?_append_of_ne_nil _ (by simp : (next :: B) ≠ [])]
          exact lastB
        have tailLast₂ : (A' ++ next :: [current]).getLast? = some current := by
          rw [List.getLast?_append_of_ne_nil _ (by simp : (next :: [current]) ≠ [])]
          rfl
        have tailsEq : A' ++ next :: B = A' ++ next :: [current] :=
          tree (A' ++ next :: B) (A' ++ next :: [current])
            tailHead₁ tailHead₂ tailNodup₁ tailNodup₂ tailChain₁ tailChain₂
            centerNotTail₁ centerNotTail₂ tailLast₁ tailLast₂
        have consEq : next :: B = next :: [current] :=
          List.append_inj_right tailsEq rfl
        have bEq : B = [current] :=
          (List.cons_inj_right next).mp consEq
        have supportForm : path.support = (center.1 :: A') ++ [next, current] := by
          rw [splitEq', bEq]
          rfl
        have historyForm : node.history =
            current :: next :: (A'.reverse ++ [center.1]) := by
          have hrev : node.history = path.support.reverse := supportReverse.symm
          rw [hrev, supportForm, List.reverse_append]
          simp
        have parentObserved : node.parent? = some next := by
          simp [OfficialCIPNode.parent?, historyForm]
        exact absurd parentObserved notParent

/-- Every executable child of a non-duplicate real node carries a current atom. -/
theorem exists_current_of_mem_executableOfficialCIPChildren
    (input : CertifiedLocalizedCIPInput)
    {node child : OfficialCIPNode input.Atom}
    (provenance : node.provenance = OfficialCIPNodeProvenance.realAtom)
    (childMem : child ∈ input.executableOfficialCIPChildren node) :
    ∃ next, child.current? = some next := by
  have nonduplicate : node.isDuplicateLeaf = false :=
    input.isDuplicateLeaf_eq_false_of_provenance_real node provenance
  unfold executableOfficialCIPChildren at childMem
  rw [if_neg (by simpa using nonduplicate), List.mem_map] at childMem
  obtain ⟨copy, _copyPresent, copyEq⟩ := childMem
  exact ⟨copy.1, by rw [← copyEq]; rfl⟩

/-- Every executable child of a non-duplicate node extends the history by exactly one atom. -/
theorem history_length_of_mem_executableOfficialCIPChildren
    (input : CertifiedLocalizedCIPInput)
    {node child : OfficialCIPNode input.Atom}
    (provenance : node.provenance = OfficialCIPNodeProvenance.realAtom)
    (childMem : child ∈ input.executableOfficialCIPChildren node) :
    child.history.length = node.history.length + 1 := by
  have nonduplicate : node.isDuplicateLeaf = false :=
    input.isDuplicateLeaf_eq_false_of_provenance_real node provenance
  unfold executableOfficialCIPChildren at childMem
  rw [if_neg (by simpa using nonduplicate), List.mem_map] at childMem
  obtain ⟨copy, _copyPresent, copyEq⟩ := childMem
  obtain ⟨next, copyIndex⟩ := copy
  change node.extend next copyIndex = child at copyEq
  rw [← copyEq, OfficialCIPNode.extend_history_length]

/-- **Every executable child of a real arm node is real-fresh or the centre closure.**  The child
is either a real atom that has not yet occurred on the branch, or the zero-distance ring duplicate
of the original centre.  In particular the simple-bond hypothesis rules out every multiple-bond
duplicate copy on the arm. -/
theorem centerArmRealNode_child_classification
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (tree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {node child : OfficialCIPNode input.Atom} {current next : input.Atom}
    (real : input.RealPathNode center.1 node)
    (suffixHist : [input.canonicalLigandAtom center index, center.1] <:+ node.history)
    (currentObserved : node.current? = some current)
    (childObserved : child.current? = some next)
    (childMem : child ∈ input.executableOfficialCIPChildren node) :
    (child.provenance = OfficialCIPNodeProvenance.realAtom ∧ next ∉ node.history) ∨
      (next = center.1 ∧
        child.provenance = OfficialCIPNodeProvenance.ringDuplicate 0) := by
  have provenance : node.provenance = OfficialCIPNodeProvenance.realAtom :=
    input.realPathNode_provenance real
  have nonduplicate : node.isDuplicateLeaf = false :=
    input.isDuplicateLeaf_eq_false_of_provenance_real node provenance
  unfold executableOfficialCIPChildren at childMem
  rw [if_neg (by simpa using nonduplicate), List.mem_map] at childMem
  obtain ⟨copy, copyPresent, copyEq⟩ := childMem
  obtain ⟨next', copyIndex⟩ := copy
  change node.extend next' copyIndex = child at copyEq
  have nextEq : next' = next := by
    have h : (node.extend next' copyIndex).current? = some next := by
      rw [copyEq]
      exact childObserved
    simpa using h
  rw [nextEq] at copyPresent copyEq
  obtain ⟨adjacent, bound⟩ :=
    input.mem_executableOfficialChildCopies_adjacent_bound node current next copyIndex
      currentObserved copyPresent
  have bondOne : input.moleculeGraph.bond current next = 1 :=
    singleBonded current next adjacent
  have copyZero : copyIndex = 0 := by
    have h := bound
    rw [bondOne] at h
    exact Nat.lt_one_iff.mp h
  rw [copyZero] at copyPresent copyEq
  have childProvenance : child.provenance = node.childProvenance next 0 := by
    rw [← copyEq, OfficialCIPNode.extend_provenance]
  by_cases visited : next ∈ node.history
  · right
    have centerEq : next = center.1 :=
      input.centerArm_visited_eq_center center index tree real suffixHist currentObserved
        visited adjacent (by
          obtain ⟨parent, parentObserved⟩ := input.exists_parent_of_suffix suffixHist
          have nextNeParent : next ≠ parent :=
            input.not_parent_of_zero_mem_executableOfficialChildCopies node next parent
              copyPresent parentObserved
          intro h
          have parentEq : parent = next := Option.some.inj (parentObserved.symm.trans h)
          exact nextNeParent parentEq.symm)
    refine ⟨centerEq, ?_⟩
    rw [childProvenance, OfficialCIPNode.childProvenance_ring_duplicate node next visited,
      centerEq, input.arm_duplicateRootDistance_center center index suffixHist]
  · left
    refine ⟨?_, visited⟩
    rw [childProvenance, OfficialCIPNode.childProvenance_real node next visited]








theorem centerArmRealNode_centerAttachment_iff
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (tree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {node : OfficialCIPNode input.Atom} {current : input.Atom}
    (real : input.RealPathNode center.1 node)
    (suffixHist : [input.canonicalLigandAtom center index, center.1] <:+ node.history)
    (currentObserved : node.current? = some current)
    (centerNotParent : node.parent? ≠ some center.1) :
    (∃ child ∈ input.executableOfficialCIPChildren node,
        child.rule1bRootDistance = 0) ↔
      input.moleculeGraph.Adj current center.1 := by
  constructor
  · rintro ⟨child, childMem, distanceZero⟩
    obtain ⟨next, childObserved⟩ :=
      input.exists_current_of_mem_executableOfficialCIPChildren
        (input.realPathNode_provenance real) childMem
    rcases input.centerArmRealNode_child_classification center index tree singleBonded real
      suffixHist currentObserved childObserved childMem with
      ⟨realProvenance, fresh⟩ | ⟨nextCenter, _ringProvenance⟩
    · exfalso
      have hdepth : child.rule1bRootDistance = child.depth := by
        simp [OfficialCIPNode.rule1bRootDistance, realProvenance]
      have lenEq : child.history.length = node.history.length + 1 :=
        input.history_length_of_mem_executableOfficialCIPChildren
          (input.realPathNode_provenance real) childMem
      have depthEq : child.depth = node.history.length := by
        unfold OfficialCIPNode.depth
        rw [lenEq]
        simp
      have hlen : 2 ≤ node.history.length := by
        have := suffixHist.length_le
        simpa using this
      omega
    · rw [← nextCenter]
      exact input.adj_of_mem_executableOfficialCIPChildren node child current next
        currentObserved childObserved childMem
  · intro adjacent
    have provenance : node.provenance = OfficialCIPNodeProvenance.realAtom :=
      input.realPathNode_provenance real
    have nonduplicate : node.isDuplicateLeaf = false :=
      input.isDuplicateLeaf_eq_false_of_provenance_real node provenance
    refine ⟨node.extend center.1 0, ?_, ?_⟩
    · exact input.mem_executableOfficialCIPChildren_of_adjacent node current center.1 0
        nonduplicate currentObserved adjacent adjacent (Or.inr centerNotParent)
    · have visited : center.1 ∈ node.history := by
        obtain ⟨t, ht⟩ := suffixHist
        rw [← ht]
        simp
      have prov : node.childProvenance center.1 0 =
          OfficialCIPNodeProvenance.ringDuplicate 0 := by
        rw [OfficialCIPNode.childProvenance_ring_duplicate node center.1 visited,
          input.arm_duplicateRootDistance_center center index suffixHist]
      simp [OfficialCIPNode.rule1bRootDistance, prov]

/-- The stored parent of a node occurs on its own branch history. -/
theorem mem_history_of_parent?_eq_some
    (input : CertifiedLocalizedCIPInput) {node : OfficialCIPNode input.Atom}
    {parent : input.Atom} (parentObserved : node.parent? = some parent) :
    parent ∈ node.history := by
  cases hh : node.history with
  | nil => simp [OfficialCIPNode.parent?, hh] at parentObserved
  | cons first rest =>
    cases rest with
    | nil => simp [OfficialCIPNode.parent?, hh] at parentObserved
    | cons second tail =>
      have h : second = parent := by
        simpa [OfficialCIPNode.parent?, hh] using parentObserved
      rw [← h]
      simp


















theorem centerArmRealNode_realChild_iff
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {node : OfficialCIPNode input.Atom} {current : input.Atom}
    (real : input.RealPathNode center.1 node)
    (currentObserved : node.current? = some current)
    (child : OfficialCIPNode input.Atom) (next : input.Atom) :
    (child ∈ input.executableOfficialCIPChildren node ∧
        child.provenance = OfficialCIPNodeProvenance.realAtom ∧
          child.current? = some next) ↔
      (next ∉ node.history ∧ input.moleculeGraph.Adj current next ∧
        child = node.extend next 0) := by
  constructor
  · rintro ⟨childMem, realProvenance, childObserved⟩
    have provenance : node.provenance = OfficialCIPNodeProvenance.realAtom :=
      input.realPathNode_provenance real
    have nonduplicate : node.isDuplicateLeaf = false :=
      input.isDuplicateLeaf_eq_false_of_provenance_real node provenance
    unfold executableOfficialCIPChildren at childMem
    rw [if_neg (by simpa using nonduplicate), List.mem_map] at childMem
    obtain ⟨copy, copyPresent, copyEq⟩ := childMem
    obtain ⟨next', copyIndex⟩ := copy
    change node.extend next' copyIndex = child at copyEq
    have nextEq : next' = next := by
      have h : (node.extend next' copyIndex).current? = some next := by
        rw [copyEq]
        exact childObserved
      simpa using h
    rw [nextEq] at copyPresent copyEq
    obtain ⟨adjacent, bound⟩ :=
      input.mem_executableOfficialChildCopies_adjacent_bound node current next copyIndex
        currentObserved copyPresent
    have bondOne : input.moleculeGraph.bond current next = 1 :=
      singleBonded current next adjacent
    have copyZero : copyIndex = 0 := by
      have h := bound
      rw [bondOne] at h
      exact Nat.lt_one_iff.mp h
    rw [copyZero] at copyPresent copyEq
    refine ⟨?_, adjacent, copyEq.symm⟩
    intro visited
    have provEq : node.childProvenance next 0 = OfficialCIPNodeProvenance.realAtom := by
      have h : (node.extend next 0).provenance = OfficialCIPNodeProvenance.realAtom := by
        rw [copyEq]
        exact realProvenance
      simpa using h
    rw [OfficialCIPNode.childProvenance_ring_duplicate node next visited] at provEq
    exact absurd provEq (by simp)
  · rintro ⟨fresh, adjacent, rfl⟩
    have provenance : node.provenance = OfficialCIPNodeProvenance.realAtom :=
      input.realPathNode_provenance real
    have nonduplicate : node.isDuplicateLeaf = false :=
      input.isDuplicateLeaf_eq_false_of_provenance_real node provenance
    have parentNe : node.parent? ≠ some next := by
      intro h
      exact fresh (input.mem_history_of_parent?_eq_some h)
    have bound : 0 < input.moleculeGraph.bond current next := by
      rw [singleBonded current next adjacent]
      exact Nat.zero_lt_one
    refine ⟨?_, ?_, rfl⟩
    · exact input.mem_executableOfficialCIPChildren_of_adjacent node current next 0
        nonduplicate currentObserved adjacent bound (Or.inr parentNe)
    · rw [OfficialCIPNode.extend_provenance,
        OfficialCIPNode.childProvenance_real node next fresh]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.moleculeGraph_not_adj_self
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedGraph
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.CenterDeletedComponentTreeAt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.CenterDeletedArmDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.head?_append_cons_eq_append_singleton
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerArm_history_eq_of_current_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_parent_of_suffix
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.arm_duplicateRootDistance_center
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerArm_visited_eq_center
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_current_of_mem_executableOfficialCIPChildren
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.history_length_of_mem_executableOfficialCIPChildren
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerArmRealNode_child_classification
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerArmRealNode_centerAttachment_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_history_of_parent?_eq_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerArmRealNode_realChild_iff
