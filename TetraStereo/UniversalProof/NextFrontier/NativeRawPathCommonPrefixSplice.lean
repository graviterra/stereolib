import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalTreeSimplePathUniqueness
import TetraStereo.OneCenter.CanonicalComparisonFrame

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRawPathCommonPrefixSplice
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeGeneratedRealPaths
open TetraStereo.UniversalProof.NativeChronologicalTreeSimplePathUniqueness

/-- Truncating after a specified physical vertex preserves actual supported path semantics. -/
theorem supported_prefix_to_vertex {mol : RawMolecule} {root finish vertex : Nat}
    (before after : List Nat)
    (path : RawSupportedPath mol root finish (before ++ vertex :: after)) :
    RawSupportedPath mol root vertex (before ++ [vertex]) := by
  have whole : before ++ vertex :: after = (before ++ [vertex]) ++ after := by
    simp only [List.append_assoc, List.singleton_append]
  have nd : ((before ++ [vertex]) ++ after).Nodup := whole ▸ path.1
  have chain : RawBondedPath mol ((before ++ [vertex]) ++ after) := whole ▸ path.2.1
  refine ⟨(List.nodup_append.mp nd).1, chain.left_of_append, ?_, ?_, ?_⟩
  · have head := path.2.2.1
    cases before with
    | nil => simpa using head
    | cons a rest => simpa using head
  · simp
  · intro atom member
    apply path.2.2.2.2 atom
    rw [whole]
    exact List.mem_append_left after member

/-- Any shared physical endpoint has identical root prefixes, derived from raw tree facts. -/
theorem shared_vertex_prefixes_equal {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root leftEnd rightEnd vertex : Nat}
    (leftBefore leftAfter rightBefore rightAfter : List Nat)
    (leftPath : RawSupportedPath mol root leftEnd (leftBefore ++ vertex :: leftAfter))
    (rightPath : RawSupportedPath mol root rightEnd (rightBefore ++ vertex :: rightAfter)) :
    leftBefore ++ [vertex] = rightBefore ++ [vertex] := by
  exact chronological_uniqueRawSimplePaths tree root vertex _ _
    (supported_prefix_to_vertex leftBefore leftAfter leftPath)
    (supported_prefix_to_vertex rightBefore rightAfter rightPath)

/-- A prefix ending at a selected vertex retains the first vertex of its nonempty suffix. -/
theorem head_prefix_through_vertex (before after : List Nat) (vertex : Nat) :
    (before ++ [vertex]).head? = (before ++ vertex :: after).head? := by
  cases before <;> rfl

/-- Paths cannot reconverge after different first vertices beyond any shared prefix. -/
theorem divergent_tails_disjoint {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root leftEnd rightEnd : Nat}
    (common left right : List Nat)
    (leftPath : RawSupportedPath mol root leftEnd (common ++ left))
    (rightPath : RawSupportedPath mol root rightEnd (common ++ right))
    (differentHeads : left.head? ≠ right.head?) :
    ∀ vertex ∈ left, vertex ∉ right := by
  intro vertex leftMember rightMember
  obtain ⟨leftBefore, leftAfter, leftEq⟩ := List.mem_iff_append.mp leftMember
  obtain ⟨rightBefore, rightAfter, rightEq⟩ := List.mem_iff_append.mp rightMember
  have leftActual : RawSupportedPath mol root leftEnd
      ((common ++ leftBefore) ++ vertex :: leftAfter) := by
    simpa only [leftEq, List.append_assoc] using leftPath
  have rightActual : RawSupportedPath mol root rightEnd
      ((common ++ rightBefore) ++ vertex :: rightAfter) := by
    simpa only [rightEq, List.append_assoc] using rightPath
  have prefixes := shared_vertex_prefixes_equal tree
    (common ++ leftBefore) leftAfter (common ++ rightBefore) rightAfter leftActual rightActual
  have suffixes : leftBefore ++ [vertex] = rightBefore ++ [vertex] := by
    apply (List.append_right_inj common).mp
    simpa only [List.append_assoc] using prefixes
  apply differentHeads
  rw [leftEq, rightEq]
  exact (head_prefix_through_vertex leftBefore leftAfter vertex).symm.trans
    ((congrArg List.head? suffixes).trans (head_prefix_through_vertex rightBefore rightAfter vertex))

/-- Every vertex common to two divergent physical routes already occurs in their shared prefix. -/
theorem shared_vertices_in_prefix {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root leftEnd rightEnd : Nat}
    (common left right : List Nat)
    (leftPath : RawSupportedPath mol root leftEnd (common ++ left))
    (rightPath : RawSupportedPath mol root rightEnd (common ++ right))
    (differentHeads : left.head? ≠ right.head?) :
    ∀ vertex ∈ common ++ left, vertex ∈ common ++ right → vertex ∈ common := by
  intro vertex leftMember rightMember
  rcases List.mem_append.mp leftMember with inCommon | inLeft
  · exact inCommon
  rcases List.mem_append.mp rightMember with inCommon | inRight
  · exact inCommon
  · exact False.elim (divergent_tails_disjoint tree common left right leftPath rightPath
      differentHeads vertex inLeft inRight)

/-- The two accepted metric namespaces compute the same prefix length, by recursion. -/
theorem commonPrefix_namespace_agrees (left right : List Nat) :
    NativeOriginFrame.commonPrefixLength left right =
      CanonicalComparisonFrame.commonPrefixLength left right := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons a left ih =>
      cases right with
      | nil => rfl
      | cons b right =>
          simp only [NativeOriginFrame.commonPrefixLength,
            CanonicalComparisonFrame.commonPrefixLength, ih]

/-- The production frame and accepted path-frame use precisely the same arithmetic metric. -/
theorem pathDistance_namespace_agrees (left right : List Nat) :
    NativeOriginFrame.pathDistance left right = CanonicalComparisonFrame.pathDistance left right := by
  simp only [NativeOriginFrame.pathDistance, CanonicalComparisonFrame.pathDistance,
    commonPrefix_namespace_agrees]

/-- A common list followed by distinct first vertices is exactly the computed common prefix. -/
theorem commonPrefix_of_divergent_heads (common left right : List Nat)
    (differentHeads : left.head? ≠ right.head?) :
    CanonicalComparisonFrame.commonPrefixLength (common ++ left) (common ++ right) = common.length := by
  induction common with
  | nil =>
      cases left with
      | nil => cases right <;> rfl
      | cons a left =>
          cases right with
          | nil => rfl
          | cons b right =>
              have different : a ≠ b := by
                intro same
                apply differentHeads
                simp only [List.head?_cons, same]
              simp [CanonicalComparisonFrame.commonPrefixLength, different]
  | cons a common ih =>
      simp only [List.cons_append, CanonicalComparisonFrame.commonPrefixLength,
        ite_true, List.length_cons]
      omega

/-- An actual junction splice is simple and supported; disjointness is proved from raw tree facts. -/
theorem divergent_junction_splice_supported {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root center target junction : Nat}
    (before left right : List Nat)
    (leftPath : RawSupportedPath mol root center ((before ++ [junction]) ++ left))
    (rightPath : RawSupportedPath mol root target ((before ++ [junction]) ++ right))
    (differentHeads : left.head? ≠ right.head?) :
    RawSupportedPath mol center target ((junction :: left).reverse ++ right) := by
  have leftWhole : RawSupportedPath mol root center (before ++ junction :: left) := by
    simpa only [List.append_assoc, List.singleton_append] using leftPath
  have rightWhole : RawSupportedPath mol root target (before ++ junction :: right) := by
    simpa only [List.append_assoc, List.singleton_append] using rightPath
  have leftNd : (junction :: left).Nodup := (List.nodup_append.mp leftWhole.1).2.1
  have rightNd : (junction :: right).Nodup := (List.nodup_append.mp rightWhole.1).2.1
  have leftChain : RawBondedPath mol (junction :: left) := leftWhole.2.1.right_of_append
  have rightChain : RawBondedPath mol (junction :: right) := rightWhole.2.1.right_of_append
  have disjoint := divergent_tails_disjoint tree (before ++ [junction]) left right
    leftPath rightPath differentHeads
  have leftLast : (junction :: left).getLast? = some center := by
    have last := leftWhole.2.2.2.1
    rw [List.getLast?_append_of_ne_nil before (by simp)] at last
    exact last
  have rightLast : (junction :: right).getLast? = some target := by
    have last := rightWhole.2.2.2.1
    rw [List.getLast?_append_of_ne_nil before (by simp)] at last
    exact last
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.reverse_cons, List.append_assoc, List.singleton_append, List.nodup_append]
    refine ⟨List.nodup_reverse.mpr (List.nodup_cons.mp leftNd).2, rightNd, ?_⟩
    intro a ha b hb equal
    subst b
    have inLeft : a ∈ left := List.mem_reverse.mp ha
    rcases List.mem_cons.mp hb with atJunction | inRight
    · subst a
      exact (List.nodup_cons.mp leftNd).1 inLeft
    · exact disjoint a inLeft inRight
  · have reversed : RawBondedPath mol (junction :: left).reverse := by
      apply List.isChain_reverse.mpr
      exact leftChain.imp_of_mem_imp (fun a b _ _ edge => by
        rwa [mol.bondOrder_symm b a])
    have rightTail : RawBondedPath mol right := (List.isChain_cons.mp rightChain).2
    apply reversed.append rightTail
    intro a ha b hb
    have atJunction : a = junction := by
      symm
      simpa using ha
    subst a
    exact (List.isChain_cons.mp rightChain).1 b hb
  · rw [List.head?_append_of_ne_nil _ (by simp), List.head?_reverse, leftLast]
  · cases right with
    | nil => simpa using rightLast
    | cons b rest =>
        rw [List.getLast?_append_of_ne_nil _ (by simp)]
        simpa only [List.getLast?_cons_cons] using rightLast
  · intro atom member
    rcases List.mem_append.mp member with inLeft | inRight
    · exact leftWhole.2.2.2.2 atom (List.mem_append_right before (List.mem_reverse.mp inLeft))
    · exact rightWhole.2.2.2.2 atom (List.mem_append_right before (List.mem_cons_of_mem junction inRight))

/-- The constructed junction path has exactly the production common-prefix distance in edges. -/
theorem divergent_junction_splice_edge_count (before left right : List Nat) (junction : Nat)
    (differentHeads : left.head? ≠ right.head?) :
    ((junction :: left).reverse ++ right).length - 1 =
      CanonicalComparisonFrame.pathDistance ((before ++ [junction]) ++ left)
        ((before ++ [junction]) ++ right) := by
  unfold CanonicalComparisonFrame.pathDistance
  rw [commonPrefix_of_divergent_heads (before ++ [junction]) left right differentHeads]
  simp only [List.length_append, List.length_reverse, List.length_cons]
  omega

/-- Recursive maximal shared-prefix decomposition, including identical lists and empty tails. -/
theorem maximal_prefix_decomposition (p q : List Nat) :
    ∃ common left right, p = common ++ left ∧ q = common ++ right ∧
      ((left = [] ∧ right = []) ∨ left.head? ≠ right.head?) := by
  induction p generalizing q with
  | nil =>
      cases q with
      | nil => exact ⟨[], [], [], rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
      | cons b q => exact ⟨[], [], b :: q, rfl, rfl, Or.inr (by simp)⟩
  | cons a p ih =>
      cases q with
      | nil => exact ⟨[], a :: p, [], rfl, rfl, Or.inr (by simp)⟩
      | cons b q =>
          by_cases same : a = b
          · subst b
            obtain ⟨common, left, right, pEq, qEq, boundary⟩ := ih q
            refine ⟨a :: common, left, right, ?_, ?_, boundary⟩
            · simpa only [List.cons_append] using congrArg (List.cons a) pEq
            · simpa only [List.cons_append] using congrArg (List.cons a) qEq
          · exact ⟨[], a :: p, b :: q, rfl, rfl, Or.inr (by simpa using same)⟩

/-- General physical splice for every pair of actual supported root paths, with exact metric.
    Maximal decomposition and tail disjointness are derived, never supplied as caller fields. -/
theorem supported_pair_splice_exists {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root center target : Nat} (p q : List Nat)
    (pPath : RawSupportedPath mol root center p)
    (qPath : RawSupportedPath mol root target q) :
    ∃ splice, RawSupportedPath mol center target splice ∧
      splice.length - 1 = CanonicalComparisonFrame.pathDistance p q := by
  obtain ⟨common, left, right, pEq, qEq, boundary⟩ := maximal_prefix_decomposition p q
  rcases boundary with ⟨leftEmpty, rightEmpty⟩ | differentHeads
  · subst left
    subst right
    simp only [List.append_nil] at pEq qEq
    have samePaths : p = q := pEq.trans qEq.symm
    have sameEnds : center = target := by
      apply Option.some.inj
      have qLast : p.getLast? = some target := by
        rw [samePaths]
        exact qPath.2.2.2.1
      exact pPath.2.2.2.1.symm.trans qLast
    subst target
    refine ⟨[center], ?_, ?_⟩
    · refine ⟨by simp, by simp [RawBondedPath], rfl, rfl, ?_⟩
      intro atom member
      simp only [List.mem_singleton] at member
      subst atom
      exact pPath.2.2.2.2 center (List.mem_of_getLast? pPath.2.2.2.1)
    · rw [← samePaths, CanonicalComparisonFrame.pathDistance_self]
      rfl
  · have commonNonempty : common ≠ [] := by
      intro empty
      have pHead := pPath.2.2.1
      have qHead := qPath.2.2.1
      rw [pEq, empty, List.nil_append] at pHead
      rw [qEq, empty, List.nil_append] at qHead
      exact differentHeads (pHead.trans qHead.symm)
    rcases List.eq_nil_or_concat common with empty | ⟨before, junction, commonEq⟩
    · exact False.elim (commonNonempty empty)
    · have commonAppend : common = before ++ [junction] := by
        simpa only [List.concat_eq_append] using commonEq
      have leftActual : RawSupportedPath mol root center ((before ++ [junction]) ++ left) := by
        rw [← commonAppend, ← pEq]
        exact pPath
      have rightActual : RawSupportedPath mol root target ((before ++ [junction]) ++ right) := by
        rw [← commonAppend, ← qEq]
        exact qPath
      refine ⟨(junction :: left).reverse ++ right,
        divergent_junction_splice_supported tree before left right leftActual rightActual differentHeads, ?_⟩
      rw [pEq, qEq, commonAppend]
      exact divergent_junction_splice_edge_count before left right junction differentHeads

end TetraStereo.UniversalProof.NativeRawPathCommonPrefixSplice
