import TetraStereo.OneCenter.LocalizedRealizedTreeCutEquivalence
import TetraStereo.KernelOnly
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput































variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
variable {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}

/-- The slot path of the root position is empty. -/
@[simp] theorem rootPosition_val
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (rootPosition tree).val = [] := rfl

section PhysicalDistance

variable (singleBonded : input.moleculeGraph.SimpleBonded)
variable (acyclic : input.moleculeGraph.Acyclic)

/-! ## An actual simple walk of exactly the address length -/












theorem exists_positionPath_aux
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom) :
    ∀ (bound : Nat) (p : Position tree), p.val.length ≤ bound →
      ∃ w : input.moleculeGraph.underlyingSimpleGraph.Walk oAtom
          (positionAtom singleBonded acyclic p),
        w.IsPath ∧ w.length = p.val.length ∧
          ∀ a ∈ w.support, ∃ q : Position tree,
            positionAtom singleBonded acyclic q = a ∧ q.val.length ≤ p.val.length := by
  intro bound
  induction bound with
  | zero =>
      intro p hp
      have hnil : p.val = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hp)
      have hpRoot : p = rootPosition tree := position_ext (by simpa using hnil)
      subst p
      rw [positionAtom_rootPosition singleBonded acyclic tree oObserved]
      refine ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, ?_, ?_⟩
      · simp
      · intro a ha
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at ha
        rw [ha]
        exact ⟨rootPosition tree,
          by rw [positionAtom_rootPosition singleBonded acyclic tree oObserved], by simp⟩
  | succ n ih =>
      intro p hp
      by_cases hnil : p.val = []
      · have hpRoot : p = rootPosition tree := position_ext (by simpa using hnil)
        subst p
        rw [positionAtom_rootPosition singleBonded acyclic tree oObserved]
        refine ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, ?_, ?_⟩
        · simp
        · intro a ha
          simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at ha
          rw [ha]
          exact ⟨rootPosition tree,
            by rw [positionAtom_rootPosition singleBonded acyclic tree oObserved], by simp⟩
      · have hparentLen : (positionParent p hnil).val.length ≤ n := by
          rw [positionParent_val, List.length_dropLast]
          have hpos : 0 < p.val.length := List.length_pos_iff.mpr hnil
          omega
        obtain ⟨wP, hwPPath, hwPLen, hwPSupp⟩ := ih (positionParent p hnil) hparentLen
        have hparentLt : (positionParent p hnil).val.length < p.val.length := by
          rw [position_eq_parent_append_last p hnil, List.length_append]
          simp
        have hAdj : input.moleculeGraph.underlyingSimpleGraph.Adj
            (positionAtom singleBonded acyclic (positionParent p hnil))
            (positionAtom singleBonded acyclic p) :=
          (positionAtom_adjacent_iff_positionAdjacent singleBonded acyclic enough realizes
            previous previousEq sameRoot valid oObserved pObserved incomingEdge
            (positionParent p hnil) p).mpr
            (Or.inl ⟨p.val.getLast hnil, position_eq_parent_append_last p hnil⟩)
        have hnotmem : positionAtom singleBonded acyclic p ∉ wP.support := by
          intro hmem
          obtain ⟨q, hqAtom, hqLen⟩ := hwPSupp (positionAtom singleBonded acyclic p) hmem
          have hqEq : q = p :=
            positionAtom_injective singleBonded acyclic enough realizes previous previousEq
              sameRoot oObserved pObserved q p hqAtom
          have hlenEq : p.val.length = q.val.length := by
            rw [show p.val = q.val from (congrArg Subtype.val hqEq).symm]
          omega
        refine ⟨wP.concat hAdj,
          SimpleGraph.Walk.IsPath.concat hwPPath hnotmem hAdj, ?_, ?_⟩
        · rw [SimpleGraph.Walk.length_concat, hwPLen,
            position_eq_parent_append_last p hnil, List.length_append]
          simp
        · intro a ha
          simp only [SimpleGraph.Walk.support_concat, List.concat_eq_append, List.mem_append,
            List.mem_singleton] at ha
          rcases ha with ha | ha
          · obtain ⟨q, hqAtom, hqLen⟩ := hwPSupp a ha
            exact ⟨q, hqAtom, le_trans hqLen (Nat.le_of_lt hparentLt)⟩
          · rw [ha]
            exact ⟨p, rfl, le_rfl⟩

/-- **Actual simple physical walk at every realized-tree position.**

Under the actual incoming-cursor hypotheses (single bonds, acyclicity, enough carrier fuel,
realization of the decorated tree, the recorded previous occurrence at the same original root,
the observed incoming atoms and the physical incoming edge), every position `p` of the tree is
the endpoint of an actual simple physical walk from the incoming atom `oAtom`, whose length is
exactly the address length `p.val.length`.

This is an actual walk certificate: neither its existence nor its length grading is supplied. -/
theorem exists_positionPath
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (p : Position tree) :
    ∃ w : input.moleculeGraph.underlyingSimpleGraph.Walk oAtom
        (positionAtom singleBonded acyclic p),
      w.IsPath ∧ w.length = p.val.length := by
  obtain ⟨w, hpath, hlen, _support⟩ :=
    exists_positionPath_aux singleBonded acyclic enough realizes previous previousEq valid
      sameRoot oObserved pObserved incomingEdge p.val.length p le_rfl
  exact ⟨w, hpath, hlen⟩

/-! ## The physical graph distance is the address length -/

/-- **Actual shortest physical distance equals the address length.**

The walk of `exists_positionPath` is a simple path of length `p.val.length`; in the acyclic
underlying simple graph the simple path between two vertices is unique, so it is a geodesic and
the physical graph distance is exactly `p.val.length`.  Nothing about distances is assumed. -/
theorem positionAtom_dist_eq_depth
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (p : Position tree) :
    input.moleculeGraph.underlyingSimpleGraph.dist oAtom
        (positionAtom singleBonded acyclic p) = p.val.length := by
  obtain ⟨w, hwPath, hwLen⟩ :=
    exists_positionPath singleBonded acyclic enough realizes previous previousEq valid
      sameRoot oObserved pObserved incomingEdge p
  have hreach : input.moleculeGraph.underlyingSimpleGraph.Reachable oAtom
      (positionAtom singleBonded acyclic p) := ⟨w⟩
  obtain ⟨q, hqPath, hqDist⟩ := hreach.exists_path_of_dist
  have hwq : w = q := by
    have packageEq :
        (⟨w, hwPath⟩ :
            input.moleculeGraph.underlyingSimpleGraph.Path oAtom
              (positionAtom singleBonded acyclic p)) = ⟨q, hqPath⟩ :=
      input.moleculeGraph.acyclic_path_unique acyclic _ _
    exact congrArg Subtype.val packageEq
  have hdist : w.length = input.moleculeGraph.underlyingSimpleGraph.dist oAtom
      (positionAtom singleBonded acyclic p) := by
    rw [hwq, hqDist]
  rw [← hdist, hwLen]






theorem positionCutEquiv_symm_dist_eq_depth
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (a : AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom) :
    input.moleculeGraph.underlyingSimpleGraph.dist oAtom (a : input.Atom) =
      ((positionCutEquiv singleBonded acyclic enough realizes previous previousEq valid
        sameRoot oObserved pObserved incomingEdge).symm a).val.length := by
  rw [← positionAtom_positionCutEquiv_symm singleBonded acyclic enough realizes previous
    previousEq valid sameRoot oObserved pObserved incomingEdge a]
  exact positionAtom_dist_eq_depth singleBonded acyclic enough realizes previous previousEq
    valid sameRoot oObserved pObserved incomingEdge _

end PhysicalDistance

/-! ## Actual carrier occurrences

The same uniqueness-of-simple-paths argument applies directly to the real path stored in a
carrier occurrence of the bounded localized enumeration.  The stored history of a carrier node
has length one more than its address, and the real walk's support is exactly that history
reversed, so the walk length is the address length. -/

/-- **Physical distance from the original root to a carrier occurrence's current atom.**

For an actual carrier occurrence of the bounded localized enumeration, the physical distance in
the underlying simple graph from the occurrence's original root to the observed current atom is
exactly the occurrence's address length.  The witness is the actual real simple walk recorded by
`carrierOccurrence_realPath`, graded by the exact history length of
`declarativeLocalizedOccurrenceSubtree_history_length`. -/
theorem carrierOccurrence_dist_eq_address_length
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel)
    {current : input.Atom} (observed : occurrence.1.node.current? = some current) :
    input.moleculeGraph.underlyingSimpleGraph.dist occurrence.1.root current =
      occurrence.1.address.length := by
  obtain ⟨current', path, observed', _head, _provenance, pathIsPath, supportReverse,
    _penultimate⟩ := input.carrierOccurrence_realPath singleBonded acyclic occurrence
  have currentEq : current = current' :=
    Option.some.inj (observed.symm.trans observed')
  subst current
  have derived := (input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2
  have rooted : input.DeclarativeLocalizedOccurrenceSubtree occurrence.1.root []
      (fuel + 1) (OfficialCIPNode.root occurrence.1.root) occurrence.1 := derived
  have aligned : (OfficialCIPNode.root occurrence.1.root).history.length =
      (([] : List Nat).length) + 1 := by
    simp [OfficialCIPNode.root]
  have historyLen : occurrence.1.node.history.length = occurrence.1.address.length + 1 :=
    input.declarativeLocalizedOccurrenceSubtree_history_length rooted aligned
  have supportLen : path.support.length = occurrence.1.node.history.length := by
    rw [← supportReverse]
    simp
  have pathLen : path.length = occurrence.1.address.length := by
    have h := SimpleGraph.Walk.length_support path
    omega
  have hreach : input.moleculeGraph.underlyingSimpleGraph.Reachable occurrence.1.root
      current' := ⟨path⟩
  obtain ⟨q, hqPath, hqDist⟩ := hreach.exists_path_of_dist
  have pathEq : path = q := by
    have packageEq :
        (⟨path, pathIsPath⟩ :
            input.moleculeGraph.underlyingSimpleGraph.Path occurrence.1.root current') =
          ⟨q, hqPath⟩ :=
      input.moleculeGraph.acyclic_path_unique acyclic _ _
    exact congrArg Subtype.val packageEq
  have hdist : path.length = input.moleculeGraph.underlyingSimpleGraph.dist
      occurrence.1.root current' := by
    rw [pathEq, hqDist]
  rw [← hdist, pathLen]

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.rootPosition_val
assert_kernel_only TetraStereo.OneCenter.exists_positionPath_aux
assert_kernel_only TetraStereo.OneCenter.exists_positionPath
assert_kernel_only TetraStereo.OneCenter.positionAtom_dist_eq_depth
assert_kernel_only TetraStereo.OneCenter.positionCutEquiv_symm_dist_eq_depth
assert_kernel_only TetraStereo.OneCenter.carrierOccurrence_dist_eq_address_length

end TetraStereo.OneCenter
