import TetraStereo.OneCenter.LocalizedMonocyclicDoubleBondPerception
import TetraStereo.OneCenter.LocalizedOccurrenceCarrierCoverage
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Find
import TetraStereo.KernelOnly

set_option autoImplicit false


























namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## The stored history of a simple occurrence path is a bonded chain -/

/-- The stored current atom is the head of the stored history for every simple occurrence
path.  This is an invariant of the actual `extend` construction, not an extra hypothesis. -/
theorem simpleOccurrencePath_history_head
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (path : SimpleOccurrencePath input root node address) :
    node.history.head? = node.current? := by
  induction path with
  | root => rfl
  | @step node address current next path currentObserved adjacent notParent fresh ih =>
      simp [OfficialCIPNode.extend_history, OfficialCIPNode.extend_current?]

/-- Every simple occurrence path stores a bonded history: consecutive stored atoms are joined by
a positive bond of the actual molecule graph.  The direction along the list is current first,
then its stored parent, and so on back to the root. -/
theorem simpleOccurrencePath_history_isChain
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (path : SimpleOccurrencePath input root node address) :
    node.history.IsChain (fun a b => input.moleculeGraph.Adj a b) := by
  induction path with
  | root => exact List.isChain_singleton root
  | @step node address current next path currentObserved adjacent notParent fresh ih =>
      rw [OfficialCIPNode.extend_history]
      have headEq := input.simpleOccurrencePath_history_head path
      rw [currentObserved] at headEq
      cases h : node.history with
      | nil => exact List.isChain_singleton next
      | cons stored tail =>
          rw [h] at ih
          rw [h] at headEq
          rw [List.isChain_cons_cons]
          refine ⟨?_, ih⟩
          have hstored : stored = current := by simpa using headEq
          rw [hstored]
          exact (input.moleculeGraph.adj_symm).mp adjacent

/-- Every atom stored on a simple occurrence path is reachable in the positive-bond component
of the occurrence root. -/
theorem simpleOccurrencePath_history_reachable_root
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (path : SimpleOccurrencePath input root node address) :
    ∀ atom, atom ∈ node.history →
      input.moleculeGraph.underlyingSimpleGraph.Reachable root atom := by
  induction path with
  | root =>
      intro atom hatom
      simp only [OfficialCIPNode.root, List.mem_singleton] at hatom
      subst atom
      exact SimpleGraph.Reachable.refl root
  | @step node address current next path currentObserved adjacent notParent fresh ih =>
      rw [OfficialCIPNode.extend_history]
      intro atom hatom
      rw [List.mem_cons] at hatom
      rcases hatom with rfl | hatom
      · have headEq := input.simpleOccurrencePath_history_head path
        rw [currentObserved] at headEq
        have hcur := ih current (List.mem_of_head? headEq)
        exact SimpleGraph.Reachable.trans hcur (SimpleGraph.Adj.reachable adjacent)
      · exact ih atom hatom

/-! ## A bonded simple list with a closing edge contains an induced cycle -/

/-- **Generic finite-graph bridge.**  A duplicate-free list whose consecutive entries are
positively bonded and which has a nonconsecutive bonded pair contains a chordless simple cycle
vertex set: it satisfies `DeclarativeLocalizedSimpleCycleVertexSet` and is contained in the list's
vertex set.

The proof chooses a closing pair of minimal index gap `g` and keeps the segment between its
endpoints.  A chord inside that segment would be a closing pair with strictly smaller gap, so the
segment has exactly the two expected retained neighbours at every vertex.  No chordlessness
hypothesis is used. -/
theorem exists_inducedSimpleCycle_of_bonded_list
    (input : CertifiedLocalizedCIPInput) (vertices : List input.Atom)
    (nodup : vertices.Nodup)
    (bonded : vertices.IsChain (fun a b => input.moleculeGraph.Adj a b))
    (closing : ∃ i j : Fin vertices.length,
      i.val + 2 ≤ j.val ∧
        input.moleculeGraph.Adj (vertices.get i) (vertices.get j)) :
    ∃ cycle : Finset input.Atom,
      cycle ⊆ vertices.toFinset ∧
        input.DeclarativeLocalizedSimpleCycleVertexSet cycle := by
  classical
  obtain ⟨i, j, hij, hadj⟩ := closing
  -- The shortest gap between the endpoints of a nonconsecutive bonded pair.
  have hExists : ∃ d : Nat, ∃ i j : Fin vertices.length,
      i.val + 2 ≤ j.val ∧
        input.moleculeGraph.Adj (vertices.get i) (vertices.get j) ∧
        j.val - i.val = d :=
    ⟨j.val - i.val, i, j, hij, hadj, rfl⟩
  set g : Nat := Nat.find hExists with hgDef
  have hSpec : ∃ i j : Fin vertices.length,
      i.val + 2 ≤ j.val ∧
        input.moleculeGraph.Adj (vertices.get i) (vertices.get j) ∧
        j.val - i.val = g := by
    rw [hgDef]
    exact Nat.find_spec hExists
  obtain ⟨i0, j0, hij0, hadj0, hgap0⟩ := hSpec
  have hig2 : 2 ≤ g := by omega
  have hj0eq : j0.val = i0.val + g := by omega
  -- The minimal closing segment, from position `i0` through `i0 + g`.
  set seg : List input.Atom := (vertices.drop i0.val).take (g + 1) with hsegDef
  have hgBound : g + 1 ≤ vertices.length - i0.val := by
    have := j0.isLt
    omega
  have hsegLen : seg.length = g + 1 := by
    rw [hsegDef, List.length_take, List.length_drop, Nat.min_eq_left hgBound]
  have hsegNodup : seg.Nodup :=
    (List.take_sublist (g + 1) (vertices.drop i0.val)).nodup
      ((List.drop_sublist i0.val vertices).nodup nodup)
  have hsegChain : seg.IsChain (fun a b => input.moleculeGraph.Adj a b) := by
    rw [hsegDef]
    exact (bonded.drop i0.val).take (g + 1)
  have hsegGet : ∀ (k : Nat) (hk : k < seg.length),
      seg[k]'hk = vertices[i0.val + k]'(by
        have := j0.isLt
        omega) := by
    intro k hk
    simp only [hsegDef, List.getElem_take, List.getElem_drop]
  -- Minimality of `g` expressed on segment positions.
  have hMinimal : ∀ (a b : Nat) (hab : a + 2 ≤ b) (hb : b < seg.length),
      input.moleculeGraph.Adj (seg[a]'(by omega)) (seg[b]'hb) → b - a = g := by
    intro a b hab hb hAdj
    have hbLe : b ≤ g := by
      have := hsegLen
      omega
    have haLt : a < seg.length := by omega
    have haV : i0.val + a < vertices.length := by
      have := j0.isLt
      omega
    have hbV : i0.val + b < vertices.length := by
      have := j0.isLt
      omega
    have hadjV : input.moleculeGraph.Adj
        (vertices.get ⟨i0.val + a, haV⟩)
        (vertices.get ⟨i0.val + b, hbV⟩) := by
      have h1 : seg[a]'haLt = vertices.get ⟨i0.val + a, haV⟩ := hsegGet a haLt
      have h2 : seg[b]'hb = vertices.get ⟨i0.val + b, hbV⟩ := hsegGet b hb
      rw [← h1, ← h2]
      exact hAdj
    have hWitness : ∃ p q : Fin vertices.length,
        p.val + 2 ≤ q.val ∧
          input.moleculeGraph.Adj (vertices.get p) (vertices.get q) ∧
          q.val - p.val = (b - a) := by
      refine ⟨⟨i0.val + a, haV⟩, ⟨i0.val + b, hbV⟩, ?_, hadjV, ?_⟩
      · show i0.val + a + 2 ≤ i0.val + b
        omega
      · show (i0.val + b) - (i0.val + a) = b - a
        omega
    have hle := Nat.find_min' hExists hWitness
    have hgle : g ≤ b - a := by
      simpa [hgDef] using hle
    omega
  -- The closing edge, as a segment edge from position zero to position `g`.
  have hzeroLt : 0 < seg.length := by omega
  have hgLt : g < seg.length := by omega
  have hseg0 : seg[0]'hzeroLt = vertices.get i0 := by
    have h := hsegGet 0 hzeroLt
    simpa using h
  have hsegg : seg[g]'hgLt = vertices.get j0 := by
    have h := hsegGet g hgLt
    simp only [h, ← hj0eq]
    rfl
  have hcloseSeg : input.moleculeGraph.Adj seg[0] seg[g] := by
    rw [hseg0, hsegg]
    exact hadj0
  have hchainSucc : ∀ (k : Nat) (hk : k + 1 < seg.length),
      input.moleculeGraph.Adj (seg[k]'(by omega)) (seg[k + 1]'hk) :=
    fun k hk => hsegChain.getElem k hk
  have hchainPred : ∀ (k : Nat) (hk : k + 1 < seg.length),
      input.moleculeGraph.Adj (seg[k + 1]'hk) (seg[k]'(by omega)) :=
    fun k hk => (input.moleculeGraph.adj_symm).mp (hsegChain.getElem k hk)
  -- Every segment vertex has exactly its two cyclic retained neighbours.
  have hdegree : ∀ atom, atom ∈ seg.toFinset →
      (input.localizedCycleNeighbors seg.toFinset atom).card = 2 := by
    intro atom hatom
    have hmem : atom ∈ seg := List.mem_toFinset.mp hatom
    obtain ⟨j, hjlt, hjEq⟩ := List.mem_iff_getElem.mp hmem
    have hjle : j ≤ g := by
      have := hsegLen
      omega
    set li : Nat := if j = 0 then g else j - 1 with hli
    set ri : Nat := if j = g then 0 else j + 1 with hri
    have hliLt : li < seg.length := by
      rw [hli]
      split <;> omega
    have hriLt : ri < seg.length := by
      rw [hri]
      split <;> omega
    have hliNe : li ≠ ri := by
      rw [hli, hri]
      split_ifs with h1 h2 <;> omega
    have hliAdj : input.moleculeGraph.Adj seg[j] seg[li] := by
      simp only [hli]
      by_cases hj0 : j = 0
      · simpa [hj0] using hcloseSeg
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
        have h := hchainPred (j - 1) (by omega)
        simpa [hj0, Nat.sub_add_cancel hjpos] using h
    have hriAdj : input.moleculeGraph.Adj seg[j] seg[ri] := by
      simp only [hri]
      by_cases hjg : j = g
      · simpa [hjg] using (input.moleculeGraph.adj_symm).mp hcloseSeg
      · have h := hchainSucc j (by omega)
        simpa [hjg] using h
    have hIndex : ∀ (k : Nat) (hk : k < seg.length),
        input.moleculeGraph.Adj (seg[j]'hjlt) (seg[k]'hk) → k = li ∨ k = ri := by
      intro k hk hAdj
      have hkj : k ≠ j := by
        intro h
        subst k
        simp [MoleculeGraph.Adj, input.moleculeGraph.bond_self] at hAdj
      rcases lt_or_gt_of_ne hkj with hklj | hjlk
      · by_cases hfar : k + 2 ≤ j
        · have hgap : j - k = g :=
            hMinimal k j hfar (by omega) ((input.moleculeGraph.adj_symm).mp hAdj)
          have hjEq : j = g := by omega
          have hkEq : k = 0 := by omega
          right
          rw [hri]
          simp [hjEq]
          exact hkEq
        · have hjk : j = k + 1 := by omega
          left
          rw [hli]
          have hj0 : j ≠ 0 := by omega
          simp [hj0]
          omega
      · by_cases hfar : j + 2 ≤ k
        · have hgap : k - j = g := hMinimal j k hfar hk hAdj
          have hjEq : j = 0 := by omega
          have hkEq : k = g := by omega
          left
          rw [hli]
          simp [hjEq]
          exact hkEq
        · have hjk : k = j + 1 := by omega
          right
          rw [hri]
          by_cases hjg : j = g
          · simp [hjg]
            omega
          · simp [hjg]
            omega
    have hneigh : input.localizedCycleNeighbors seg.toFinset atom =
        {seg[li], seg[ri]} := by
      ext y
      rw [mem_localizedCycleNeighbors_iff]
      constructor
      · rintro ⟨hyS, hyAdj⟩
        have hyseg : y ∈ seg := List.mem_toFinset.mp hyS
        obtain ⟨k, hklt, hkEq⟩ := List.mem_iff_getElem.mp hyseg
        have hAdj : input.moleculeGraph.Adj seg[j] seg[k] := by
          simpa [← hjEq, ← hkEq] using hyAdj
        rcases hIndex k hklt hAdj with hk | hk
        · exact Finset.mem_insert.mpr (Or.inl (by simp only [← hkEq, hk]))
        · exact Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton.mpr (by simp only [← hkEq, hk])))
      · intro hy
        rw [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with hy | hy
        · rw [hy]
          refine ⟨List.mem_toFinset.mpr (List.mem_iff_getElem.mpr ⟨li, hliLt, rfl⟩), ?_⟩
          simpa [← hjEq] using hliAdj
        · rw [hy]
          refine ⟨List.mem_toFinset.mpr (List.mem_iff_getElem.mpr ⟨ri, hriLt, rfl⟩), ?_⟩
          simpa [← hjEq] using hriAdj
    rw [hneigh]
    refine Finset.card_pair ?_
    intro h
    exact hliNe ((hsegNodup.getElem_inj_iff (i := li) (hi := hliLt)
      (j := ri) (hj := hriLt)).mp h)
  -- Consecutive retained vertices are reachable inside the induced graph.
  have hsuccReach : ∀ (k : Nat) (hk : k + 1 < seg.length),
      (input.localizedInducedCycleGraph seg.toFinset).Reachable
        (seg[k]'(by omega)) (seg[k + 1]'hk) := by
    intro k hk
    refine SimpleGraph.Adj.reachable ?_
    rw [localizedInducedCycleGraph_adj]
    exact ⟨List.mem_toFinset.mpr (List.mem_iff_getElem.mpr ⟨k, by omega, rfl⟩),
      List.mem_toFinset.mpr (List.mem_iff_getElem.mpr ⟨k + 1, hk, rfl⟩),
      hsegChain.getElem k hk⟩
  have hprefixReach : ∀ (t : Nat) (ht : t ≤ g),
      (input.localizedInducedCycleGraph seg.toFinset).Reachable
        (seg[0]'hzeroLt) (seg[t]'(by omega)) := by
    intro t
    induction t with
    | zero =>
        intro _
        exact SimpleGraph.Reachable.refl (seg[0]'hzeroLt)
    | succ t ih =>
        intro ht
        have hstep := hsuccReach t (by omega)
        exact SimpleGraph.Reachable.trans (ih (by omega)) hstep
  have hconnected : ∀ left, left ∈ seg.toFinset →
      ∀ right, right ∈ seg.toFinset →
        (input.localizedInducedCycleGraph seg.toFinset).Reachable left right := by
    intro left hleft right hright
    obtain ⟨a, _haLt, haEq⟩ :=
      List.mem_iff_getElem.mp (List.mem_toFinset.mp hleft)
    obtain ⟨b, _hbLt, hbEq⟩ :=
      List.mem_iff_getElem.mp (List.mem_toFinset.mp hright)
    have haLe : a ≤ g := by
      have := hsegLen
      omega
    have hbLe : b ≤ g := by
      have := hsegLen
      omega
    have h0a := hprefixReach a haLe
    have h0b := hprefixReach b hbLe
    rw [← haEq, ← hbEq]
    exact SimpleGraph.Reachable.trans h0a.symm h0b
  have hcard : 3 ≤ seg.toFinset.card := by
    rw [List.toFinset_card_of_nodup hsegNodup, hsegLen]
    omega
  have hsubset : seg.toFinset ⊆ vertices.toFinset := by
    intro x hx
    have hxseg : x ∈ seg := List.mem_toFinset.mp hx
    rw [hsegDef] at hxseg
    have hxdrop : x ∈ vertices.drop i0.val :=
      (List.take_sublist (g + 1) (vertices.drop i0.val)).subset hxseg
    exact List.mem_toFinset.mpr ((List.drop_sublist i0.val vertices).subset hxdrop)
  refine ⟨seg.toFinset, hsubset, ?_⟩
  exact ⟨hcard, hdegree, hconnected⟩

/-! ## The actual official-history corollary -/

/-- **Actual-history ring closure yields an induced cycle in the history.**  If `node` is the
endpoint of a `SimpleOccurrencePath` (hence a duplicate-free bonded history), its current atom is
bonded to an atom `next` already stored in that history, and `next` is not the stored parent that
the executable child enumeration removes, then the closed walk contains a chordless simple cycle
whose vertex set is entirely contained in the stored history.

This is the `LegitimateOccurrence.ring` situation: `next` is the zero-copy ring duplicate of a
history atom.  The official-child-filter parent exclusion is exactly what rules out the degenerate
two-vertex case. -/
theorem exists_history_inducedSimpleCycle_of_ringStep
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    {current next : input.Atom}
    (path : SimpleOccurrencePath input root node address)
    (currentObserved : node.current? = some current)
    (adjacent : input.moleculeGraph.Adj current next)
    (notParent : node.parent? ≠ some next)
    (visited : next ∈ node.history) :
    ∃ cycle : Finset input.Atom,
      cycle ⊆ node.history.toFinset ∧
        input.DeclarativeLocalizedSimpleCycleVertexSet cycle := by
  classical
  have nodup := input.simpleOccurrencePath_history_nodup path
  have bonded := input.simpleOccurrencePath_history_isChain path
  have headEq := input.simpleOccurrencePath_history_head path
  rw [currentObserved] at headEq
  obtain ⟨k, hklt, hkEq⟩ := List.mem_iff_getElem.mp visited
  -- Membership at an index, in `getElem?` form, so that case analysis on indices never has to
  -- abstract a dependent proof argument.
  have hkOpt : node.history[k]? = some next :=
    List.getElem?_eq_some_iff.mpr ⟨hklt, hkEq⟩
  -- The stored history is headed by the current atom.
  obtain ⟨tail, htail⟩ := List.head?_eq_some_iff.mp headEq
  -- `next` is not the head, by looplessness of bond adjacency.
  have hk0 : k ≠ 0 := by
    intro hkzero
    rw [hkzero] at hkOpt
    have hsome : (current :: tail)[0]? = some next := by
      simpa [htail] using hkOpt
    have hnext : current = next := by
      have hsome' : some current = some next := by simpa using hsome
      exact Option.some.inj hsome'
    rw [← hnext] at adjacent
    simp [MoleculeGraph.Adj, input.moleculeGraph.bond_self] at adjacent
  -- `next` is not the stored parent, by the official child filter.
  have hk1 : k ≠ 1 := by
    intro hkone
    apply notParent
    rw [hkone] at hkOpt
    have hsome : (current :: tail)[1]? = some next := by
      simpa [htail] using hkOpt
    cases tail with
    | nil => simp at hsome
    | cons second rest =>
        have hsecond : second = next := by
          have hsome' : some second = some next := by simpa using hsome
          exact Option.some.inj hsome'
        simp [OfficialCIPNode.parent?, htail, hsecond]
  have hk2 : 2 ≤ k := by omega
  -- The stored history prefix ending at the closing atom.
  set histPrefix : List input.Atom := node.history.take (k + 1) with hprefixDef
  have hprefixLen : histPrefix.length = k + 1 := by
    rw [hprefixDef, List.length_take, Nat.min_eq_left (by omega)]
  have hprefixNodup : histPrefix.Nodup :=
    (List.take_sublist (k + 1) node.history).nodup nodup
  have hprefixChain : histPrefix.IsChain (fun a b => input.moleculeGraph.Adj a b) := by
    rw [hprefixDef]
    exact bonded.take (k + 1)
  have hprefixGet : ∀ (m : Nat) (hm : m < histPrefix.length),
      histPrefix[m]'hm = node.history[m]'(by omega) := by
    intro m hm
    simp only [hprefixDef, List.getElem_take]
  have hkPrefix : k < histPrefix.length := by omega
  have hzeroPrefix : 0 < histPrefix.length := by omega
  have hprefix0 : histPrefix[0]'hzeroPrefix = current := by
    have h := hprefixGet 0 hzeroPrefix
    simpa [htail] using h
  have hprefixK : histPrefix[k]'hkPrefix = next := by
    rw [hprefixGet k hkPrefix]
    exact hkEq
  -- Close the prefix at its two endpoints.
  have hclosure : ∃ i j : Fin histPrefix.length,
      i.val + 2 ≤ j.val ∧
        input.moleculeGraph.Adj (histPrefix.get i) (histPrefix.get j) := by
    refine ⟨⟨0, hzeroPrefix⟩, ⟨k, hkPrefix⟩, ?_, ?_⟩
    · show 0 + 2 ≤ k
      omega
    · have hAdjPrefix : input.moleculeGraph.Adj
          (histPrefix[0]'hzeroPrefix) (histPrefix[k]'hkPrefix) := by
        rw [hprefix0, hprefixK]
        exact adjacent
      simpa using hAdjPrefix
  obtain ⟨cycle, hcycleSub, hcycle⟩ :=
    input.exists_inducedSimpleCycle_of_bonded_list histPrefix hprefixNodup hprefixChain hclosure
  refine ⟨cycle, ?_, hcycle⟩
  intro x hx
  have hxprefix : x ∈ histPrefix := List.mem_toFinset.mp (hcycleSub hx)
  rw [hprefixDef] at hxprefix
  exact List.mem_toFinset.mpr ((List.take_sublist (k + 1) node.history).subset hxprefix)

/-- **Component-contained form.**  The induced cycle supplied by
`exists_history_inducedSimpleCycle_of_ringStep` also lies in the positive-bond component of the
occurrence root, matching the component side condition of the monocyclic carrier. -/
theorem exists_component_history_inducedSimpleCycle_of_ringStep
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    {current next : input.Atom}
    (path : SimpleOccurrencePath input root node address)
    (currentObserved : node.current? = some current)
    (adjacent : input.moleculeGraph.Adj current next)
    (notParent : node.parent? ≠ some next)
    (visited : next ∈ node.history) :
    ∃ cycle : Finset input.Atom,
      cycle ⊆ node.history.toFinset ∧
        cycle ⊆ input.localizedCovalentComponentAtoms root ∧
          input.DeclarativeLocalizedSimpleCycleVertexSet cycle := by
  obtain ⟨cycle, hhistory, hcycle⟩ :=
    input.exists_history_inducedSimpleCycle_of_ringStep path currentObserved adjacent
      notParent visited
  refine ⟨cycle, hhistory, ?_, hcycle⟩
  intro x hx
  rw [input.mem_localizedCovalentComponentAtoms_iff]
  exact input.simpleOccurrencePath_history_reachable_root path x
    (List.mem_toFinset.mp (hhistory hx))

/-- **Ring-duplicate child form.**  The same cycle is contained in the history of the zero-copy
ring-duplicate child `node.extend next 0`, whose parent is the actual occurrence node. -/
theorem ringDuplicateChild_exists_history_inducedSimpleCycle
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    {current next : input.Atom}
    (path : SimpleOccurrencePath input root node address)
    (currentObserved : node.current? = some current)
    (adjacent : input.moleculeGraph.Adj current next)
    (notParent : node.parent? ≠ some next)
    (visited : next ∈ node.history) :
    ∃ cycle : Finset input.Atom,
      cycle ⊆ (node.extend next 0).history.toFinset ∧
        input.DeclarativeLocalizedSimpleCycleVertexSet cycle := by
  obtain ⟨cycle, hhistory, hcycle⟩ :=
    input.exists_history_inducedSimpleCycle_of_ringStep path currentObserved adjacent
      notParent visited
  refine ⟨cycle, ?_, hcycle⟩
  intro x hx
  rw [OfficialCIPNode.extend_history, List.mem_toFinset]
  exact List.mem_cons_of_mem next (List.mem_toFinset.mp (hhistory hx))

/-- A fresh atom outside the stored history is automatically outside any cycle contained in the
history vertex set.  This is the exclusion used for the fresh real child of the parent
occurrence. -/
theorem not_mem_of_subset_history_toFinset
    {input : CertifiedLocalizedCIPInput} {node : OfficialCIPNode input.Atom}
    {cycle : Finset input.Atom} {fresh : input.Atom}
    (hsubset : cycle ⊆ node.history.toFinset)
    (hfresh : fresh ∉ node.history) :
    fresh ∉ cycle := by
  intro hmem
  exact hfresh (List.mem_toFinset.mp (hsubset hmem))

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleOccurrencePath_history_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleOccurrencePath_history_isChain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleOccurrencePath_history_reachable_root
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_inducedSimpleCycle_of_bonded_list
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_history_inducedSimpleCycle_of_ringStep
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_component_history_inducedSimpleCycle_of_ringStep
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ringDuplicateChild_exists_history_inducedSimpleCycle
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.not_mem_of_subset_history_toFinset
