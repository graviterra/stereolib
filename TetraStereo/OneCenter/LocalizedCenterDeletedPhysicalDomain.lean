import TetraStereo.OneCenter.LocalizedCenterDeletedTreeRingReconstruction
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false































namespace TetraStereo.OneCenter

/-! ## Generic chain-to-walk bridges -/

/-- If `a` is the head of `l`, then `a` occurs in `l`. -/
theorem mem_of_head?_eq_some {X : Type*} {l : List X} {a : X} (h : l.head? = some a) :
    a ∈ l :=
  List.mem_of_mem_head? (by rw [h]; simp)

/-- If `a` is the last element of `l`, then `a` occurs in `l`. -/
theorem mem_of_getLast?_eq_some {X : Type*} {l : List X} {a : X}
    (h : l.getLast? = some a) : a ∈ l :=
  List.mem_of_mem_getLast? (by rw [h]; simp)

/-- A chain with observed head and last vertices is the support of an actual walk between them.
The walk is built directly from the chain, so its support is the chain itself (as a list), with no
up-to-reversal or up-to-path-equivalence slack. -/
theorem exists_walk_of_isChain_head?_getLast? {X : Type*} {G : SimpleGraph X}
    {l : List X} {a b : X} (hhead : l.head? = some a) (hlast : l.getLast? = some b)
    (hchain : l.IsChain G.Adj) : ∃ w : G.Walk a b, w.support = l := by
  induction l generalizing a with
  | nil => simp at hhead
  | cons x rest ih =>
      cases rest with
      | nil =>
          simp only [List.head?_cons, Option.some.injEq] at hhead
          subst a
          rw [List.getLast?_singleton, Option.some.injEq] at hlast
          subst b
          exact ⟨SimpleGraph.Walk.nil, rfl⟩
      | cons y rest =>
          rw [List.isChain_cons_cons] at hchain
          obtain ⟨hxy, hchain'⟩ := hchain
          simp only [List.head?_cons, Option.some.injEq] at hhead
          subst a
          rw [List.getLast?_cons_cons] at hlast
          obtain ⟨w, hw⟩ := ih rfl hlast hchain'
          exact ⟨SimpleGraph.Walk.cons hxy w, by
            rw [SimpleGraph.Walk.support_cons, hw]⟩

/-- Every vertex on a walk that starts in a connected component lies in that component. -/
theorem mem_component_supp_of_mem_support {X : Type*} {G : SimpleGraph X}
    (C : G.ConnectedComponent) :
    ∀ {u v : X} (p : G.Walk u v), u ∈ C.supp → ∀ x ∈ p.support, x ∈ C.supp
  | _, _, .nil, hu, x, hx => by
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
      subst hx
      exact hu
  | _, _, .cons h p, hu, x, hx => by
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hu
      · exact mem_component_supp_of_mem_support C p
          (C.mem_supp_of_adj_mem_supp hu h) x hx

/-- Mapping the support of a walk induced on a vertex set back along the subtype embedding recovers
the original support, as a list. -/
theorem support_induce_map {X : Type*} {G : SimpleGraph X} {s : Set X} :
    ∀ {u v : X} (p : G.Walk u v) (hs : ∀ x ∈ p.support, x ∈ s),
      (p.induce s hs).support.map Subtype.val = p.support
  | _, _, .nil, _ => rfl
  | u, _, .cons h p, hs => by
      simp only [SimpleGraph.Walk.induce_cons, SimpleGraph.Walk.support_cons, List.map_cons]
      exact congrArg (List.cons u) (support_induce_map p _)

/-! ## Lifting atom chains through the centre-deleted subtype -/

/-- A chain in the ambient graph whose elements all satisfy `p` lifts to a chain of subtypes,
provided the subtype relation is implied by the ambient relation. -/
theorem isChain_attachWith_of_isChain {X : Type*} {p : X → Prop}
    {R : {x // p x} → {x // p x} → Prop} {S : X → X → Prop}
    (hRS : ∀ x hx y hy, S x y → R ⟨x, hx⟩ ⟨y, hy⟩) :
    ∀ {l : List X} (H : ∀ x ∈ l, p x), l.IsChain S → (l.attachWith p H).IsChain R
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | x :: y :: rest, H, hchain => by
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hxy, hchain'⟩ := hchain
      rw [List.attachWith_cons, List.attachWith_cons, List.isChain_cons_cons]
      exact ⟨hRS x _ y _ hxy,
        isChain_attachWith_of_isChain hRS
          (fun z hz => H z (List.mem_cons_of_mem x hz)) hchain'⟩

/-- A nodup list stays nodup after attaching subtype proofs. -/
theorem nodup_attachWith {X : Type*} {p : X → Prop} {l : List X} (H : ∀ x ∈ l, p x)
    (h : l.Nodup) : (l.attachWith p H).Nodup :=
  List.Nodup.of_map Subtype.val (by
    rw [List.attachWith_map_subtype_val]
    exact h)

/-- The head of the subtype-attached list is the head atom with its membership proof. -/
theorem head?_attachWith_of_head? {X : Type*} {p : X → Prop} {l : List X}
    (H : ∀ x ∈ l, p x) {a : X} (h : l.head? = some a) :
    (l.attachWith p H).head? = some ⟨a, H a (mem_of_head?_eq_some h)⟩ := by
  cases l with
  | nil => simp at h
  | cons x xs =>
      simp only [List.head?_cons, Option.some.injEq] at h
      subst a
      rw [List.attachWith_cons]
      exact congrArg some (Subtype.ext rfl)

/-- The last element of the subtype-attached list is the last atom with its membership proof. -/
theorem getLast?_attachWith_of_getLast? {X : Type*} {p : X → Prop} :
    ∀ {l : List X} (H : ∀ x ∈ l, p x) {a : X} (h : l.getLast? = some a),
      (l.attachWith p H).getLast? = some ⟨a, H a (mem_of_getLast?_eq_some h)⟩
  | [], _, _, h => by simp at h
  | [x], H, a, h => by
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst a
      rw [List.attachWith_cons]
      exact congrArg some (Subtype.ext rfl)
  | x :: y :: rest, H, a, h => by
      rw [List.getLast?_cons_cons] at h
      rw [List.attachWith_cons, List.attachWith_cons, List.getLast?_cons_cons]
      exact (getLast?_attachWith_of_getLast?
        (fun z hz => H z (List.mem_cons_of_mem x hz)) h).trans
        (congrArg some (Subtype.ext rfl))

/-! ## Unique chains inside an acyclic connected component -/

/-- **Unique simple chains in an acyclic connected component.**  Two simple chains with the same
head `u` and the same last vertex `v`, whose heads lie in an acyclic connected component `C` of
`G`, are equal.  No hypothesis is made about the rest of `G`. -/
theorem eq_of_isChain_of_component_acyclic {X : Type*} {G : SimpleGraph X}
    (C : G.ConnectedComponent) (hacyc : C.toSimpleGraph.IsAcyclic)
    {u v : X} (hu : u ∈ C.supp)
    {l₁ l₂ : List X}
    (h₁ : l₁.head? = some u) (h₂ : l₂.head? = some u)
    (e₁ : l₁.getLast? = some v) (e₂ : l₂.getLast? = some v)
    (n₁ : l₁.Nodup) (n₂ : l₂.Nodup)
    (c₁ : l₁.IsChain G.Adj) (c₂ : l₂.IsChain G.Adj) :
    l₁ = l₂ := by
  obtain ⟨w₁, hw₁⟩ := exists_walk_of_isChain_head?_getLast? h₁ e₁ c₁
  obtain ⟨w₂, hw₂⟩ := exists_walk_of_isChain_head?_getLast? h₂ e₂ c₂
  have hs₁ : ∀ x ∈ w₁.support, x ∈ C.supp :=
    fun x hx => mem_component_supp_of_mem_support C w₁ hu x hx
  have hs₂ : ∀ x ∈ w₂.support, x ∈ C.supp :=
    fun x hx => mem_component_supp_of_mem_support C w₂ hu x hx
  let A : C := ⟨u, hu⟩
  let B : C := ⟨v, hs₁ v w₁.end_mem_support⟩
  let P₁ : C.toSimpleGraph.Walk A B :=
    (w₁.induce C.supp hs₁).copy (Subtype.ext rfl) (Subtype.ext rfl)
  let P₂ : C.toSimpleGraph.Walk A B :=
    (w₂.induce C.supp hs₂).copy (Subtype.ext rfl) (Subtype.ext rfl)
  have hp₁ : P₁.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    show ((w₁.induce C.supp hs₁).copy _ _).support.Nodup
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_induce]
    exact nodup_attachWith hs₁ (hw₁.symm ▸ n₁)
  have hp₂ : P₂.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    show ((w₂.induce C.supp hs₂).copy _ _).support.Nodup
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_induce]
    exact nodup_attachWith hs₂ (hw₂.symm ▸ n₂)
  have hP : P₁ = P₂ :=
    congrArg Subtype.val
      (SimpleGraph.IsAcyclic.path_unique hacyc ⟨P₁, hp₁⟩ ⟨P₂, hp₂⟩)
  have key₁ : P₁.support.map Subtype.val = l₁ := by
    show ((w₁.induce C.supp hs₁).copy _ _).support.map Subtype.val = l₁
    rw [SimpleGraph.Walk.support_copy, support_induce_map, hw₁]
  have key₂ : P₂.support.map Subtype.val = l₂ := by
    show ((w₂.induce C.supp hs₂).copy _ _).support.map Subtype.val = l₂
    rw [SimpleGraph.Walk.support_copy, support_induce_map, hw₂]
  calc l₁ = P₁.support.map Subtype.val := key₁.symm
    _ = P₂.support.map Subtype.val := by rw [hP]
    _ = l₂ := key₂



namespace CertifiedLocalizedCIPInput





theorem centerDeletedComponentTreeAt_of_component_acyclic
    (input : CertifiedLocalizedCIPInput) (center ligand : input.Atom)
    (hligand : ligand ≠ center)
    (hacyclic : ((centerDeletedGraph input.moleculeGraph center).connectedComponentMk
      ⟨ligand, hligand⟩).toSimpleGraph.IsAcyclic) :
    input.CenterDeletedComponentTreeAt center ligand := by
  intro target left right hleftHead hrightHead hleftNodup hrightNodup
    hleftChain hrightChain hleftCenter hrightCenter hleftLast hrightLast
  let D := centerDeletedGraph input.moleculeGraph center
  let C := D.connectedComponentMk ⟨ligand, hligand⟩
  have hmemLeft : ∀ x ∈ left, x ≠ center :=
    fun x hx hxc => hleftCenter (hxc ▸ hx)
  have hmemRight : ∀ x ∈ right, x ≠ center :=
    fun x hx hxc => hrightCenter (hxc ▸ hx)
  let left' : List {v : input.Atom // v ≠ center} :=
    left.attachWith (fun x => x ≠ center) hmemLeft
  let right' : List {v : input.Atom // v ≠ center} :=
    right.attachWith (fun x => x ≠ center) hmemRight
  have htarget : target ≠ center :=
    hmemLeft target (mem_of_getLast?_eq_some hleftLast)
  have hleftHead' : left'.head? = some ⟨ligand, hligand⟩ := by
    show (left.attachWith (fun x => x ≠ center) hmemLeft).head? =
      some ⟨ligand, hligand⟩
    rw [head?_attachWith_of_head? hmemLeft hleftHead]
  have hrightHead' : right'.head? = some ⟨ligand, hligand⟩ := by
    show (right.attachWith (fun x => x ≠ center) hmemRight).head? =
      some ⟨ligand, hligand⟩
    rw [head?_attachWith_of_head? hmemRight hrightHead]
  have hleftLast' : left'.getLast? = some ⟨target, htarget⟩ := by
    show (left.attachWith (fun x => x ≠ center) hmemLeft).getLast? =
      some ⟨target, htarget⟩
    rw [getLast?_attachWith_of_getLast? hmemLeft hleftLast]
  have hrightLast' : right'.getLast? = some ⟨target, htarget⟩ := by
    show (right.attachWith (fun x => x ≠ center) hmemRight).getLast? =
      some ⟨target, htarget⟩
    rw [getLast?_attachWith_of_getLast? hmemRight hrightLast]
  have hleftChain' : left'.IsChain D.Adj := by
    show (left.attachWith (fun x => x ≠ center) hmemLeft).IsChain D.Adj
    exact isChain_attachWith_of_isChain (fun _ _ _ _ h => h) hmemLeft hleftChain
  have hrightChain' : right'.IsChain D.Adj := by
    show (right.attachWith (fun x => x ≠ center) hmemRight).IsChain D.Adj
    exact isChain_attachWith_of_isChain (fun _ _ _ _ h => h) hmemRight hrightChain
  have hleftNodup' : left'.Nodup := nodup_attachWith hmemLeft hleftNodup
  have hrightNodup' : right'.Nodup := nodup_attachWith hmemRight hrightNodup
  have hu : (⟨ligand, hligand⟩ : {v : input.Atom // v ≠ center}) ∈ C.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have heq : left' = right' :=
    eq_of_isChain_of_component_acyclic C hacyclic hu hleftHead' hrightHead'
      hleftLast' hrightLast' hleftNodup' hrightNodup' hleftChain' hrightChain'
  calc left = left'.map Subtype.val := (List.attachWith_map_subtype_val hmemLeft).symm
    _ = right'.map Subtype.val := by rw [heq]
    _ = right := List.attachWith_map_subtype_val hmemRight

/-- The same adapter from acyclicity of the entire centre-deleted graph.  This is strictly stronger
than needed, but convenient for concrete finite molecules whose deletion leaves a forest. -/
theorem centerDeletedComponentTreeAt_of_centerDeleted_acyclic
    (input : CertifiedLocalizedCIPInput) (center ligand : input.Atom)
    (hligand : ligand ≠ center)
    (acyclic : (centerDeletedGraph input.moleculeGraph center).IsAcyclic) :
    input.CenterDeletedComponentTreeAt center ligand :=
  input.centerDeletedComponentTreeAt_of_component_acyclic center ligand hligand
    (SimpleGraph.IsAcyclic.isTree_connectedComponent acyclic _).IsAcyclic

end CertifiedLocalizedCIPInput










/-- **The starting vertex of a cycle has two distinct neighbours.**  Its first and last steps leave
`u` along two vertices that cannot coincide, because a cycle visits every position between `1` and
its length exactly once. -/
theorem exists_two_adj_of_isCycle {X : Type*} {G : SimpleGraph X} {u : X} {c : G.Walk u u}
    (hc : c.IsCycle) : ∃ a b : X, a ≠ b ∧ G.Adj u a ∧ G.Adj u b := by
  have hlen : 3 ≤ c.length := SimpleGraph.Walk.IsCycle.three_le_length hc
  refine ⟨c.getVert 1, c.getVert (c.length - 1), ?_, ?_, ?_⟩
  · intro heq
    have h1 : 1 ∈ {i : Nat | 1 ≤ i ∧ i ≤ c.length} := by
      simp only [Set.mem_setOf_eq]; omega
    have h2 : c.length - 1 ∈ {i : Nat | 1 ≤ i ∧ i ≤ c.length} := by
      simp only [Set.mem_setOf_eq]; omega
    have : 1 = c.length - 1 := SimpleGraph.Walk.IsCycle.getVert_injOn hc h1 h2 heq
    omega
  · have hstep := SimpleGraph.Walk.adj_getVert_succ c (i := 0) (by omega)
    simpa using hstep
  · have hstep := SimpleGraph.Walk.adj_getVert_succ c (i := c.length - 1) (by omega)
    have hlast : c.getVert (c.length - 1 + 1) = u := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ c.length)]
      exact SimpleGraph.Walk.getVert_length c
    have hbw : G.Adj (c.getVert (c.length - 1)) u := by
      simpa [hlast] using hstep
    exact G.symm hbw

/-- A graph in which no vertex has two distinct neighbours is acyclic. -/
theorem isAcyclic_of_adj_unique {X : Type*} {G : SimpleGraph X}
    (h : ∀ u v w, G.Adj u v → G.Adj u w → v = w) : G.IsAcyclic := by
  intro u c hc
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_adj_of_isCycle hc
  exact hab (h u a b ha hb)

namespace CenterDeletedRingFixture

/-! ### The molecule

Atom `0` is a carbon bonded to four oxygens `1`, `2`, `3`, `4`; the oxygen pairs `1-2` and `3-4`
are additionally bonded.  The full graph therefore contains the two genuine triangles `0-1-2-0`
and `0-3-4-0`, atom `0` is automatically detected as a four-neighbour centre, and deleting atom
`0` leaves exactly the two disjoint edges `1-2` and `3-4`. -/

/-- Checked periodic-table element spelling. -/
def periodicElement (atomicNumber : Nat) (positive : 0 < atomicNumber)
    (bounded : atomicNumber ≤ 118) : PeriodicElement :=
  { atomicNumber := atomicNumber, positive := positive, atMost118 := bounded }

def carbon : PeriodicElement := periodicElement 6 (by decide) (by decide)
def oxygen : PeriodicElement := periodicElement 8 (by decide) (by decide)

/-- A neutral, unlabelled atom of one element. -/
def atom (element : PeriodicElement) : SemanticAtom := { element := element }

/-- One ordinary single bond. -/
def singleBond (left right : Nat) : SemanticInteraction :=
  { participants := [left, right], kind := .covalent 1 }

/-- The raw five-atom ring source: `0 = C`, `1..4 = O`, bonds `0-1`, `0-2`, `1-2`, `0-3`,
`0-4`, `3-4`. -/
def source : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, oxygen, oxygen, oxygen, oxygen].map atom
        interactions :=
          [singleBond 0 1, singleBond 0 2, singleBond 1 2,
            singleBond 0 3, singleBond 0 4, singleBond 3 4] }
    spatial? := some { positions :=
      [{ x := 0, y := 0, z := 0 },
       { x := 1, y := 1, z := 0 },
       { x := -1, y := 1, z := 0 },
       { x := 0, y := -1, z := 1 },
       { x := 0, y := -1, z := -1 }] } }

theorem source_structurallyWellFormed : source.structurallyWellFormed? = true := by
  decide +kernel

theorem source_localizedGraphReady : source.molecule.localizedCIPGraphReady? = true := by
  decide +kernel

def certifiedSource : CertifiedAuthoritativeChemicalInput :=
  { input := source
    structurallyWellFormed :=
      (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp
        source_structurallyWellFormed }

/-- The actual certified localized input used by the fixture. -/
def input : CertifiedLocalizedCIPInput :=
  { certified := certifiedSource
    graphReady :=
      (certifiedSource.input.molecule.localizedCIPGraphReady?_eq_true_iff).mp
        source_localizedGraphReady }

abbrev Atom : Type := input.Atom

def atom0 : Atom := ⟨0, by decide⟩
def atom1 : Atom := ⟨1, by decide⟩
def atom2 : Atom := ⟨2, by decide⟩
def atom3 : Atom := ⟨3, by decide⟩
def atom4 : Atom := ⟨4, by decide⟩

/-! ### Automatic detection of the degree-four centre -/

theorem atom0_mem_centerSet : atom0 ∈ input.tetrahedralCenterSet := by
  decide +kernel

/-- The detected degree-four centre of the fixture. -/
def center : input.TetrahedralCenter := ⟨atom0, atom0_mem_centerSet⟩

/-! ### Concrete adjacency facts -/

theorem adj_zero_one : input.moleculeGraph.Adj atom0 atom1 := by decide +kernel
theorem adj_zero_two : input.moleculeGraph.Adj atom0 atom2 := by decide +kernel
theorem adj_one_two : input.moleculeGraph.Adj atom1 atom2 := by decide +kernel
theorem adj_zero_three : input.moleculeGraph.Adj atom0 atom3 := by decide +kernel
theorem adj_zero_four : input.moleculeGraph.Adj atom0 atom4 := by decide +kernel
theorem adj_three_four : input.moleculeGraph.Adj atom3 atom4 := by decide +kernel

theorem adj_two_zero : input.moleculeGraph.Adj atom2 center.1 :=
  input.moleculeGraph.adj_symm.mp adj_zero_two

theorem atom1_ne_center : atom1 ≠ center.1 := by decide +kernel
theorem atom2_ne_center : atom2 ≠ center.1 := by decide +kernel

/-- Every positive bond of the fixture has order one.  The `show` unfolds `SimpleBonded`, which is
not reducible during instance search; the finite `Fin`-quantifier decision procedure can then
evaluate the whole bond table in the kernel. -/
theorem simpleBonded : input.moleculeGraph.SimpleBonded := by
  show ∀ u v : Atom, input.moleculeGraph.Adj u v → input.moleculeGraph.bond u v = 1
  decide +kernel

/-! ### The centre-deleted graph is acyclic -/

/-- Every vertex of the centre-deleted graph has at most one neighbour: deleting atom `0` leaves
the two disjoint edges `1-2` and `3-4`. -/
theorem centerDeletedGraph_adj_unique_atoms :
    ∀ u v w : Atom, u ≠ center.1 → v ≠ center.1 → w ≠ center.1 →
      input.moleculeGraph.Adj u v → input.moleculeGraph.Adj u w → v = w := by
  decide +kernel

theorem centerDeletedGraph_adj_unique :
    ∀ u v w : {x : Atom // x ≠ center.1},
      (CertifiedLocalizedCIPInput.centerDeletedGraph input.moleculeGraph center.1).Adj u v →
      (CertifiedLocalizedCIPInput.centerDeletedGraph input.moleculeGraph center.1).Adj u w →
        v = w := by
  intro u v w huv huw
  exact Subtype.ext
    (centerDeletedGraph_adj_unique_atoms u.1 v.1 w.1 u.2 v.2 w.2 huv huw)

theorem centerDeletedGraph_acyclic :
    (CertifiedLocalizedCIPInput.centerDeletedGraph input.moleculeGraph center.1).IsAcyclic :=
  isAcyclic_of_adj_unique centerDeletedGraph_adj_unique




theorem centerDeletedComponentTreeAt (ligand : Atom) (hligand : ligand ≠ center.1) :
    input.CenterDeletedComponentTreeAt center.1 ligand :=
  input.centerDeletedComponentTreeAt_of_centerDeleted_acyclic center.1 ligand hligand
    centerDeletedGraph_acyclic

theorem canonicalLigand_ne_center (index : Fin 4) :
    input.canonicalLigandAtom center index ≠ center.1 := by
  intro equality
  have adjacent := input.canonicalLigandAtom_adj center index
  rw [equality] at adjacent
  exact CertifiedLocalizedCIPInput.moleculeGraph_not_adj_self
    input.moleculeGraph center.1 adjacent




theorem armDomain (index : Fin 4) : input.CenterDeletedArmDomain center index where
  singleBonded := simpleBonded
  tree := centerDeletedComponentTreeAt _
    (canonicalLigand_ne_center index)

/-- The **general component adapter** applied to the actual ligand component.  Unlike `armDomain`,
this consumes acyclicity of the connected component of the ligand inside the centre-deleted graph
itself, obtained here from the graph-level forest proof through
`SimpleGraph.IsAcyclic.isTree_connectedComponent`. -/
theorem componentTreeAt_of_component (index : Fin 4) :
    input.CenterDeletedComponentTreeAt center.1 (input.canonicalLigandAtom center index) :=
  input.centerDeletedComponentTreeAt_of_component_acyclic center.1
    (input.canonicalLigandAtom center index) (canonicalLigand_ne_center index)
    (SimpleGraph.IsAcyclic.isTree_connectedComponent centerDeletedGraph_acyclic _).IsAcyclic









theorem atom2_ne_atom1 : atom2 ≠ atom1 := by decide +kernel

theorem exists_canonicalLigandAtom_eq_atom1 :
    ∃ index : Fin 4, input.canonicalLigandAtom center index = atom1 := by
  obtain ⟨index, hindex⟩ :=
    (input.canonicalLigandNeighbor_bijective center).2 ⟨atom1, adj_zero_one⟩
  exact ⟨index, congrArg Subtype.val hindex⟩

/-- The canonical ligand slot occupied by atom `1`.  Noncomputable because the canonical neighbour
list is sorted by an opaque `Finset.sort`: the slot is obtained from surjectivity, not by
evaluation. -/
noncomputable def ligandIndex : Fin 4 :=
  Classical.choose exists_canonicalLigandAtom_eq_atom1

theorem canonicalLigandAtom_ligandIndex :
    input.canonicalLigandAtom center ligandIndex = atom1 :=
  Classical.choose_spec exists_canonicalLigandAtom_eq_atom1


theorem ligandTree : input.CenterDeletedComponentTreeAt center.1
    (input.canonicalLigandAtom center ligandIndex) :=
  centerDeletedComponentTreeAt _ (canonicalLigand_ne_center ligandIndex)

/-- The real occurrence `centre → 1 → 2` on the triangle through the centre. -/
def ligandNode : OfficialCIPNode input.Atom :=
  ((OfficialCIPNode.root center.1).extend atom1 0).extend atom2 0

theorem ligandNode_history : ligandNode.history = [atom2, atom1, center.1] := rfl

theorem ligandNode_parent? : ligandNode.parent? = some atom1 := rfl

theorem ligandNode_history_suffix :
    [input.canonicalLigandAtom center ligandIndex, center.1] <:+ ligandNode.history := by
  rw [canonicalLigandAtom_ligandIndex, ligandNode_history]
  exact ⟨[atom2], rfl⟩

theorem ligandNode_real : input.RealPathNode center.1 ligandNode := by
  refine ⟨atom2, SimpleGraph.Walk.cons adj_zero_one
    (SimpleGraph.Walk.cons adj_one_two SimpleGraph.Walk.nil), rfl, rfl, ?_, ?_, ?_, ?_⟩
  · show ((OfficialCIPNode.root center.1).extend atom1 0).childProvenance atom2 0 =
      OfficialCIPNodeProvenance.realAtom
    rw [OfficialCIPNode.childProvenance_real]
    decide +kernel
  · rw [SimpleGraph.Walk.isPath_def]
    decide +kernel
  · decide +kernel
  · intro parent hparent
    rw [ligandNode_parent?] at hparent
    have hparent' : parent = atom1 := (Option.some.inj hparent).symm
    rw [hparent']
    rw [SimpleGraph.Walk.penultimate_cons_cons, SimpleGraph.Walk.penultimate_cons_nil]

theorem ligandNode_centerNotParent : ligandNode.parent? ≠ some center.1 := by
  rw [ligandNode_parent?]
  exact fun same => atom1_ne_center (Option.some.inj same)

/-- The executable ring-closure child of the real node `centre → 1 → 2`. -/
def centerChild : OfficialCIPNode input.Atom := ligandNode.extend center.1 0

theorem centerChild_mem : centerChild ∈ input.executableOfficialCIPChildren ligandNode :=
  input.mem_executableOfficialCIPChildren_of_adjacent ligandNode atom2 center.1 0
    (input.isDuplicateLeaf_eq_false_of_provenance_real ligandNode
      (input.realPathNode_provenance ligandNode_real))
    rfl adj_two_zero adj_two_zero (Or.inr ligandNode_centerNotParent)




theorem centerChild_classification :
    (centerChild.provenance = OfficialCIPNodeProvenance.realAtom ∧
        center.1 ∉ ligandNode.history) ∨
      (center.1 = center.1 ∧
        centerChild.provenance = OfficialCIPNodeProvenance.ringDuplicate 0) :=
  input.centerArmRealNode_child_classification center ligandIndex ligandTree simpleBonded
    (node := ligandNode) (child := centerChild) (current := atom2) (next := center.1)
    ligandNode_real ligandNode_history_suffix rfl rfl centerChild_mem

/-- The executable ring-closure child has the original-centre ring-duplicate provenance: the left
branch of the classification is impossible because the centre already occurs on the branch. -/
theorem centerChild_provenance :
    centerChild.provenance = OfficialCIPNodeProvenance.ringDuplicate 0 := by
  rcases centerChild_classification with ⟨_, fresh⟩ | ⟨_, hprovenance⟩
  · exact absurd (by decide +kernel : center.1 ∈ ligandNode.history) fresh
  · exact hprovenance

theorem centerChild_rule1bRootDistance : centerChild.rule1bRootDistance = 0 := by
  unfold OfficialCIPNode.rule1bRootDistance
  rw [centerChild_provenance]




theorem ligandNode_centerAttachment :
    (∃ child ∈ input.executableOfficialCIPChildren ligandNode,
        child.rule1bRootDistance = 0) ↔
      input.moleculeGraph.Adj atom2 center.1 :=
  input.centerArmRealNode_centerAttachment_iff center ligandIndex ligandTree simpleBonded
    (node := ligandNode) (current := atom2)
    ligandNode_real ligandNode_history_suffix rfl ligandNode_centerNotParent

/-- The zero-distance child delivered by the attachment equivalence at the ring closure. -/
theorem ligandNode_zeroDistanceChild :
    ∃ child ∈ input.executableOfficialCIPChildren ligandNode,
      child.rule1bRootDistance = 0 :=
  ligandNode_centerAttachment.mpr adj_two_zero

/-- The actual witness is the ring-closure child itself. -/
theorem centerChild_is_zeroDistanceChild :
    centerChild ∈ input.executableOfficialCIPChildren ligandNode ∧
      centerChild.rule1bRootDistance = 0 :=
  ⟨centerChild_mem, centerChild_rule1bRootDistance⟩

/-! ### The full graph is cyclic -/

/-- The direct simple path `0 -> 2`. -/
def directPath : input.moleculeGraph.underlyingSimpleGraph.Path atom0 atom2 :=
  ⟨SimpleGraph.Walk.cons adj_zero_two SimpleGraph.Walk.nil, by
    rw [SimpleGraph.Walk.isPath_def]
    decide +kernel⟩

/-- The detour simple path `0 -> 1 -> 2` through the genuine triangle `0-1-2-0`. -/
def detourPath : input.moleculeGraph.underlyingSimpleGraph.Path atom0 atom2 :=
  ⟨SimpleGraph.Walk.cons adj_zero_one
      (SimpleGraph.Walk.cons adj_one_two SimpleGraph.Walk.nil), by
    rw [SimpleGraph.Walk.isPath_def]
    decide +kernel⟩

/-- **The full molecular graph is not acyclic.**  Two distinct simple paths join atoms `0` and
`2`, so global acyclicity fails, while the centre-deleted graph above is a forest. -/
theorem fullGraph_not_acyclic : ¬ input.moleculeGraph.Acyclic := by
  intro hacyclic
  have hEq : directPath = detourPath :=
    SimpleGraph.IsAcyclic.path_unique hacyclic directPath detourPath
  have hlen := congrArg
    (fun p : input.moleculeGraph.underlyingSimpleGraph.Path atom0 atom2 =>
      p.1.support.length) hEq
  simp [directPath, detourPath] at hlen

end CenterDeletedRingFixture

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.mem_of_head?_eq_some
assert_kernel_only TetraStereo.OneCenter.mem_of_getLast?_eq_some
assert_kernel_only TetraStereo.OneCenter.exists_walk_of_isChain_head?_getLast?
assert_kernel_only TetraStereo.OneCenter.mem_component_supp_of_mem_support
assert_kernel_only TetraStereo.OneCenter.support_induce_map
assert_kernel_only TetraStereo.OneCenter.isChain_attachWith_of_isChain
assert_kernel_only TetraStereo.OneCenter.nodup_attachWith
assert_kernel_only TetraStereo.OneCenter.head?_attachWith_of_head?
assert_kernel_only TetraStereo.OneCenter.getLast?_attachWith_of_getLast?
assert_kernel_only TetraStereo.OneCenter.eq_of_isChain_of_component_acyclic
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedComponentTreeAt_of_component_acyclic
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedComponentTreeAt_of_centerDeleted_acyclic
assert_kernel_only TetraStereo.OneCenter.exists_two_adj_of_isCycle
assert_kernel_only TetraStereo.OneCenter.isAcyclic_of_adj_unique
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.periodicElement
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.carbon
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.oxygen
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.atom
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.singleBond
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.source
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.source_structurallyWellFormed
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.source_localizedGraphReady
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.certifiedSource
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.input
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.Atom
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.atom0
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.atom1
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.atom2
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.atom3
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.atom4
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.atom0_mem_centerSet
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.center
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.adj_zero_one
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.adj_zero_two
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.adj_one_two
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.adj_zero_three
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.adj_zero_four
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.adj_three_four
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.adj_two_zero
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.atom1_ne_center
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.atom2_ne_center
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.simpleBonded
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.centerDeletedGraph_adj_unique_atoms
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.centerDeletedGraph_adj_unique
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.centerDeletedGraph_acyclic
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.centerDeletedComponentTreeAt
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.canonicalLigand_ne_center
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.armDomain
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.componentTreeAt_of_component
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.atom2_ne_atom1
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.exists_canonicalLigandAtom_eq_atom1
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.ligandIndex
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.canonicalLigandAtom_ligandIndex
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.ligandTree
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.ligandNode
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.ligandNode_history
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.ligandNode_parent?
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.ligandNode_history_suffix
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.ligandNode_real
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.ligandNode_centerNotParent
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.centerChild
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.centerChild_mem
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.centerChild_classification
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.centerChild_provenance
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.centerChild_rule1bRootDistance
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.ligandNode_centerAttachment
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.ligandNode_zeroDistanceChild
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.centerChild_is_zeroDistanceChild
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.directPath
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.detourPath
assert_kernel_only TetraStereo.OneCenter.CenterDeletedRingFixture.fullGraph_not_acyclic
