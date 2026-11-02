import TetraStereo.OneCenter.DeclarativeCIPCanonicalOrder
import TetraStereo.OneCenter.DeclarativeCIPConstitutionalTotality

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

open Certificate.CanonicalSphereKey (Key sortDesc keyObservation slotOf WellShaped)

noncomputable section

open scoped Classical

universe u

/-!
# Canonical constitutional outcomes do not depend on the faithful expansion

`Problem.RuleOutcome` quantifies over *every* admissible expansion of both ligands.  A canonical
outcome computed from one pair of faithful exact expansions is therefore a rule outcome only if
every other faithful expansion yields the same outcome.

This module proves that it does, without constructing a tree isomorphism.  At a real node, the
faithful-expansion multiplicities, duplicate-distance payloads and atom-bearing condition fix the
number of children carrying each node label.  Matched nodes (same label, depth, parent atom and
ancestor atoms with depths) therefore have label-matched children, and by induction from the leaves
they have equal vector keys (`faithful_ruleKey_eq_of_matched`).  With the width independence of the
canonical order, all canonical observations of two faithful expansions of the same ligand agree
(`faithful_addressObservation_eq`), and so do their canonical outcomes against any third hierarchy.

The total `Problem.RuleOutcome` endpoint and the `ExpansionsFaithful` predicate are re-exported from
`DeclarativeCIPConstitutionalTotality`, whose proof uses the shared faithful-expansion isomorphism
and canonical-outcome transport.  This module retains the independent matched-node key argument and
the canonical-outcome agreement that compares arbitrary faithful expansions.
-/

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

open RootedDigraph

local instance (graph : RootedDigraph Atom) : Fintype graph.Node := graph.nodeFintype

/-! ## Structure of addressed hierarchies -/

section Tree

variable {graph : RootedDigraph Atom} (addressing : graph.Addressing)

include addressing in
theorem not_transGen_root (node : graph.Node) : ¬ Relation.TransGen graph.child node graph.root := by
  intro h
  rcases Relation.TransGen.tail'_iff.1 h with ⟨parent, _, hedge⟩
  exact addressing.not_child_root parent hedge

include addressing in
/-- Strict ancestors of a node in an addressed hierarchy form a chain. -/
theorem transGen_chain {first second node : graph.Node}
    (hfirst : Relation.TransGen graph.child first node)
    (hsecond : Relation.TransGen graph.child second node) :
    first = second ∨ Relation.TransGen graph.child first second ∨
      Relation.TransGen graph.child second first := by
  induction hfirst generalizing second with
  | single hedge =>
      rcases Relation.TransGen.tail'_iff.1 hsecond with ⟨parent, hpath, hparent⟩
      have hp : parent = first := addressing.parent_unique hparent hedge
      subst hp
      rcases Relation.ReflTransGen.cases_tail hpath with rfl | ⟨_, _, _⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Relation.TransGen.tail' (by assumption) (by assumption)))
  | @tail middle node hpath hedge ih =>
      rcases Relation.TransGen.tail'_iff.1 hsecond with ⟨parent, hreach, hparent⟩
      have hp : parent = middle := addressing.parent_unique hparent hedge
      subst hp
      rcases Relation.ReflTransGen.cases_tail hreach with rfl | ⟨_, _, _⟩
      · exact Or.inr (Or.inl hpath)
      · exact ih (Relation.TransGen.tail' (by assumption) (by assumption))

include addressing in
/-- A strict ancestor of a child is the parent or a strict ancestor of the parent. -/
theorem transGen_child_iff {parent node ancestor : graph.Node} (hedge : graph.child parent node) :
    Relation.TransGen graph.child ancestor node ↔
      ancestor = parent ∨ Relation.TransGen graph.child ancestor parent := by
  constructor
  · intro h
    rcases Relation.TransGen.tail'_iff.1 h with ⟨other, hreach, hother⟩
    have hp : other = parent := addressing.parent_unique hother hedge
    subst hp
    rcases Relation.ReflTransGen.cases_tail hreach with rfl | ⟨_, _, _⟩
    · exact Or.inl rfl
    · exact Or.inr (Relation.TransGen.tail' (by assumption) (by assumption))
  · rintro (rfl | h)
    · exact Relation.TransGen.single hedge
    · exact Relation.TransGen.tail h hedge

include addressing in
theorem parentAtom_child_iff {parent node : graph.Node} (hedge : graph.child parent node)
    (atom : Atom) :
    ParentAtom graph node atom ↔ (graph.label parent).atom? = some atom := by
  constructor
  · rintro ⟨other, hother, hatom⟩
    rwa [addressing.parent_unique hother hedge] at hatom
  · intro h
    exact ⟨parent, hedge, h⟩

end Tree

/-! ## Faithful expansions -/

section Faithful

variable {molecule : MoleculeGraph Atom} {externalParent ligand : Atom}
  {graph : RootedDigraph Atom}
  (hgraph : FaithfulExactExpansion molecule externalParent ligand graph)

include hgraph in
theorem faithful_exists_addressing : Nonempty graph.Addressing := by
  obtain ⟨_, addressing, _⟩ := hgraph.1
  exact ⟨addressing⟩

include hgraph in
/-- A node with a child is a real atom node. -/
theorem faithful_real_of_child {parent node : graph.Node} (hedge : graph.child parent node) :
    (graph.label parent).provenance = NodeProvenance.realAtom ∧
      ∃ atom, (graph.label parent).atom? = some atom := by
  obtain ⟨⟨_, hcompat, hterminal, _⟩, _⟩ := hgraph.1
  have hreal : (graph.label parent).provenance = NodeProvenance.realAtom := by
    cases hprov : (graph.label parent).provenance with
    | realAtom => rfl
    | _ =>
        exfalso
        exact hterminal parent (by simp [ProvenanceTerminal, hprov]) node hedge
  refine ⟨hreal, ?_⟩
  have h := hcompat parent
  unfold LabelCompatible at h
  rw [hreal] at h
  exact h

include hgraph in
theorem faithful_root_label : graph.label graph.root = ⟨some ligand, NodeProvenance.realAtom⟩ :=
  hgraph.1.1.1

include hgraph in
theorem faithful_adj_of_child {parent node : graph.Node} (hedge : graph.child parent node)
    {parentAtom nodeAtom : Atom} (hp : (graph.label parent).atom? = some parentAtom)
    (hn : (graph.label node).atom? = some nodeAtom) : molecule.Adj parentAtom nodeAtom :=
  hgraph.1.1.2.2.2 parent node parentAtom nodeAtom hedge hp hn

theorem not_adj_self (molecule : MoleculeGraph Atom) (atom : Atom) : ¬ molecule.Adj atom atom := by
  simp [MoleculeGraph.Adj, molecule.bond_self]

theorem childCountWhere_congr {graph : RootedDigraph Atom} {parent : graph.Node}
    {first second : graph.Node → Prop}
    (h : ∀ node, graph.child parent node → (first node ↔ second node)) :
    ChildCountWhere graph parent first = ChildCountWhere graph parent second := by
  unfold ChildCountWhere
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun node =>
    ⟨fun hn => ⟨hn.1, (h node hn.1).1 hn.2⟩, fun hn => ⟨hn.1, (h node hn.1).2 hn.2⟩⟩

theorem childCountWhere_eq_zero {graph : RootedDigraph Atom} {parent : graph.Node}
    {predicate : graph.Node → Prop} (h : ∀ node, graph.child parent node → ¬ predicate node) :
    ChildCountWhere graph parent predicate = 0 := by
  unfold ChildCountWhere
  rw [Nat.card_eq_zero]
  left
  exact ⟨fun node => h node.1 node.2.1 node.2.2⟩

theorem childCountWhere_pos {graph : RootedDigraph Atom} {parent node : graph.Node}
    {predicate : graph.Node → Prop} (hedge : graph.child parent node) (hnode : predicate node) :
    0 < ChildCountWhere graph parent predicate := by
  unfold ChildCountWhere
  haveI : Nonempty {node : graph.Node // graph.child parent node ∧ predicate node} :=
    ⟨⟨node, hedge, hnode⟩⟩
  exact Nat.card_pos

include hgraph in
/-- A real child's atom is absent from the branch history of its parent. -/
theorem faithful_real_child_not_branch {parent node : graph.Node} (hedge : graph.child parent node)
    {atom : Atom} (hlabel : graph.label node = ⟨some atom, NodeProvenance.realAtom⟩) :
    ¬ BranchAncestorAtom graph externalParent atom parent := by
  obtain ⟨hreal, parentAtom, hparentAtom⟩ := faithful_real_of_child hgraph hedge
  obtain ⟨_, _, hmult⟩ := hgraph.1
  have hcounts := hmult parent parentAtom hparentAtom (by simp [ProvenanceRealAtom, hreal]) atom
  have hpos : 0 < ChildAtomProvenanceCount graph parent atom ProvenanceRealAtom :=
    childCountWhere_pos hedge ⟨by simp [hlabel], by simp [hlabel, ProvenanceRealAtom]⟩
  rw [hcounts.2.2.2] at hpos
  split at hpos
  · rename_i hcond
    exact hcond.2
  · omega

include hgraph in
/-- No real hierarchy node represents the external stereocenter. -/
theorem faithful_real_atom_ne_externalParent {node : graph.Node} {atom : Atom}
    (hlabel : graph.label node = ⟨some atom, NodeProvenance.realAtom⟩) : atom ≠ externalParent := by
  obtain ⟨_, addressing, _⟩ := hgraph.1
  rcases (graph.reachable node).cases_tail with hroot | ⟨parent, _, hedge⟩
  · subst hroot
    rw [faithful_root_label hgraph] at hlabel
    have hatom : ligand = atom := by
      have := congrArg NodeLabel.atom? hlabel
      simpa using this
    subst hatom
    intro heq
    have hadj := hgraph.2.1
    rw [heq] at hadj
    exact not_adj_self molecule _ hadj
  · intro heq
    exact faithful_real_child_not_branch hgraph hedge hlabel (Or.inl heq)

include hgraph in
theorem faithful_label_of_child {parent node : graph.Node} (hedge : graph.child parent node)
    {atom : Atom} (hatom : (graph.label parent).atom? = some atom) :
    graph.label parent = ⟨some atom, NodeProvenance.realAtom⟩ := by
  obtain ⟨hreal, _⟩ := faithful_real_of_child hgraph hedge
  cases hlabel : graph.label parent with
  | mk atom? provenance =>
      rw [hlabel] at hatom hreal
      simp only at hatom hreal
      rw [hatom, hreal]

theorem faithful_has_child_of_transGen {ancestor node : graph.Node}
    (h : Relation.TransGen graph.child ancestor node) : ∃ child, graph.child ancestor child := by
  rcases Relation.TransGen.head'_iff.1 h with ⟨child, hedge, _⟩
  exact ⟨child, hedge⟩

include hgraph in
/-- A real node's atom does not occur at any strict ancestor. -/
theorem faithful_ancestor_atom_ne {ancestor node : graph.Node}
    (h : Relation.TransGen graph.child ancestor node) {atom : Atom}
    (hlabel : graph.label node = ⟨some atom, NodeProvenance.realAtom⟩) :
    (graph.label ancestor).atom? ≠ some atom := by
  obtain ⟨_, addressing, _⟩ := hgraph.1
  intro hancestor
  rcases Relation.TransGen.tail'_iff.1 h with ⟨parent, hreach, hedge⟩
  have hbranch := faithful_real_child_not_branch hgraph hedge hlabel
  rcases Relation.ReflTransGen.cases_tail hreach with rfl | ⟨middle, hmid, hmidEdge⟩
  · exact not_adj_self molecule atom
      (faithful_adj_of_child hgraph hedge hancestor (by simp [hlabel]))
  · exact hbranch (Or.inr ⟨ancestor, Relation.TransGen.tail' hmid hmidEdge, hancestor⟩)

include hgraph in
/-- Strict ancestors of a node carry pairwise distinct atoms. -/
theorem faithful_ancestor_atoms_injective {first second node : graph.Node}
    (hfirst : Relation.TransGen graph.child first node)
    (hsecond : Relation.TransGen graph.child second node) {atom : Atom}
    (hfirstAtom : (graph.label first).atom? = some atom)
    (hsecondAtom : (graph.label second).atom? = some atom) : first = second := by
  obtain ⟨_, addressing, _⟩ := hgraph.1
  rcases transGen_chain addressing hfirst hsecond with h | h | h
  · exact h
  · obtain ⟨child, hchild⟩ := faithful_has_child_of_transGen hsecond
    exact (faithful_ancestor_atom_ne hgraph h
      (faithful_label_of_child hgraph hchild hsecondAtom) hfirstAtom).elim
  · obtain ⟨child, hchild⟩ := faithful_has_child_of_transGen hfirst
    exact (faithful_ancestor_atom_ne hgraph h
      (faithful_label_of_child hgraph hchild hfirstAtom) hsecondAtom).elim

end Faithful

/-! ## Matched nodes -/

/-- A strict ancestor of `node` carries `atom` at depth `depth`. -/
def AncestorAt (graph : RootedDigraph Atom) (node : graph.Node) (atom : Atom) (depth : ℕ) :
    Prop :=
  ∃ ancestor, Relation.TransGen graph.child ancestor node ∧
    (graph.label ancestor).atom? = some atom ∧ graph.depth ancestor = depth

/-- The admissible Rule-1b payloads of a ring duplicate of `atom` below `node`. -/
def RingDistanceValid (graph : RootedDigraph Atom) (externalParent atom : Atom)
    (node : graph.Node) (distance : ℕ) : Prop :=
  (atom = externalParent ∧ distance = 0) ∨
    ∃ depth, AncestorAt graph node atom depth ∧ distance = depth + 1

section Valid

variable {molecule : MoleculeGraph Atom} {externalParent ligand : Atom}
  {graph : RootedDigraph Atom}
  (hgraph : FaithfulExactExpansion molecule externalParent ligand graph)

include hgraph in
theorem faithful_ringDistance_unique {node : graph.Node} {atom : Atom} {first second : ℕ}
    (hfirst : RingDistanceValid graph externalParent atom node first)
    (hsecond : RingDistanceValid graph externalParent atom node second) : first = second := by
  have hnotExternal : ∀ depth, AncestorAt graph node atom depth → atom ≠ externalParent := by
    rintro depth ⟨ancestor, hpath, hatom, _⟩
    obtain ⟨child, hchild⟩ := faithful_has_child_of_transGen hpath
    exact faithful_real_atom_ne_externalParent hgraph (faithful_label_of_child hgraph hchild hatom)
  rcases hfirst with ⟨hext, rfl⟩ | ⟨d₁, h₁, rfl⟩ <;>
    rcases hsecond with ⟨_, rfl⟩ | ⟨d₂, h₂, rfl⟩
  · rfl
  · exact (hnotExternal d₂ h₂ hext).elim
  · rename_i hext
    exact (hnotExternal d₁ h₁ hext).elim
  · obtain ⟨a₁, p₁, at₁, rfl⟩ := h₁
    obtain ⟨a₂, p₂, at₂, rfl⟩ := h₂
    rw [faithful_ancestor_atoms_injective hgraph p₁ p₂ at₁ at₂]

include hgraph in
/-- Every child of a faithful expansion is atom-bearing, real or a duplicate, and its duplicate
payload is the one prescribed by its parent's depth and history. -/
theorem faithful_child_label {parent node : graph.Node} (hedge : graph.child parent node) :
    ∃ atom, (graph.label node).atom? = some atom ∧
      ((graph.label node).provenance = NodeProvenance.realAtom ∨
        (graph.label node).provenance =
          NodeProvenance.multipleBondDuplicate (graph.depth parent + 1) ∨
        ∃ distance, (graph.label node).provenance = NodeProvenance.ringDuplicate distance ∧
          RingDistanceValid graph externalParent atom parent distance) := by
  obtain ⟨⟨_, hcompat, _, _⟩, addressing, _⟩ := hgraph.1
  obtain ⟨atom, hatom⟩ := hgraph.2.2.1 parent node hedge
  have hdist := hgraph.2.2.2 addressing parent node hedge
  have hcomp := hcompat node
  refine ⟨atom, hatom, ?_⟩
  cases hlabel : graph.label node with
  | mk atom? provenance =>
      rw [hlabel] at hatom hdist hcomp
      simp only at hatom
      subst hatom
      cases provenance with
      | realAtom => exact Or.inl rfl
      | multipleBondDuplicate distance =>
          simp only at hdist
          right; left
          rw [hdist, addressing.address_length_eq_depth]
      | ringDuplicate distance =>
          simp only at hdist
          right; right
          refine ⟨distance, rfl, ?_⟩
          rcases hdist with hext | ⟨ancestor, hpath, hanc, hd⟩
          · exact Or.inl hext
          · exact Or.inr ⟨graph.depth ancestor, ⟨ancestor, hpath, hanc, rfl⟩,
              by rw [hd, addressing.address_length_eq_depth]⟩
      | phantom _ => simp [LabelCompatible] at hcomp
      | lonePair _ => simp [LabelCompatible] at hcomp
      | auxiliary _ => simp [LabelCompatible] at hcomp

end Valid

/-- Two nodes, possibly of different hierarchies, are matched when they carry the same label at the
same depth, are both roots or both non-roots, and have the same parent atom and the same strict
ancestor atoms at the same depths. -/
structure Matched {first second : RootedDigraph Atom} (left : first.Node) (right : second.Node) :
    Prop where
  label : first.label left = second.label right
  depth : first.depth left = second.depth right
  root : left = first.root ↔ right = second.root
  parent : ∀ atom, ParentAtom first left atom ↔ ParentAtom second right atom
  ancestor : ∀ atom depth, AncestorAt first left atom depth ↔ AncestorAt second right atom depth

section MatchedFacts

variable {first second : RootedDigraph Atom} {left : first.Node} {right : second.Node}

theorem Matched.ancestorAtom (h : Matched left right) (atom : Atom) :
    AncestorAtom first left atom ↔ AncestorAtom second right atom := by
  constructor
  · rintro ⟨ancestor, hpath, hatom⟩
    obtain ⟨other, hother, hotherAtom, _⟩ :=
      (h.ancestor atom (first.depth ancestor)).1 ⟨ancestor, hpath, hatom, rfl⟩
    exact ⟨other, hother, hotherAtom⟩
  · rintro ⟨ancestor, hpath, hatom⟩
    obtain ⟨other, hother, hotherAtom, _⟩ :=
      (h.ancestor atom (second.depth ancestor)).2 ⟨ancestor, hpath, hatom, rfl⟩
    exact ⟨other, hother, hotherAtom⟩

theorem Matched.branch (h : Matched left right) (externalParent atom : Atom) :
    BranchAncestorAtom first externalParent atom left ↔
      BranchAncestorAtom second externalParent atom right := by
  unfold BranchAncestorAtom
  rw [h.ancestorAtom]

theorem Matched.suppressed (h : Matched left right) (externalParent atom : Atom) :
    SuppressedParentAtom first externalParent atom left ↔
      SuppressedParentAtom second externalParent atom right := by
  unfold SuppressedParentAtom
  rw [h.root, h.parent]

theorem Matched.ringDistance (h : Matched left right) (externalParent atom : Atom)
    (distance : ℕ) :
    RingDistanceValid first externalParent atom left distance ↔
      RingDistanceValid second externalParent atom right distance := by
  unfold RingDistanceValid
  simp only [h.ancestor]

end MatchedFacts

/-! ## Equal label counts at matched nodes -/

/-- The number of children carrying a given label. -/
def labelCount (graph : RootedDigraph Atom) (parent : graph.Node) (label : NodeLabel Atom) : ℕ :=
  ChildCountWhere graph parent fun node => graph.label node = label

section Counts

variable {molecule : MoleculeGraph Atom} {externalParent ligand : Atom}

theorem labelCount_eq_zero_of_not_child {graph : RootedDigraph Atom} {parent : graph.Node}
    (hleaf : ∀ node, ¬ graph.child parent node) (label : NodeLabel Atom) :
    labelCount graph parent label = 0 :=
  childCountWhere_eq_zero fun node hedge => (hleaf node hedge).elim

/-- The label count at a real node, expressed through the faithful-expansion data. -/
theorem faithful_labelCount {graph : RootedDigraph Atom}
    (hgraph : FaithfulExactExpansion molecule externalParent ligand graph)
    {parent : graph.Node} {parentAtom : Atom}
    (hparent : graph.label parent = ⟨some parentAtom, NodeProvenance.realAtom⟩)
    (label : NodeLabel Atom) :
    labelCount graph parent label =
      match label with
      | ⟨some atom, .realAtom⟩ =>
          if molecule.Adj parentAtom atom ∧
              ¬ BranchAncestorAtom graph externalParent atom parent then 1 else 0
      | ⟨some atom, .multipleBondDuplicate distance⟩ =>
          if distance = graph.depth parent + 1 then molecule.bond parentAtom atom - 1 else 0
      | ⟨some atom, .ringDuplicate distance⟩ =>
          if RingDistanceValid graph externalParent atom parent distance then
            (if molecule.Adj parentAtom atom ∧
                BranchAncestorAtom graph externalParent atom parent ∧
                ¬ SuppressedParentAtom graph externalParent atom parent then 1 else 0)
          else 0
      | _ => 0 := by
  obtain ⟨_, _, hmult⟩ := hgraph.1
  have hcounts := fun atom => hmult parent parentAtom (by simp [hparent])
    (by simp [hparent, ProvenanceRealAtom]) atom
  have hchild := fun {node : graph.Node} (hedge : graph.child parent node) =>
    faithful_child_label hgraph hedge
  unfold labelCount
  rcases label with ⟨_ | atom, provenance⟩
  · apply childCountWhere_eq_zero
    intro node hedge hlabel
    obtain ⟨atom, hatom, _⟩ := hchild hedge
    rw [hlabel] at hatom
    simp at hatom
  · cases provenance with
    | realAtom =>
        dsimp only
        rw [← (hcounts atom).2.2.2]
        apply childCountWhere_congr
        intro node _
        constructor
        · intro h; simp [h, ProvenanceRealAtom]
        · rintro ⟨hatom, hprov⟩
          cases hlabel : graph.label node with
          | mk atom? provenance =>
              rw [hlabel] at hatom hprov
              simp only at hatom hprov
              cases provenance <;> simp_all [ProvenanceRealAtom]
    | multipleBondDuplicate distance =>
        simp only
        split
        · rename_i hd
          rw [← (hcounts atom).2.1]
          apply childCountWhere_congr
          intro node hedge
          constructor
          · intro h; simp [h, ProvenanceMultipleBondDuplicate]
          · rintro ⟨hatom, hprov⟩
            obtain ⟨_, _, hkind⟩ := hchild hedge
            cases hlabel : graph.label node with
            | mk atom? provenance =>
                rw [hlabel] at hatom hprov hkind
                simp only at hatom hprov hkind
                cases provenance <;> simp_all [ProvenanceMultipleBondDuplicate]
        · rename_i hd
          apply childCountWhere_eq_zero
          intro node hedge hlabel
          obtain ⟨_, _, hkind⟩ := hchild hedge
          rw [hlabel] at hkind
          simp at hkind
          exact hd hkind
    | ringDuplicate distance =>
        simp only
        split
        · rename_i hvalid
          rw [← (hcounts atom).2.2.1]
          apply childCountWhere_congr
          intro node hedge
          constructor
          · intro h; simp [h, ProvenanceRingDuplicate]
          · rintro ⟨hatom, hprov⟩
            obtain ⟨found, hfound, hkind⟩ := hchild hedge
            rw [hatom] at hfound
            simp only [Option.some.injEq] at hfound
            subst hfound
            cases hlabel : graph.label node with
            | mk atom? provenance =>
                rw [hlabel] at hatom hprov hkind
                simp only at hatom hprov hkind
                subst hatom
                cases provenance with
                | ringDuplicate other =>
                    simp only [reduceCtorEq, false_or] at hkind
                    obtain ⟨_, hother, hotherValid⟩ := hkind
                    cases hother
                    rw [faithful_ringDistance_unique hgraph hotherValid hvalid]
                | _ => simp [ProvenanceRingDuplicate] at hprov
        · rename_i hvalid
          apply childCountWhere_eq_zero
          intro node hedge hlabel
          obtain ⟨found, hfound, hkind⟩ := hchild hedge
          rw [hlabel] at hfound hkind
          simp only [Option.some.injEq] at hfound
          subst hfound
          simp only [reduceCtorEq, false_or, NodeProvenance.ringDuplicate.injEq] at hkind
          obtain ⟨_, rfl, hother⟩ := hkind
          exact hvalid hother
    | phantom _ | lonePair _ | auxiliary _ =>
        apply childCountWhere_eq_zero
        intro node hedge hlabel
        obtain ⟨_, _, hkind⟩ := hchild hedge
        rw [hlabel] at hkind
        simp at hkind

/-- Matched nodes of two faithful expansions of the same ligand have equal label counts. -/
theorem faithful_labelCount_eq {first second : RootedDigraph Atom}
    (hfirst : FaithfulExactExpansion molecule externalParent ligand first)
    (hsecond : FaithfulExactExpansion molecule externalParent ligand second)
    {left : first.Node} {right : second.Node} (hmatched : Matched left right)
    (label : NodeLabel Atom) :
    labelCount first left label = labelCount second right label := by
  by_cases hleaf : ∃ node, first.child left node
  · obtain ⟨node, hedge⟩ := hleaf
    obtain ⟨_, parentAtom, hatom⟩ := faithful_real_of_child hfirst hedge
    have hlabel := faithful_label_of_child hfirst hedge hatom
    have hlabel' : second.label right = ⟨some parentAtom, NodeProvenance.realAtom⟩ := by
      rw [← hmatched.label, hlabel]
    rw [faithful_labelCount hfirst hlabel, faithful_labelCount hsecond hlabel']
    rcases label with ⟨_ | atom, provenance⟩
    · rfl
    · cases provenance <;>
        simp only [hmatched.branch, hmatched.suppressed, hmatched.ringDistance, hmatched.depth]
  · have hleft : ∀ node, ¬ first.child left node := fun node h => hleaf ⟨node, h⟩
    have hright : ∀ node, ¬ second.child right node := by
      intro node hedge
      obtain ⟨hreal, parentAtom, hatom⟩ := faithful_real_of_child hsecond hedge
      have hlabel := faithful_label_of_child hsecond hedge hatom
      rw [← hmatched.label] at hlabel
      obtain ⟨⟨_, _, hterminal, _⟩, _⟩ := hfirst.1
      -- `left` is real but childless; its child count for real atoms must still vanish.
      have hzero := labelCount_eq_zero_of_not_child hleft
      have hcountRight := faithful_labelCount hsecond (by rw [← hmatched.label]; exact hlabel)
      have hcountLeft := faithful_labelCount hfirst hlabel
      obtain ⟨found, hfound, hkind⟩ := faithful_child_label hsecond hedge
      have hpos : 0 < labelCount second right (second.label node) :=
        childCountWhere_pos hedge rfl
      have heq : labelCount first left (second.label node) =
          labelCount second right (second.label node) := by
        rw [hcountLeft, hcountRight]
        rcases second.label node with ⟨_ | atom, provenance⟩
        · rfl
        · cases provenance <;>
            simp only [hmatched.branch, hmatched.suppressed, hmatched.ringDistance,
              hmatched.depth]
      rw [← heq, hzero] at hpos
      exact lt_irrefl 0 hpos
    rw [labelCount_eq_zero_of_not_child hleft, labelCount_eq_zero_of_not_child hright]

end Counts

/-! ## Matched roots and children -/

section MatchedConstruction

theorem ancestorAt_child_iff {graph : RootedDigraph Atom} (addressing : graph.Addressing)
    {parent node : graph.Node} (hedge : graph.child parent node) (atom : Atom) (depth : ℕ) :
    AncestorAt graph node atom depth ↔
      ((graph.label parent).atom? = some atom ∧ graph.depth parent = depth) ∨
        AncestorAt graph parent atom depth := by
  unfold AncestorAt
  simp only [transGen_child_iff addressing hedge]
  constructor
  · rintro ⟨ancestor, rfl | hpath, hatom, hdepth⟩
    · exact Or.inl ⟨hatom, hdepth⟩
    · exact Or.inr ⟨ancestor, hpath, hatom, hdepth⟩
  · rintro (⟨hatom, hdepth⟩ | ⟨ancestor, hpath, hatom, hdepth⟩)
    · exact ⟨parent, Or.inl rfl, hatom, hdepth⟩
    · exact ⟨ancestor, Or.inr hpath, hatom, hdepth⟩

variable {molecule : MoleculeGraph Atom} {externalParent ligand : Atom}
  {first second : RootedDigraph Atom}
  (hfirst : FaithfulExactExpansion molecule externalParent ligand first)
  (hsecond : FaithfulExactExpansion molecule externalParent ligand second)

include hfirst hsecond in
theorem faithful_matched_root : Matched first.root second.root := by
  obtain ⟨_, firstAddressing, _⟩ := hfirst.1
  obtain ⟨_, secondAddressing, _⟩ := hsecond.1
  refine ⟨by rw [faithful_root_label hfirst, faithful_root_label hsecond], by
    rw [first.root_depth, second.root_depth], iff_of_true rfl rfl, ?_, ?_⟩
  · intro atom
    constructor
    · rintro ⟨parent, hedge, _⟩
      exact (firstAddressing.not_child_root parent hedge).elim
    · rintro ⟨parent, hedge, _⟩
      exact (secondAddressing.not_child_root parent hedge).elim
  · intro atom depth
    constructor
    · rintro ⟨ancestor, hpath, _⟩
      exact (not_transGen_root firstAddressing ancestor hpath).elim
    · rintro ⟨ancestor, hpath, _⟩
      exact (not_transGen_root secondAddressing ancestor hpath).elim

include hfirst hsecond in
theorem faithful_matched_child {left : first.Node} {right : second.Node}
    (hmatched : Matched left right) {leftChild : first.Node} {rightChild : second.Node}
    (hleft : first.child left leftChild) (hright : second.child right rightChild)
    (hlabel : first.label leftChild = second.label rightChild) :
    Matched leftChild rightChild := by
  obtain ⟨_, firstAddressing, _⟩ := hfirst.1
  obtain ⟨_, secondAddressing, _⟩ := hsecond.1
  refine ⟨hlabel, ?_, ?_, ?_, ?_⟩
  · rw [first.child_depth hleft, second.child_depth hright, hmatched.depth]
  · exact iff_of_false (fun h => firstAddressing.not_child_root left (h ▸ hleft))
      (fun h => secondAddressing.not_child_root right (h ▸ hright))
  · intro atom
    rw [parentAtom_child_iff firstAddressing hleft, parentAtom_child_iff secondAddressing hright,
      hmatched.label]
  · intro atom depth
    rw [ancestorAt_child_iff firstAddressing hleft, ancestorAt_child_iff secondAddressing hright,
      hmatched.label, hmatched.depth, hmatched.ancestor]

include hfirst hsecond in
/-- Equal label counts give a label-preserving bijection between the children of matched nodes. -/
theorem faithful_child_bijection {left : first.Node} {right : second.Node}
    (hmatched : Matched left right) :
    ∃ bijection : {node // first.child left node} ≃ {node // second.child right node},
      ∀ node, second.label (bijection node).1 = first.label node.1 := by
  have hfiber : ∀ label : NodeLabel Atom,
      Nonempty ({node : {node // first.child left node} // first.label node.1 = label} ≃
        {node : {node // second.child right node} // second.label node.1 = label}) := by
    intro label
    apply Finite.card_eq.1
    have h := faithful_labelCount_eq hfirst hsecond hmatched label
    unfold labelCount ChildCountWhere at h
    rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun node => first.child left node)
        (fun node => first.label node = label)),
      Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun node => second.child right node)
        (fun node => second.label node = label))]
    exact h
  exact ⟨Equiv.ofFiberEquiv (f := fun node : {node // first.child left node} => first.label node.1)
    (g := fun node : {node // second.child right node} => second.label node.1)
    (fun label => Classical.choice (hfiber label)),
    fun node => Equiv.ofFiberEquiv_map
      (f := fun node : {node // first.child left node} => first.label node.1)
      (g := fun node : {node // second.child right node} => second.label node.1) _ node⟩

include hfirst hsecond in
/-- **Key uniqueness.**  Matched nodes of two faithful expansions of the same ligand have equal
vector keys under every layout. -/
theorem faithful_ruleKey_eq_of_matched (W D : ℕ) :
    ∀ (left : first.Node) (right : second.Node), Matched left right →
      ruleKey molecule first W D left = ruleKey molecule second W D right := by
  intro left
  refine node_induction first (motive := fun left => ∀ right : second.Node, Matched left right →
    ruleKey molecule first W D left = ruleKey molecule second W D right) ?_ left
  intro left ih right hmatched
  obtain ⟨bijection, hbijection⟩ := faithful_child_bijection hfirst hsecond hmatched
  have hperm : ((first.childList left).map (ruleKey molecule first W D)).Perm
      ((second.childList right).map (ruleKey molecule second W D)) := by
    rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, ← Multiset.map_coe]
    simp only [RootedDigraph.childList, Finset.coe_toList]
    apply Multiset.map_eq_map_of_bij_of_nodup _ _ (Finset.nodup _) (Finset.nodup _)
      (fun node hnode => (bijection ⟨node, by simpa using hnode⟩).1)
    · intro node _
      simpa using (bijection _).2
    · intro a ha b hb hab
      have := bijection.injective (Subtype.ext hab)
      simpa using this
    · intro node hnode
      refine ⟨(bijection.symm ⟨node, by simpa using hnode⟩).1,
        by simpa using (bijection.symm ⟨node, by simpa using hnode⟩).2, ?_⟩
      simp
    · intro node hnode
      have hchild : first.child left node := by simpa using hnode
      exact ih node hchild _ (faithful_matched_child hfirst hsecond hmatched hchild
        (bijection ⟨node, hchild⟩).2 (hbijection ⟨node, hchild⟩).symm)
  have hobs : ∀ rule, nodeObservation molecule first rule left =
      nodeObservation molecule second rule right := by
    intro rule
    simp only [nodeObservation, hmatched.label, hmatched.depth]
  rw [ruleKey_eq, ruleKey_eq]
  simp only [ruleComponent, hobs, Certificate.CanonicalSphereKey.sortDesc_eq_of_perm hperm]

include hfirst hsecond in
theorem faithful_root_ruleKey_eq (W D : ℕ) :
    ruleKey molecule first W D first.root = ruleKey molecule second W D second.root :=
  faithful_ruleKey_eq_of_matched hfirst hsecond W D _ _ (faithful_matched_root hfirst hsecond)

end MatchedConstruction

/-! ## Observations and outcomes across expansions -/

section Outcomes

variable {molecule : MoleculeGraph Atom}

/-- Canonical observations of two faithful expansions of the same ligand coincide. -/
theorem faithful_addressObservation_eq {externalParent ligand : Atom}
    {first second : RootedDigraph Atom}
    (hfirst : FaithfulExactExpansion molecule externalParent ligand first)
    (hsecond : FaithfulExactExpansion molecule externalParent ligand second)
    {firstAddressing : first.Addressing} {secondAddressing : second.Addressing}
    (hfirstCanonical : CanonicalAddressing molecule firstAddressing)
    (hsecondCanonical : CanonicalAddressing molecule secondAddressing)
    (rule : ConstitutionalRule) (position : List ℕ) :
    addressObservation molecule firstAddressing rule position =
      addressObservation molecule secondAddressing rule position := by
  let W := max first.width second.width
  let D := max first.height second.height
  have hW₁ : first.width ≤ W := le_max_left _ _
  have hW₂ : second.width ≤ W := le_max_right _ _
  have hD₁ : first.height ≤ D := le_max_left _ _
  have hD₂ : second.height ≤ D := le_max_right _ _
  obtain ⟨hdense₁, hsorted₁⟩ :=
    (canonicalAddressing_iff_of_bounds molecule first hW₁ hD₁ firstAddressing).1 hfirstCanonical
  obtain ⟨hdense₂, hsorted₂⟩ :=
    (canonicalAddressing_iff_of_bounds molecule second hW₂ hD₂ secondAddressing).1
      hsecondCanonical
  by_cases hin : (∀ slot ∈ position, slot < W) ∧ position.length ≤ D
  · have h₁ := addressObservation_eq_keyObservation molecule W D hdense₁ hsorted₁ rule position
      first.root hin.1 hin.2
    have h₂ := addressObservation_eq_keyObservation molecule W D hdense₂ hsorted₂ rule position
      second.root hin.1 hin.2
    rw [firstAddressing.root_address, List.nil_append] at h₁
    rw [secondAddressing.root_address, List.nil_append] at h₂
    rw [← h₁, ← h₂, faithful_root_ruleKey_eq hfirst hsecond W D]
  · have hout : ∀ {graph : RootedDigraph Atom} (addressing : graph.Addressing),
        Dense addressing → graph.width ≤ W → graph.height ≤ D →
          ∀ node, addressing.address node ≠ position := by
      intro graph addressing hdense hW hD node hnode
      exact hin ⟨fun slot hslot => lt_of_lt_of_le
          (address_slots_lt_width hdense node slot (hnode ▸ hslot)) hW,
        hnode ▸ le_trans (address_length_le_height addressing node) hD⟩
    rw [addressObservation_of_unoccupied molecule firstAddressing rule
        (hout firstAddressing hdense₁ hW₁ hD₁),
      addressObservation_of_unoccupied molecule secondAddressing rule
        (hout secondAddressing hdense₂ hW₂ hD₂)]

/-- Equal observations at an address give equal constitutional rule values, across graphs. -/
theorem ruleValue_eq_of_addressObservation_eq_of_graphs {first second : RootedDigraph Atom}
    {firstAddressing : first.Addressing} {secondAddressing : second.Addressing}
    (rule : ConstitutionalRule) (position : List ℕ)
    (h : addressObservation molecule firstAddressing rule position =
      addressObservation molecule secondAddressing rule position) :
    ruleValue molecule rule position (addressLabel firstAddressing position) =
      ruleValue molecule rule position (addressLabel secondAddressing position) := by
  unfold addressObservation at h
  unfold addressLabel
  by_cases h₁ : ∃ node, firstAddressing.address node = position <;>
    by_cases h₂ : ∃ node, secondAddressing.address node = position
  · rw [dif_pos h₁, dif_pos h₂] at h ⊢
    have hobs := priorityValue_injective rule (WithBot.coe_injective h)
    have hlen₁ : (List.replicate (first.depth (Classical.choose h₁)) 0).length =
        position.length := by
      rw [List.length_replicate, ← firstAddressing.address_length_eq_depth,
        Classical.choose_spec h₁]
    have hlen₂ : (List.replicate (second.depth (Classical.choose h₂)) 0).length =
        position.length := by
      rw [List.length_replicate, ← secondAddressing.address_length_eq_depth,
        Classical.choose_spec h₂]
    rw [← ruleValue_eq_of_length_eq molecule rule hlen₁,
      ← ruleValue_eq_of_length_eq molecule rule hlen₂]
    exact hobs
  · rw [dif_pos h₁, dif_neg h₂] at h
    exact (WithBot.coe_ne_bot h).elim
  · rw [dif_neg h₁, dif_pos h₂] at h
    exact (WithBot.coe_ne_bot h.symm).elim
  · rw [dif_neg h₁, dif_neg h₂]

/-- Constitutional hierarchy outcomes under canonical addressings depend only on the ligands, not
on the faithful expansions chosen for them. -/
theorem faithful_hierarchyOutcome_iff {externalParent leftLigand rightLigand : Atom}
    {left left' right right' : RootedDigraph Atom}
    (hleft : FaithfulExactExpansion molecule externalParent leftLigand left)
    (hleft' : FaithfulExactExpansion molecule externalParent leftLigand left')
    (hright : FaithfulExactExpansion molecule externalParent rightLigand right)
    (hright' : FaithfulExactExpansion molecule externalParent rightLigand right')
    {leftAddressing : left.Addressing} {leftAddressing' : left'.Addressing}
    {rightAddressing : right.Addressing} {rightAddressing' : right'.Addressing}
    (hlc : CanonicalAddressing molecule leftAddressing)
    (hlc' : CanonicalAddressing molecule leftAddressing')
    (hrc : CanonicalAddressing molecule rightAddressing)
    (hrc' : CanonicalAddressing molecule rightAddressing')
    (rule : ConstitutionalRule) (outcome : Ordering) :
    ConstitutionalHierarchyOutcome molecule rule left leftAddressing right rightAddressing
        outcome ↔
      ConstitutionalHierarchyOutcome molecule rule left' leftAddressing' right' rightAddressing'
        outcome := by
  apply FirstDifferenceOutcome.congr
  intro position outcome
  rw [constitutionalOutcomeAt_iff, constitutionalOutcomeAt_iff,
    ruleValue_eq_of_addressObservation_eq_of_graphs rule position
      (faithful_addressObservation_eq hleft hleft' hlc hlc' rule position),
    ruleValue_eq_of_addressObservation_eq_of_graphs rule position
      (faithful_addressObservation_eq hright hright' hrc hrc' rule position)]

end Outcomes

/-! ## Total constitutional rule outcomes -/

namespace ConstitutionalProblemData

variable {Unit : Type u}

/-- Canonical outcomes agree for every choice of faithful expansions of the two ligands. -/
theorem withCanonicalAddressing_canonicalOutcome_iff (data : ConstitutionalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (rule : ConstitutionalRule)
    {leftLigand rightLigand : Atom} {left left' right right' : RootedDigraph Atom}
    (hleft : FaithfulExactExpansion data.molecule (data.centerAtom unit) leftLigand left)
    (hleft' : FaithfulExactExpansion data.molecule (data.centerAtom unit) leftLigand left')
    (hright : FaithfulExactExpansion data.molecule (data.centerAtom unit) rightLigand right)
    (hright' : FaithfulExactExpansion data.molecule (data.centerAtom unit) rightLigand right')
    (outcome : Ordering) :
    data.withCanonicalAddressing.CanonicalOutcome descriptorMap unit rule left right outcome ↔
      data.withCanonicalAddressing.CanonicalOutcome descriptorMap unit rule left' right'
        outcome := by
  have hexists : ∀ {ligand : Atom} {graph : RootedDigraph Atom},
      FaithfulExactExpansion data.molecule (data.centerAtom unit) ligand graph →
        ∃ addressing : graph.Addressing, CanonicalAddressing data.molecule addressing := by
    intro ligand graph hgraph
    obtain ⟨_, base, _⟩ := hgraph.1
    exact exists_canonicalAddressing data.molecule base
  constructor
  · rintro ⟨⟨la, hla⟩, ⟨ra, hra⟩, hall⟩
    refine ⟨hexists hleft', hexists hright', fun la' ra' hla' hra' => ?_⟩
    exact (faithful_hierarchyOutcome_iff hleft hleft' hright hright' hla hla' hra hra' rule
      outcome).1 (hall la ra hla hra)
  · rintro ⟨⟨la', hla'⟩, ⟨ra', hra'⟩, hall⟩
    refine ⟨hexists hleft, hexists hright, fun la ra hla hra => ?_⟩
    exact (faithful_hierarchyOutcome_iff hleft' hleft hright' hright hla' hla hra' hra rule
      outcome).1 (hall la' ra' hla' hra')

end ConstitutionalProblemData

end
end DeclarativeCIP
end OneCenter
end TetraStereo
