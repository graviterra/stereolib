import TetraStereo.OneCenter.DeclarativeCIPConstitutional
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Local child histograms for faithful CIP expansions

Faithful exact expansions are unordered finite rooted trees.  To prove that an actual canonical
production hierarchy represents every independently faithful expansion, the global construction
first needs a local fact at each matched real node: the two nodes expose the same atom/provenance-
category child counts.  This module proves that histogram theorem once.

Category histograms deliberately do not identify duplicate-distance payloads and therefore are not
yet a labelled bisimulation.  The stronger invariant below records the depth-aligned history needed
by the next theorem, which must refine the histograms to exact labels before constructing a rooted
labelled isomorphism.  No production function or IUPAC provision is mentioned here.
-/

namespace TetraStereo.OneCenter.DeclarativeCIP
namespace RootedDigraph

universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

/-- One real ancestor carrying `atom` at an exact hierarchy depth.  Duplicate-distance payloads
are determined by this depth, not merely by unindexed ancestor membership. -/
def AncestorAtomAtDepth (graph : RootedDigraph Atom) (node : graph.Node)
    (atom : Atom) (depth : Nat) : Prop :=
  ∃ ancestor,
    Relation.TransGen graph.child ancestor node ∧
      (graph.label ancestor).atom? = some atom ∧
      graph.depth ancestor = depth

omit [Fintype Atom] [DecidableEq Atom] in
/-- Every parent-preserving semantic address has length equal to the graph's intrinsic depth.
Sibling slot names may vary, but no addressing can change a duplicate-distance sphere. -/
theorem Addressing.address_length_eq_depth
    {graph : RootedDigraph Atom} (addressing : graph.Addressing) (node : graph.Node) :
    (addressing.address node).length = graph.depth node := by
  have reachable := graph.reachable node
  induction reachable with
  | refl =>
      simp [addressing.root_address, graph.root_depth]
  | @tail parent child _path hedge inductionHypothesis =>
      rcases (addressing.child_iff parent child).1 hedge with ⟨slot, childAddress⟩
      rw [childAddress, graph.child_depth hedge]
      simp [inductionHypothesis]

omit [Fintype Atom] [DecidableEq Atom] in
/-- In an addressed hierarchy, strict ancestors of one node lie on the same branch. -/
theorem Addressing.strictAncestors_comparable
    {graph : RootedDigraph Atom} (addressing : graph.Addressing)
    {first second node : graph.Node}
    (firstPath : Relation.TransGen graph.child first node)
    (secondPath : Relation.TransGen graph.child second node) :
    first = second ∨
      Relation.TransGen graph.child first second ∨
      Relation.TransGen graph.child second first := by
  induction firstPath generalizing second with
  | single firstEdge =>
      obtain ⟨secondParent, secondPrefix, secondEdge⟩ :=
        Relation.TransGen.tail'_iff.mp secondPath
      have parentEq : secondParent = first := addressing.parent_unique secondEdge firstEdge
      subst secondParent
      cases secondPrefix with
      | refl => exact Or.inl rfl
      | tail prefixPath pathEdge =>
          exact Or.inr (Or.inr (Relation.TransGen.tail' prefixPath pathEdge))
  | @tail parent node firstPrefix firstEdge inductionHypothesis =>
      obtain ⟨secondParent, secondPrefix, secondEdge⟩ :=
        Relation.TransGen.tail'_iff.mp secondPath
      have parentEq : secondParent = parent := addressing.parent_unique secondEdge firstEdge
      subst secondParent
      cases secondPrefix with
      | refl => exact Or.inr (Or.inl firstPrefix)
      | tail prefixPath pathEdge =>
          exact inductionHypothesis (Relation.TransGen.tail' prefixPath pathEdge)

omit [Fintype Atom] [DecidableEq Atom] in
/-- The semantic parent atom of an immediate child is exactly the atom carried by its unique
addressed parent. -/
theorem Addressing.parentAtom_child_iff
    {graph : RootedDigraph Atom} (addressing : graph.Addressing)
    {parent child : graph.Node} (edge : graph.child parent child)
    {parentAtom atom : Atom}
    (parentAtomEq : (graph.label parent).atom? = some parentAtom) :
    ParentAtom graph child atom ↔ atom = parentAtom := by
  constructor
  · rintro ⟨otherParent, otherEdge, otherAtom⟩
    have parentEq : otherParent = parent := addressing.parent_unique otherEdge edge
    subst otherParent
    exact Option.some.inj (otherAtom.symm.trans parentAtomEq)
  · intro atomEq
    exact ⟨parent, edge, by simpa [atomEq] using parentAtomEq⟩

omit [Fintype Atom] [DecidableEq Atom] in
/-- Strict ancestors of an immediate child are its unique parent followed by that parent's strict
ancestors. -/
theorem Addressing.ancestorAtom_child_iff
    {graph : RootedDigraph Atom} (addressing : graph.Addressing)
    {parent child : graph.Node} (edge : graph.child parent child) (atom : Atom) :
    AncestorAtom graph child atom ↔
      (graph.label parent).atom? = some atom ∨ AncestorAtom graph parent atom := by
  constructor
  · rintro ⟨ancestor, ancestorPath, ancestorAtom⟩
    obtain ⟨lastParent, ancestorPrefix, lastEdge⟩ :=
      Relation.TransGen.tail'_iff.mp ancestorPath
    have parentEq : lastParent = parent := addressing.parent_unique lastEdge edge
    subst lastParent
    cases ancestorPrefix with
    | refl => exact Or.inl ancestorAtom
    | tail path pathEdge =>
        exact Or.inr ⟨ancestor, Relation.TransGen.tail' path pathEdge, ancestorAtom⟩
  · rintro (parentAtom | ⟨ancestor, ancestorPath, ancestorAtom⟩)
    · exact ⟨parent, Relation.TransGen.single edge, parentAtom⟩
    · exact ⟨ancestor, ancestorPath.tail edge, ancestorAtom⟩

omit [Fintype Atom] [DecidableEq Atom] in
/-- Depth-indexed strict ancestors of an immediate child split into its parent at the parent's
depth and the already-indexed strict ancestors of that parent. -/
theorem Addressing.ancestorAtomAtDepth_child_iff
    {graph : RootedDigraph Atom} (addressing : graph.Addressing)
    {parent child : graph.Node} (edge : graph.child parent child)
    (atom : Atom) (depth : Nat) :
    AncestorAtomAtDepth graph child atom depth ↔
      ((graph.label parent).atom? = some atom ∧ graph.depth parent = depth) ∨
        AncestorAtomAtDepth graph parent atom depth := by
  constructor
  · rintro ⟨ancestor, ancestorPath, ancestorAtom, ancestorDepth⟩
    obtain ⟨lastParent, ancestorPrefix, lastEdge⟩ :=
      Relation.TransGen.tail'_iff.mp ancestorPath
    have parentEq : lastParent = parent := addressing.parent_unique lastEdge edge
    subst lastParent
    cases ancestorPrefix with
    | refl => exact Or.inl ⟨ancestorAtom, ancestorDepth⟩
    | tail path pathEdge =>
        exact Or.inr ⟨ancestor, Relation.TransGen.tail' path pathEdge, ancestorAtom,
          ancestorDepth⟩
  · rintro (⟨parentAtom, parentDepth⟩ | ⟨ancestor, ancestorPath, ancestorAtom,
      ancestorDepth⟩)
    · exact ⟨parent, Relation.TransGen.single edge, parentAtom, parentDepth⟩
    · exact ⟨ancestor, ancestorPath.tail edge, ancestorAtom, ancestorDepth⟩

omit [Fintype Atom] [DecidableEq Atom] in
theorem Addressing.not_parentAtom_root
    {graph : RootedDigraph Atom} (addressing : graph.Addressing) (atom : Atom) :
    ¬ ParentAtom graph graph.root atom := by
  rintro ⟨parent, edge, _parentAtom⟩
  exact addressing.not_child_root parent edge

omit [Fintype Atom] [DecidableEq Atom] in
theorem Addressing.not_ancestorAtom_root
    {graph : RootedDigraph Atom} (addressing : graph.Addressing) (atom : Atom) :
    ¬ AncestorAtom graph graph.root atom := by
  rintro ⟨ancestor, ancestorPath, _ancestorAtom⟩
  obtain ⟨lastParent, _prefix, lastEdge⟩ := Relation.TransGen.tail'_iff.mp ancestorPath
  exact addressing.not_child_root lastParent lastEdge

omit [Fintype Atom] [DecidableEq Atom] in
theorem Addressing.not_ancestorAtomAtDepth_root
    {graph : RootedDigraph Atom} (addressing : graph.Addressing)
    (atom : Atom) (depth : Nat) :
    ¬ AncestorAtomAtDepth graph graph.root atom depth := by
  rintro ⟨ancestor, ancestorPath, _ancestorAtom, _ancestorDepth⟩
  obtain ⟨lastParent, _prefix, lastEdge⟩ := Relation.TransGen.tail'_iff.mp ancestorPath
  exact addressing.not_child_root lastParent lastEdge

omit [Fintype Atom] [DecidableEq Atom] in
/-- Reachability and positive child-depth steps make the root the unique depth-zero node. -/
theorem eq_root_of_depth_eq_zero
    (graph : RootedDigraph Atom) (node : graph.Node) (depthZero : graph.depth node = 0) :
    node = graph.root := by
  have reachable := graph.reachable node
  cases reachable with
  | refl => rfl
  | @tail parent child _path edge =>
      rw [graph.child_depth edge] at depthZero
      simp at depthZero

/-- The unique addressed parent of a non-root node. -/
noncomputable def Addressing.parentOfNonroot
    {graph : RootedDigraph Atom} (addressing : graph.Addressing)
    (node : graph.Node) (nodeNeRoot : node ≠ graph.root) : graph.Node :=
  Classical.choose (addressing.existsUnique_parent node nodeNeRoot)

omit [Fintype Atom] [DecidableEq Atom] in
theorem Addressing.parentOfNonroot_child
    {graph : RootedDigraph Atom} (addressing : graph.Addressing)
    (node : graph.Node) (nodeNeRoot : node ≠ graph.root) :
    graph.child (addressing.parentOfNonroot node nodeNeRoot) node :=
  (Classical.choose_spec (addressing.existsUnique_parent node nodeNeRoot)).1

/-- Two real parents in faithful expansions have the same semantic branch history.  Equality of
the parent atom fixes molecular bond multiplicities; the two iff fields retain exactly the
history-sensitive inputs used by ring closure and parent suppression. -/
structure FaithfulParentAgreement
    (left right : RootedDigraph Atom) (externalParent : Atom)
    (leftParent : left.Node) (rightParent : right.Node) : Type u where
  parentAtom : Atom
  left_atom : (left.label leftParent).atom? = some parentAtom
  right_atom : (right.label rightParent).atom? = some parentAtom
  left_real : ProvenanceRealAtom (left.label leftParent).provenance
  right_real : ProvenanceRealAtom (right.label rightParent).provenance
  suppressed_iff : ∀ atom,
    SuppressedParentAtom left externalParent atom leftParent ↔
      SuppressedParentAtom right externalParent atom rightParent
  ancestor_iff : ∀ atom,
    BranchAncestorAtom left externalParent atom leftParent ↔
      BranchAncestorAtom right externalParent atom rightParent

/-- The exact source-facing distance alternatives for one ring duplicate: zero for the external
stereocenter, or one plus the intrinsic depth of the represented strict ancestor. -/
def RingDuplicateDistanceAt (graph : RootedDigraph Atom) (externalParent : Atom)
    (node : graph.Node) (atom : Atom) (distance : Nat) : Prop :=
  (atom = externalParent ∧ distance = 0) ∨
    ∃ ancestor,
      Relation.TransGen graph.child ancestor node ∧
        (graph.label ancestor).atom? = some atom ∧
        distance = graph.depth ancestor + 1

omit [Fintype Atom] [DecidableEq Atom] in
/-- Once the external stereocenter is excluded from represented ancestors and one molecular atom
cannot occur at two ancestor depths, a ring-duplicate atom has at most one legal distance label. -/
theorem RingDuplicateDistanceAt.unique
    (graph : RootedDigraph Atom) (externalParent : Atom) (node : graph.Node)
    (externalParentAbsent : ¬ AncestorAtom graph node externalParent)
    (ancestorDepthUnique : ∀ atom first second,
      AncestorAtomAtDepth graph node atom first →
        AncestorAtomAtDepth graph node atom second → first = second)
    (atom : Atom) {first second : Nat}
    (firstAt : RingDuplicateDistanceAt graph externalParent node atom first)
    (secondAt : RingDuplicateDistanceAt graph externalParent node atom second) :
    first = second := by
  rcases firstAt with firstExternal | firstRepresented
  · rcases secondAt with secondExternal | secondRepresented
    · exact firstExternal.2.trans secondExternal.2.symm
    · obtain ⟨ancestor, ancestorPath, ancestorAtom, _distance⟩ := secondRepresented
      exfalso
      apply externalParentAbsent
      exact ⟨ancestor, ancestorPath, by simpa [firstExternal.1] using ancestorAtom⟩
  · rcases secondAt with secondExternal | secondRepresented
    · obtain ⟨ancestor, ancestorPath, ancestorAtom, _distance⟩ := firstRepresented
      exfalso
      apply externalParentAbsent
      exact ⟨ancestor, ancestorPath, by simpa [secondExternal.1] using ancestorAtom⟩
    · obtain ⟨firstAncestor, firstPath, firstAtom, firstDistance⟩ := firstRepresented
      obtain ⟨secondAncestor, secondPath, secondAtom, secondDistance⟩ := secondRepresented
      have depthEq := ancestorDepthUnique atom (graph.depth firstAncestor)
        (graph.depth secondAncestor)
        ⟨firstAncestor, firstPath, firstAtom, rfl⟩
        ⟨secondAncestor, secondPath, secondAtom, rfl⟩
      exact firstDistance.trans ((congrArg (fun depth => depth + 1) depthEq).trans
        secondDistance.symm)

/-- Address-free duplicate-distance correctness.  This is the intrinsic labelled condition needed
by representation comparison: multiple-bond duplicates use their parent's graph depth, while ring
duplicates use either the external stereocenter or the depth of a represented strict ancestor. -/
def IntrinsicDuplicateDistancesCorrect (graph : RootedDigraph Atom) (externalParent : Atom) :
    Prop :=
  ∀ parent child, graph.child parent child →
    match graph.label child with
    | ⟨_, NodeProvenance.multipleBondDuplicate distance⟩ =>
        distance = graph.depth parent + 1
    | ⟨some atom, NodeProvenance.ringDuplicate distance⟩ =>
        RingDuplicateDistanceAt graph externalParent parent atom distance
    | ⟨none, NodeProvenance.ringDuplicate _⟩ => False
    | _ => True

omit [Fintype Atom] [DecidableEq Atom] in
/-- Semantic sibling-slot names are immaterial: address-based distance correctness is equivalent
to the intrinsic depth-and-ancestry condition for every parent-preserving addressing. -/
theorem duplicateDistancesCorrect_iff_intrinsic
    (graph : RootedDigraph Atom) (externalParent : Atom) (addressing : graph.Addressing) :
    DuplicateDistancesCorrect graph externalParent addressing ↔
      IntrinsicDuplicateDistancesCorrect graph externalParent := by
  unfold DuplicateDistancesCorrect IntrinsicDuplicateDistancesCorrect
  constructor
  · intro correct parent child edge
    have localCorrect := correct parent child edge
    cases labelEq : graph.label child with
    | mk atom? provenance =>
        cases provenance with
        | realAtom | phantom | lonePair | auxiliary => trivial
        | multipleBondDuplicate distance =>
            simp [labelEq] at localCorrect ⊢
            exact localCorrect.trans (congrArg (fun depth => depth + 1)
              (addressing.address_length_eq_depth parent))
        | ringDuplicate distance =>
            cases atom? with
            | none => simp [labelEq] at localCorrect
            | some atom =>
                simp [labelEq, RingDuplicateDistanceAt] at localCorrect ⊢
                rcases localCorrect with external | represented
                · exact Or.inl external
                · obtain ⟨ancestor, ancestorPath, ancestorAtom, ancestorDistance⟩ := represented
                  exact Or.inr ⟨ancestor, ancestorPath, ancestorAtom,
                    ancestorDistance.trans (congrArg (fun depth => depth + 1)
                      (addressing.address_length_eq_depth ancestor))⟩
  · intro correct parent child edge
    have localCorrect := correct parent child edge
    cases labelEq : graph.label child with
    | mk atom? provenance =>
        cases provenance with
        | realAtom | phantom | lonePair | auxiliary => trivial
        | multipleBondDuplicate distance =>
            simp [labelEq] at localCorrect ⊢
            exact localCorrect.trans (congrArg (fun depth => depth + 1)
              (addressing.address_length_eq_depth parent).symm)
        | ringDuplicate distance =>
            cases atom? with
            | none => simp [labelEq] at localCorrect
            | some atom =>
                simp [labelEq, RingDuplicateDistanceAt] at localCorrect ⊢
                rcases localCorrect with external | represented
                · exact Or.inl external
                · obtain ⟨ancestor, ancestorPath, ancestorAtom, ancestorDistance⟩ := represented
                  exact Or.inr ⟨ancestor, ancestorPath, ancestorAtom,
                    ancestorDistance.trans (congrArg (fun depth => depth + 1)
                      (addressing.address_length_eq_depth ancestor).symm)⟩

/-- The quantified addressing clause in `FaithfulExactExpansion` has an exact address-free form.
This is the constitutional boundary consumed by later labelled-isomorphism construction. -/
theorem faithfulExactExpansion_iff_intrinsic
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (graph : RootedDigraph Atom) :
    FaithfulExactExpansion molecule externalParent ligand graph ↔
      ExactExpansion molecule externalParent ligand graph ∧
        molecule.Adj externalParent ligand ∧
        AtomBearingChildren graph ∧
        IntrinsicDuplicateDistancesCorrect graph externalParent := by
  constructor
  · intro faithful
    rcases faithful.1.2 with ⟨addressing, _multiplicities⟩
    exact ⟨faithful.1, faithful.2.1, faithful.2.2.1,
      (duplicateDistancesCorrect_iff_intrinsic graph externalParent addressing).1
        (faithful.2.2.2 addressing)⟩
  · rintro ⟨exactExpansion, rootBond, atomBearing, intrinsicDistances⟩
    refine ⟨exactExpansion, rootBond, atomBearing, ?_⟩
    intro addressing
    exact (duplicateDistancesCorrect_iff_intrinsic graph externalParent addressing).2
      intrinsicDistances

/-- A node with an outgoing hierarchy edge is real: every non-real provenance is terminal. -/
theorem FaithfulExactExpansion.real_of_hasChild
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (graph : RootedDigraph Atom)
    (faithful : FaithfulExactExpansion molecule externalParent ligand graph)
    (node child : graph.Node) (edge : graph.child node child) :
    ProvenanceRealAtom (graph.label node).provenance := by
  have notTerminal : ¬ ProvenanceTerminal (graph.label node).provenance := by
    intro terminal
    exact faithful.1.1.2.2.1 node terminal child edge
  cases provenanceEq : (graph.label node).provenance <;>
    simp [provenanceEq, ProvenanceTerminal, ProvenanceRealAtom] at notTerminal ⊢

/-- Local label compatibility supplies the atom carried by every real hierarchy node. -/
theorem FaithfulExactExpansion.atom_exists_of_real
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (graph : RootedDigraph Atom)
    (faithful : FaithfulExactExpansion molecule externalParent ligand graph)
    (node : graph.Node)
    (real : ProvenanceRealAtom (graph.label node).provenance) :
    ∃ atom, (graph.label node).atom? = some atom := by
  have compatible := faithful.1.1.2.1 node
  cases provenanceEq : (graph.label node).provenance <;>
    simp [provenanceEq, ProvenanceRealAtom] at real
  simpa [LabelCompatible, provenanceEq] using compatible

/-- Every represented real child satisfies the exact positive branch of the real-child
multiplicity equation. -/
theorem FaithfulExactExpansion.realChild_condition
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (graph : RootedDigraph Atom)
    (faithful : FaithfulExactExpansion molecule externalParent ligand graph)
    (parent child : graph.Node) (edge : graph.child parent child)
    (parentAtom childAtom : Atom)
    (parentAtomEq : (graph.label parent).atom? = some parentAtom)
    (parentReal : ProvenanceRealAtom (graph.label parent).provenance)
    (childAtomEq : (graph.label child).atom? = some childAtom)
    (childReal : ProvenanceRealAtom (graph.label child).provenance) :
    molecule.Adj parentAtom childAtom ∧
      ¬ BranchAncestorAtom graph externalParent childAtom parent := by
  rcases faithful.1.2 with ⟨_addressing, multiplicities⟩
  have counts := multiplicities parent parentAtom parentAtomEq parentReal childAtom
  have positive : 0 < ChildAtomProvenanceCount graph parent childAtom ProvenanceRealAtom := by
    letI : Fintype graph.Node := graph.nodeFintype
    unfold ChildAtomProvenanceCount ChildCountWhere
    refine Nat.card_pos_iff.mpr ⟨?_, inferInstance⟩
    exact ⟨⟨child, edge, childAtomEq, childReal⟩⟩
  rw [counts.2.2.2] at positive
  by_cases condition : molecule.Adj parentAtom childAtom ∧
      ¬ BranchAncestorAtom graph externalParent childAtom parent
  · exact condition
  · simp [condition] at positive

/-- A real child is neither the external stereocenter nor a repetition of any atom already on its
strict ancestor chain. -/
theorem FaithfulExactExpansion.realChild_atom_fresh
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (graph : RootedDigraph Atom)
    (faithful : FaithfulExactExpansion molecule externalParent ligand graph)
    (parent child : graph.Node) (edge : graph.child parent child)
    (childAtom : Atom)
    (childAtomEq : (graph.label child).atom? = some childAtom)
    (childReal : ProvenanceRealAtom (graph.label child).provenance) :
    childAtom ≠ externalParent ∧ ¬ AncestorAtom graph child childAtom := by
  have parentReal := faithful.real_of_hasChild molecule externalParent ligand graph
    parent child edge
  obtain ⟨parentAtom, parentAtomEq⟩ :=
    faithful.atom_exists_of_real molecule externalParent ligand graph parent parentReal
  have condition := faithful.realChild_condition molecule externalParent ligand graph
    parent child edge parentAtom childAtom parentAtomEq parentReal childAtomEq childReal
  rcases faithful.1.2 with ⟨addressing, _multiplicities⟩
  constructor
  · intro childExternal
    exact condition.2 (Or.inl childExternal)
  · rintro ⟨ancestor, ancestorPath, ancestorAtom⟩
    obtain ⟨lastParent, ancestorPrefix, lastEdge⟩ :=
      Relation.TransGen.tail'_iff.mp ancestorPath
    have lastParentEq : lastParent = parent := addressing.parent_unique lastEdge edge
    subst lastParent
    cases ancestorPrefix with
    | refl =>
        have sameAtom : parentAtom = childAtom :=
          Option.some.inj (parentAtomEq.symm.trans ancestorAtom)
        subst childAtom
        simpa [MoleculeGraph.Adj, molecule.bond_self] using condition.1
    | tail ancestorPrefixPath ancestorPrefixEdge =>
        apply condition.2
        exact Or.inr ⟨ancestor,
          Relation.TransGen.tail' ancestorPrefixPath ancestorPrefixEdge, ancestorAtom⟩

/-- No faithful ligand hierarchy can represent its external stereocenter as a strict ancestor. -/
theorem FaithfulExactExpansion.externalParent_not_ancestor
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (graph : RootedDigraph Atom)
    (faithful : FaithfulExactExpansion molecule externalParent ligand graph)
    (node : graph.Node) :
    ¬ AncestorAtom graph node externalParent := by
  rintro ⟨ancestor, ancestorPath, ancestorAtom⟩
  obtain ⟨next, firstEdge, _remainingPath⟩ := Relation.TransGen.head'_iff.mp ancestorPath
  have ancestorReal := faithful.real_of_hasChild molecule externalParent ligand graph
    ancestor next firstEdge
  by_cases ancestorRoot : ancestor = graph.root
  · subst ancestor
    have ligandEq : ligand = externalParent := by
      simpa [faithful.1.1.1] using ancestorAtom
    simpa [ligandEq, MoleculeGraph.Adj, molecule.bond_self] using faithful.2.1
  · rcases faithful.1.2 with ⟨addressing, _multiplicities⟩
    obtain ⟨parent, parentEdge, _parentUnique⟩ :=
      addressing.existsUnique_parent ancestor ancestorRoot
    exact (faithful.realChild_atom_fresh molecule externalParent ligand graph parent ancestor
      parentEdge externalParent ancestorAtom ancestorReal).1 rfl

/-- In a faithful exact expansion, one molecular atom cannot occur at two depths on the strict
ancestor chain of a node. -/
theorem FaithfulExactExpansion.ancestorAtomAtDepth_unique
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (graph : RootedDigraph Atom)
    (faithful : FaithfulExactExpansion molecule externalParent ligand graph)
    (node : graph.Node) (atom : Atom) (first second : Nat)
    (firstAt : AncestorAtomAtDepth graph node atom first)
    (secondAt : AncestorAtomAtDepth graph node atom second) :
    first = second := by
  obtain ⟨firstAncestor, firstPath, firstAtom, firstDepth⟩ := firstAt
  obtain ⟨secondAncestor, secondPath, secondAtom, secondDepth⟩ := secondAt
  rcases faithful.1.2 with ⟨addressing, _multiplicities⟩
  rcases addressing.strictAncestors_comparable firstPath secondPath with
    same | firstBeforeSecond | secondBeforeFirst
  · subst secondAncestor
    exact firstDepth.symm.trans secondDepth
  · obtain ⟨next, secondEdge, _remainingPath⟩ :=
      Relation.TransGen.head'_iff.mp secondPath
    have secondReal := faithful.real_of_hasChild molecule externalParent ligand graph
      secondAncestor next secondEdge
    obtain ⟨parent, parentPrefix, parentEdge⟩ :=
      Relation.TransGen.tail'_iff.mp firstBeforeSecond
    have fresh := faithful.realChild_atom_fresh molecule externalParent ligand graph
      parent secondAncestor parentEdge atom secondAtom secondReal
    exact (fresh.2 ⟨firstAncestor, firstBeforeSecond, firstAtom⟩).elim
  · obtain ⟨next, firstEdge, _remainingPath⟩ :=
      Relation.TransGen.head'_iff.mp firstPath
    have firstReal := faithful.real_of_hasChild molecule externalParent ligand graph
      firstAncestor next firstEdge
    obtain ⟨parent, parentPrefix, parentEdge⟩ :=
      Relation.TransGen.tail'_iff.mp secondBeforeFirst
    have fresh := faithful.realChild_atom_fresh molecule externalParent ligand graph
      parent firstAncestor parentEdge atom firstAtom firstReal
    exact (fresh.2 ⟨secondAncestor, secondBeforeFirst, secondAtom⟩).elim

/-- Faithful multiple-bond duplicate payloads are fixed by intrinsic parent depth. -/
theorem FaithfulExactExpansion.multipleBondDuplicate_distance_eq_depth
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (graph : RootedDigraph Atom)
    (faithful : FaithfulExactExpansion molecule externalParent ligand graph)
    (parent child : graph.Node) (edge : graph.child parent child)
    (atom? : Option Atom) (distance : Nat)
    (labelEq : graph.label child =
      ⟨atom?, NodeProvenance.multipleBondDuplicate distance⟩) :
    distance = graph.depth parent + 1 := by
  rcases faithful.1.2 with ⟨addressing, _multiplicities⟩
  have correct := faithful.2.2.2 addressing parent child edge
  have addressed : distance = (addressing.address parent).length + 1 := by
    simpa [labelEq] using correct
  exact addressed.trans (congrArg (fun depth => depth + 1)
    (addressing.address_length_eq_depth parent))

/-- Faithful ring-duplicate payloads are exactly zero or a represented ancestor's intrinsic
depth plus one.  This removes arbitrary sibling addressing from the labelled matching boundary. -/
theorem FaithfulExactExpansion.ringDuplicate_distance_at
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (graph : RootedDigraph Atom)
    (faithful : FaithfulExactExpansion molecule externalParent ligand graph)
    (parent child : graph.Node) (edge : graph.child parent child)
    (atom : Atom) (distance : Nat)
    (labelEq : graph.label child = ⟨some atom, NodeProvenance.ringDuplicate distance⟩) :
    RingDuplicateDistanceAt graph externalParent parent atom distance := by
  rcases faithful.1.2 with ⟨addressing, _multiplicities⟩
  have correct := faithful.2.2.2 addressing parent child edge
  have addressed :
      (atom = externalParent ∧ distance = 0) ∨
        ∃ ancestor,
          Relation.TransGen graph.child ancestor parent ∧
            (graph.label ancestor).atom? = some atom ∧
            distance = (addressing.address ancestor).length + 1 := by
    simpa [labelEq] using correct
  rcases addressed with external | represented
  · exact Or.inl external
  · obtain ⟨ancestor, ancestorPath, ancestorAtom, ancestorDistance⟩ := represented
    exact Or.inr ⟨ancestor, ancestorPath, ancestorAtom,
      ancestorDistance.trans (congrArg (fun depth => depth + 1)
        (addressing.address_length_eq_depth ancestor))⟩

/-- The stronger induction invariant required for exact labelled matching.  Parent depth fixes
multiple-bond duplicate distances.  Depth-indexed ancestor agreement fixes the possible
ring-duplicate distances, while uniqueness prevents a repeated atom at two ancestor depths from
making the payload ambiguous. -/
structure FaithfulLabelledParentAgreement
    (left right : RootedDigraph Atom) (externalParent : Atom)
    (leftParent : left.Node) (rightParent : right.Node) : Type u
    extends FaithfulParentAgreement left right externalParent leftParent rightParent where
  parent_depth_eq : left.depth leftParent = right.depth rightParent
  left_externalParent_not_ancestor : ¬ AncestorAtom left leftParent externalParent
  right_externalParent_not_ancestor : ¬ AncestorAtom right rightParent externalParent
  ancestorAtDepth_iff : ∀ atom depth,
    AncestorAtomAtDepth left leftParent atom depth ↔
      AncestorAtomAtDepth right rightParent atom depth
  left_ancestor_depth_unique : ∀ atom first second,
    AncestorAtomAtDepth left leftParent atom first →
      AncestorAtomAtDepth left leftParent atom second → first = second
  right_ancestor_depth_unique : ∀ atom first second,
    AncestorAtomAtDepth right rightParent atom first →
      AncestorAtomAtDepth right rightParent atom second → first = second

/-- Faithfulness discharges every local freshness and ancestor-depth uniqueness field.  A caller
constructing a labelled correspondence need provide only the matched-parent semantics, equal
depth, and the depth-indexed ancestor correspondence maintained by its induction. -/
noncomputable def FaithfulLabelledParentAgreement.ofFaithful
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftParent : left.Node) (rightParent : right.Node)
    (parentAgreement : FaithfulParentAgreement left right externalParent
      leftParent rightParent)
    (parentDepthEq : left.depth leftParent = right.depth rightParent)
    (ancestorAtDepthIff : ∀ atom depth,
      AncestorAtomAtDepth left leftParent atom depth ↔
        AncestorAtomAtDepth right rightParent atom depth) :
    FaithfulLabelledParentAgreement left right externalParent leftParent rightParent where
  toFaithfulParentAgreement := parentAgreement
  parent_depth_eq := parentDepthEq
  left_externalParent_not_ancestor :=
    leftFaithful.externalParent_not_ancestor molecule externalParent ligand left leftParent
  right_externalParent_not_ancestor :=
    rightFaithful.externalParent_not_ancestor molecule externalParent ligand right rightParent
  ancestorAtDepth_iff := ancestorAtDepthIff
  left_ancestor_depth_unique := fun atom first second =>
    leftFaithful.ancestorAtomAtDepth_unique molecule externalParent ligand left leftParent atom
      first second
  right_ancestor_depth_unique := fun atom first second =>
    rightFaithful.ancestorAtomAtDepth_unique molecule externalParent ligand right rightParent atom
      first second

/-- The roots of any two faithful exact expansions of the same ligand satisfy the full labelled
parent agreement. -/
noncomputable def FaithfulLabelledParentAgreement.roots
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right) :
    FaithfulLabelledParentAgreement left right externalParent left.root right.root := by
  let leftAddressing : left.Addressing := Classical.choose leftFaithful.1.2
  let rightAddressing : right.Addressing := Classical.choose rightFaithful.1.2
  have leftRootAtom : (left.label left.root).atom? = some ligand := by
    simp [leftFaithful.1.1.1]
  have rightRootAtom : (right.label right.root).atom? = some ligand := by
    simp [rightFaithful.1.1.1]
  have leftRootReal : ProvenanceRealAtom (left.label left.root).provenance := by
    simp [leftFaithful.1.1.1, ProvenanceRealAtom]
  have rightRootReal : ProvenanceRealAtom (right.label right.root).provenance := by
    simp [rightFaithful.1.1.1, ProvenanceRealAtom]
  let rootParentAgreement : FaithfulParentAgreement left right externalParent
      left.root right.root :=
    { parentAtom := ligand
      left_atom := leftRootAtom
      right_atom := rightRootAtom
      left_real := leftRootReal
      right_real := rightRootReal
      suppressed_iff := by
        intro atom
        unfold SuppressedParentAtom
        simp [leftAddressing.not_parentAtom_root atom,
          rightAddressing.not_parentAtom_root atom]
      ancestor_iff := by
        intro atom
        unfold BranchAncestorAtom
        simp [leftAddressing.not_ancestorAtom_root atom,
          rightAddressing.not_ancestorAtom_root atom] }
  have rootDepthEq : left.depth left.root = right.depth right.root := by
    rw [left.root_depth, right.root_depth]
  have rootAncestorAtDepthIff : ∀ atom depth,
      AncestorAtomAtDepth left left.root atom depth ↔
        AncestorAtomAtDepth right right.root atom depth := by
    intro atom depth
    simp [leftAddressing.not_ancestorAtomAtDepth_root atom depth,
      rightAddressing.not_ancestorAtomAtDepth_root atom depth]
  exact FaithfulLabelledParentAgreement.ofFaithful molecule externalParent ligand left right
    leftFaithful rightFaithful left.root right.root rootParentAgreement rootDepthEq
      rootAncestorAtDepthIff

/-- A complete-label match between real children extends the full depth-aware parent agreement
from their parents to those children.  This is the recursive labelled-bisimulation step. -/
noncomputable def FaithfulLabelledParentAgreement.realChildren
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftParent : left.Node) (rightParent : right.Node)
    (agreement : FaithfulLabelledParentAgreement left right externalParent
      leftParent rightParent)
    (leftChild : left.Node) (rightChild : right.Node)
    (leftEdge : left.child leftParent leftChild)
    (rightEdge : right.child rightParent rightChild)
    (childLabelEq : left.label leftChild = right.label rightChild)
    (leftChildReal : ProvenanceRealAtom (left.label leftChild).provenance) :
    FaithfulLabelledParentAgreement left right externalParent leftChild rightChild := by
  let leftAddressing : left.Addressing := Classical.choose leftFaithful.1.2
  let rightAddressing : right.Addressing := Classical.choose rightFaithful.1.2
  have rightChildReal : ProvenanceRealAtom (right.label rightChild).provenance := by
    rw [← childLabelEq]
    exact leftChildReal
  let childAtom : Atom := Classical.choose
    (leftFaithful.atom_exists_of_real molecule externalParent ligand left leftChild leftChildReal)
  have leftChildAtom : (left.label leftChild).atom? = some childAtom :=
    Classical.choose_spec
      (leftFaithful.atom_exists_of_real molecule externalParent ligand left leftChild leftChildReal)
  have rightChildAtom : (right.label rightChild).atom? = some childAtom := by
    rw [← childLabelEq]
    exact leftChildAtom
  have leftChildNe : leftChild ≠ left.root := by
    intro childRoot
    subst leftChild
    exact leftAddressing.not_child_root leftParent leftEdge
  have rightChildNe : rightChild ≠ right.root := by
    intro childRoot
    subst rightChild
    exact rightAddressing.not_child_root rightParent rightEdge
  let childParentAgreement : FaithfulParentAgreement left right externalParent
      leftChild rightChild :=
    { parentAtom := childAtom
      left_atom := leftChildAtom
      right_atom := rightChildAtom
      left_real := leftChildReal
      right_real := rightChildReal
      suppressed_iff := by
        intro atom
        unfold SuppressedParentAtom
        rw [leftAddressing.parentAtom_child_iff leftEdge agreement.left_atom,
          rightAddressing.parentAtom_child_iff rightEdge agreement.right_atom]
        simp [leftChildNe, rightChildNe]
      ancestor_iff := by
        intro atom
        have parentAncestorIff := agreement.ancestor_iff atom
        unfold BranchAncestorAtom at parentAncestorIff ⊢
        rw [leftAddressing.ancestorAtom_child_iff leftEdge atom,
          rightAddressing.ancestorAtom_child_iff rightEdge atom,
          agreement.left_atom, agreement.right_atom]
        simp only [Option.some.injEq]
        tauto }
  have childDepthEq : left.depth leftChild = right.depth rightChild := by
    calc
      left.depth leftChild = left.depth leftParent + 1 := left.child_depth leftEdge
      _ = right.depth rightParent + 1 :=
        congrArg (fun depth => depth + 1) agreement.parent_depth_eq
      _ = right.depth rightChild := (right.child_depth rightEdge).symm
  have childAncestorAtDepthIff : ∀ atom depth,
      AncestorAtomAtDepth left leftChild atom depth ↔
        AncestorAtomAtDepth right rightChild atom depth := by
    intro atom depth
    rw [leftAddressing.ancestorAtomAtDepth_child_iff leftEdge atom depth,
      rightAddressing.ancestorAtomAtDepth_child_iff rightEdge atom depth,
      agreement.left_atom, agreement.right_atom, agreement.parent_depth_eq,
      agreement.ancestorAtDepth_iff atom depth]
  exact FaithfulLabelledParentAgreement.ofFaithful molecule externalParent ligand left right
    leftFaithful rightFaithful leftChild rightChild childParentAgreement childDepthEq
      childAncestorAtDepthIff

omit [Fintype Atom] [DecidableEq Atom] in
/-- Depth-indexed ancestor agreement transports the complete legal ring-distance relation between
matched real parents. -/
theorem FaithfulLabelledParentAgreement.ringDuplicateDistanceAt_iff
    {left right : RootedDigraph Atom} {externalParent : Atom}
    {leftParent : left.Node} {rightParent : right.Node}
    (agreement : FaithfulLabelledParentAgreement left right externalParent
      leftParent rightParent)
    (atom : Atom) (distance : Nat) :
    RingDuplicateDistanceAt left externalParent leftParent atom distance ↔
      RingDuplicateDistanceAt right externalParent rightParent atom distance := by
  constructor
  · rintro (external | represented)
    · exact Or.inl external
    · obtain ⟨ancestor, ancestorPath, ancestorAtom, ancestorDistance⟩ := represented
      have leftAt : AncestorAtomAtDepth left leftParent atom (left.depth ancestor) :=
        ⟨ancestor, ancestorPath, ancestorAtom, rfl⟩
      obtain ⟨rightAncestor, rightPath, rightAtom, rightDepth⟩ :=
        (agreement.ancestorAtDepth_iff atom (left.depth ancestor)).1 leftAt
      exact Or.inr ⟨rightAncestor, rightPath, rightAtom,
        ancestorDistance.trans (congrArg (fun depth => depth + 1) rightDepth.symm)⟩
  · rintro (external | represented)
    · exact Or.inl external
    · obtain ⟨ancestor, ancestorPath, ancestorAtom, ancestorDistance⟩ := represented
      have rightAt : AncestorAtomAtDepth right rightParent atom (right.depth ancestor) :=
        ⟨ancestor, ancestorPath, ancestorAtom, rfl⟩
      obtain ⟨leftAncestor, leftPath, leftAtom, leftDepth⟩ :=
        (agreement.ancestorAtDepth_iff atom (right.depth ancestor)).2 rightAt
      exact Or.inr ⟨leftAncestor, leftPath, leftAtom,
        ancestorDistance.trans (congrArg (fun depth => depth + 1) leftDepth.symm)⟩

/-- Number of children carrying one complete semantic label, including duplicate-distance
payloads. -/
noncomputable def ChildLabelCount (graph : RootedDigraph Atom) (parent : graph.Node)
    (label : NodeLabel Atom) : Nat :=
  ChildCountWhere graph parent fun child => graph.label child = label

/-- The finite subtype of immediate children of one hierarchy node. -/
def ChildNode (graph : RootedDigraph Atom) (parent : graph.Node) :=
  {child : graph.Node // graph.child parent child}

/-- Flatten the label fiber of the child subtype to the conjunction subtype counted by
`ChildLabelCount`. -/
def childLabelFiberFlatten (graph : RootedDigraph Atom) (parent : graph.Node)
    (label : NodeLabel Atom) :
    {child : ChildNode graph parent // graph.label child.1 = label} ≃
      {child : graph.Node // graph.child parent child ∧ graph.label child = label} where
  toFun child := ⟨child.1.1, child.1.2, child.2⟩
  invFun child := ⟨⟨child.1, child.2.1⟩, child.2.2⟩
  left_inv := by intro child; rfl
  right_inv := by intro child; rfl

/-- Equal complete-label counts provide an equivalence between the two corresponding child-label
fibers. -/
noncomputable def childLabelFiberEquivOfCounts
    (left right : RootedDigraph Atom)
    (leftParent : left.Node) (rightParent : right.Node)
    (counts : ∀ label,
      ChildLabelCount left leftParent label = ChildLabelCount right rightParent label)
    (label : NodeLabel Atom) :
    {child : ChildNode left leftParent // left.label child.1 = label} ≃
      {child : ChildNode right rightParent // right.label child.1 = label} := by
  classical
  letI : Fintype left.Node := left.nodeFintype
  letI : Fintype right.Node := right.nodeFintype
  letI : Finite (ChildNode left leftParent) := by
    unfold ChildNode
    infer_instance
  letI : Finite (ChildNode right rightParent) := by
    unfold ChildNode
    infer_instance
  letI : Fintype (ChildNode left leftParent) := Fintype.ofFinite _
  letI : Fintype (ChildNode right rightParent) := Fintype.ofFinite _
  apply Fintype.equivOfCardEq
  have nestedCardEq :
      Nat.card {child : ChildNode left leftParent // left.label child.1 = label} =
        Nat.card {child : ChildNode right rightParent // right.label child.1 = label} := by
    calc
      Nat.card {child : ChildNode left leftParent // left.label child.1 = label} =
          ChildLabelCount left leftParent label := by
            simpa [ChildLabelCount, ChildCountWhere] using
              Nat.card_congr (childLabelFiberFlatten left leftParent label)
      _ = ChildLabelCount right rightParent label := counts label
      _ = Nat.card {child : ChildNode right rightParent //
          right.label child.1 = label} := by
            simpa [ChildLabelCount, ChildCountWhere] using
              (Nat.card_congr (childLabelFiberFlatten right rightParent label)).symm
  simpa only [Nat.card_eq_fintype_card] using nestedCardEq

/-- Fiberwise complete-label equivalences combine into one label-preserving equivalence of the
whole immediate-child sets. -/
noncomputable def childEquivOfLabelCounts
    (left right : RootedDigraph Atom)
    (leftParent : left.Node) (rightParent : right.Node)
    (counts : ∀ label,
      ChildLabelCount left leftParent label = ChildLabelCount right rightParent label) :
    ChildNode left leftParent ≃ ChildNode right rightParent :=
  Equiv.ofFiberEquiv fun label =>
    childLabelFiberEquivOfCounts left right leftParent rightParent counts label

omit [Fintype Atom] [DecidableEq Atom] in
theorem childEquivOfLabelCounts_map_label
    (left right : RootedDigraph Atom)
    (leftParent : left.Node) (rightParent : right.Node)
    (counts : ∀ label,
      ChildLabelCount left leftParent label = ChildLabelCount right rightParent label)
    (child : ChildNode left leftParent) :
    right.label ((childEquivOfLabelCounts left right leftParent rightParent counts child).1) =
      left.label child.1 := by
  simpa [childEquivOfLabelCounts] using
    Equiv.ofFiberEquiv_map
      (fun label => childLabelFiberEquivOfCounts left right leftParent rightParent counts label)
      child

omit [Fintype Atom] [DecidableEq Atom] in
/-- Child counts on one graph respect pointwise equivalence of predicates along actual edges. -/
theorem childCountWhere_congr
    (graph : RootedDigraph Atom) (parent : graph.Node)
    (first second : graph.Node → Prop)
    (predicateIff : ∀ child, graph.child parent child → (first child ↔ second child)) :
    ChildCountWhere graph parent first = ChildCountWhere graph parent second := by
  unfold ChildCountWhere
  apply Nat.card_congr
  exact (Equiv.refl graph.Node).subtypeEquiv fun child => by
    constructor
    · rintro ⟨edge, satisfies⟩
      exact ⟨edge, (predicateIff child edge).1 satisfies⟩
    · rintro ⟨edge, satisfies⟩
      exact ⟨edge, (predicateIff child edge).2 satisfies⟩

omit [Fintype Atom] [DecidableEq Atom] in
/-- If one exact label is impossible below both parents, its two child counts agree. -/
theorem childLabelCount_eq_of_impossible
    (left right : RootedDigraph Atom)
    (leftParent : left.Node) (rightParent : right.Node) (label : NodeLabel Atom)
    (leftImpossible : ∀ child, left.child leftParent child → left.label child ≠ label)
    (rightImpossible : ∀ child, right.child rightParent child → right.label child ≠ label) :
    ChildLabelCount left leftParent label = ChildLabelCount right rightParent label := by
  unfold ChildLabelCount ChildCountWhere
  apply Nat.card_congr
  exact
    { toFun := fun child =>
        False.elim (leftImpossible child.1 child.2.1 child.2.2)
      invFun := fun child =>
        False.elim (rightImpossible child.1 child.2.1 child.2.2)
      left_inv := fun child =>
        False.elim (leftImpossible child.1 child.2.1 child.2.2)
      right_inv := fun child =>
        False.elim (rightImpossible child.1 child.2.1 child.2.2) }

omit [Fintype Atom] [DecidableEq Atom] in
/-- Counting a complete real-atom label is exactly the existing real-provenance category count. -/
theorem childRealLabelCount_eq_category
    (graph : RootedDigraph Atom) (parent : graph.Node) (atom : Atom) :
    ChildLabelCount graph parent ⟨some atom, NodeProvenance.realAtom⟩ =
      ChildAtomProvenanceCount graph parent atom ProvenanceRealAtom := by
  unfold ChildLabelCount ChildAtomProvenanceCount
  apply childCountWhere_congr
  intro child _edge
  cases labelEq : graph.label child with
  | mk atom? provenance =>
      cases atom? <;> cases provenance <;>
        simp [ProvenanceRealAtom]

/-- At its intrinsic distance, a complete multiple-bond-duplicate label counts the entire
multiple-bond provenance category for that atom. -/
theorem FaithfulExactExpansion.childMultipleBondLabelCount_eq_category
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (graph : RootedDigraph Atom)
    (faithful : FaithfulExactExpansion molecule externalParent ligand graph)
    (parent : graph.Node) (atom : Atom) (distance : Nat)
    (distanceEq : distance = graph.depth parent + 1) :
    ChildLabelCount graph parent
        ⟨some atom, NodeProvenance.multipleBondDuplicate distance⟩ =
      ChildAtomProvenanceCount graph parent atom ProvenanceMultipleBondDuplicate := by
  unfold ChildLabelCount ChildAtomProvenanceCount
  apply childCountWhere_congr
  intro child edge
  cases labelEq : graph.label child with
  | mk atom? provenance =>
      cases atom? with
      | none =>
          cases provenance <;>
            simp [ProvenanceMultipleBondDuplicate]
      | some childAtom =>
          cases provenance with
          | realAtom | ringDuplicate | phantom | lonePair | auxiliary =>
              simp [ProvenanceMultipleBondDuplicate]
          | multipleBondDuplicate actualDistance =>
              have actualDistanceEq :=
                faithful.multipleBondDuplicate_distance_eq_depth molecule externalParent ligand
                  graph parent child edge (some childAtom) actualDistance labelEq
              simp [ProvenanceMultipleBondDuplicate, actualDistanceEq, distanceEq]

/-- At a legal intrinsic distance, a complete ring-duplicate label counts the entire ring
provenance category for that atom. -/
theorem FaithfulExactExpansion.childRingLabelCount_eq_category
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (graph : RootedDigraph Atom)
    (faithful : FaithfulExactExpansion molecule externalParent ligand graph)
    (parent : graph.Node) (atom : Atom) (distance : Nat)
    (legalDistance : RingDuplicateDistanceAt graph externalParent parent atom distance) :
    ChildLabelCount graph parent ⟨some atom, NodeProvenance.ringDuplicate distance⟩ =
      ChildAtomProvenanceCount graph parent atom ProvenanceRingDuplicate := by
  unfold ChildLabelCount ChildAtomProvenanceCount
  apply childCountWhere_congr
  intro child edge
  cases labelEq : graph.label child with
  | mk atom? provenance =>
      cases atom? with
      | none =>
          cases provenance <;>
            simp [ProvenanceRingDuplicate]
      | some childAtom =>
          cases provenance with
          | realAtom | multipleBondDuplicate | phantom | lonePair | auxiliary =>
              simp [ProvenanceRingDuplicate]
          | ringDuplicate actualDistance =>
              by_cases childAtomEq : childAtom = atom
              · subst childAtom
                have actualLegal := faithful.ringDuplicate_distance_at molecule externalParent
                  ligand graph parent child edge atom actualDistance labelEq
                have actualDistanceEq := RingDuplicateDistanceAt.unique graph externalParent parent
                  (faithful.externalParent_not_ancestor molecule externalParent ligand graph parent)
                  (fun currentAtom first second =>
                    faithful.ancestorAtomAtDepth_unique molecule externalParent ligand graph parent
                      currentAtom first second)
                  atom actualLegal legalDistance
                simp [ProvenanceRingDuplicate, actualDistanceEq]
              · simp [ProvenanceRingDuplicate, childAtomEq]

/-- Exact complete-label histograms shared by two matched faithful parents. -/
structure FaithfulChildLabelHistogramAgreement
    (left right : RootedDigraph Atom)
    (leftParent : left.Node) (rightParent : right.Node) : Prop where
  labelCount : ∀ label,
    ChildLabelCount left leftParent label = ChildLabelCount right rightParent label

/-- Depth-aware matched-parent agreement upgrades the coarse atom/provenance histograms to counts
of complete labels, including every multiple-bond and ring-duplicate distance payload. -/
theorem faithfulExactExpansion_childLabelHistogram_eq
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftParent : left.Node) (rightParent : right.Node)
    (agreement : FaithfulLabelledParentAgreement left right externalParent
      leftParent rightParent) :
    FaithfulChildLabelHistogramAgreement left right leftParent rightParent := by
  rcases leftFaithful.1.2 with ⟨_leftAddressing, leftMultiplicities⟩
  rcases rightFaithful.1.2 with ⟨_rightAddressing, rightMultiplicities⟩
  have multipleCategoryEq : ∀ atom,
      ChildAtomProvenanceCount left leftParent atom ProvenanceMultipleBondDuplicate =
        ChildAtomProvenanceCount right rightParent atom ProvenanceMultipleBondDuplicate := by
    intro atom
    have leftCounts := leftMultiplicities leftParent agreement.parentAtom
      agreement.left_atom agreement.left_real atom
    have rightCounts := rightMultiplicities rightParent agreement.parentAtom
      agreement.right_atom agreement.right_real atom
    exact leftCounts.2.1.trans rightCounts.2.1.symm
  have ringCategoryEq : ∀ atom,
      ChildAtomProvenanceCount left leftParent atom ProvenanceRingDuplicate =
        ChildAtomProvenanceCount right rightParent atom ProvenanceRingDuplicate := by
    intro atom
    have leftCounts := leftMultiplicities leftParent agreement.parentAtom
      agreement.left_atom agreement.left_real atom
    have rightCounts := rightMultiplicities rightParent agreement.parentAtom
      agreement.right_atom agreement.right_real atom
    rw [leftCounts.2.2.1, rightCounts.2.2.1, agreement.ancestor_iff atom,
      agreement.suppressed_iff atom]
  have realCategoryEq : ∀ atom,
      ChildAtomProvenanceCount left leftParent atom ProvenanceRealAtom =
        ChildAtomProvenanceCount right rightParent atom ProvenanceRealAtom := by
    intro atom
    have leftCounts := leftMultiplicities leftParent agreement.parentAtom
      agreement.left_atom agreement.left_real atom
    have rightCounts := rightMultiplicities rightParent agreement.parentAtom
      agreement.right_atom agreement.right_real atom
    rw [leftCounts.2.2.2, rightCounts.2.2.2, agreement.ancestor_iff atom]
  refine ⟨?_⟩
  intro label
  cases label with
  | mk atom? provenance =>
      cases atom? with
      | none =>
          apply childLabelCount_eq_of_impossible left right leftParent rightParent
          · intro child edge labelEq
            obtain ⟨atom, atomEq⟩ := leftFaithful.2.2.1 leftParent child edge
            simp [labelEq] at atomEq
          · intro child edge labelEq
            obtain ⟨atom, atomEq⟩ := rightFaithful.2.2.1 rightParent child edge
            simp [labelEq] at atomEq
      | some atom =>
          cases provenance with
          | realAtom =>
              rw [childRealLabelCount_eq_category left leftParent atom,
                childRealLabelCount_eq_category right rightParent atom]
              exact realCategoryEq atom
          | multipleBondDuplicate distance =>
              by_cases leftDistance : distance = left.depth leftParent + 1
              · have rightDistance : distance = right.depth rightParent + 1 :=
                  leftDistance.trans (congrArg (fun depth => depth + 1)
                    agreement.parent_depth_eq)
                rw [leftFaithful.childMultipleBondLabelCount_eq_category molecule externalParent
                    ligand left leftParent atom distance leftDistance,
                  rightFaithful.childMultipleBondLabelCount_eq_category molecule externalParent
                    ligand right rightParent atom distance rightDistance]
                exact multipleCategoryEq atom
              · have rightDistance : distance ≠ right.depth rightParent + 1 := by
                  intro distanceEq
                  exact leftDistance (distanceEq.trans (congrArg (fun depth => depth + 1)
                    agreement.parent_depth_eq.symm))
                apply childLabelCount_eq_of_impossible left right leftParent rightParent
                · intro child edge labelEq
                  exact leftDistance
                    (leftFaithful.multipleBondDuplicate_distance_eq_depth molecule externalParent
                      ligand left leftParent child edge (some atom) distance labelEq)
                · intro child edge labelEq
                  exact rightDistance
                    (rightFaithful.multipleBondDuplicate_distance_eq_depth molecule externalParent
                      ligand right rightParent child edge (some atom) distance labelEq)
          | ringDuplicate distance =>
              by_cases leftLegal :
                  RingDuplicateDistanceAt left externalParent leftParent atom distance
              · have rightLegal :=
                  (agreement.ringDuplicateDistanceAt_iff atom distance).1 leftLegal
                rw [leftFaithful.childRingLabelCount_eq_category molecule externalParent ligand
                    left leftParent atom distance leftLegal,
                  rightFaithful.childRingLabelCount_eq_category molecule externalParent ligand
                    right rightParent atom distance rightLegal]
                exact ringCategoryEq atom
              · have rightIllegal :
                    ¬ RingDuplicateDistanceAt right externalParent rightParent atom distance := by
                  intro rightLegal
                  exact leftLegal
                    ((agreement.ringDuplicateDistanceAt_iff atom distance).2 rightLegal)
                apply childLabelCount_eq_of_impossible left right leftParent rightParent
                · intro child edge labelEq
                  exact leftLegal
                    (leftFaithful.ringDuplicate_distance_at molecule externalParent ligand left
                      leftParent child edge atom distance labelEq)
                · intro child edge labelEq
                  exact rightIllegal
                    (rightFaithful.ringDuplicate_distance_at molecule externalParent ligand right
                      rightParent child edge atom distance labelEq)
          | phantom distance | lonePair distance | auxiliary distance =>
              apply childLabelCount_eq_of_impossible left right leftParent rightParent
              · intro child _edge labelEq
                have compatible := leftFaithful.1.1.2.1 child
                simp [labelEq, LabelCompatible] at compatible
              · intro child _edge labelEq
                have compatible := rightFaithful.1.1.2.1 child
                simp [labelEq, LabelCompatible] at compatible

/-- The exact histogram theorem chooses a complete-label-preserving equivalence between the two
finite immediate-child sets. -/
noncomputable def FaithfulLabelledParentAgreement.childEquiv
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftParent : left.Node) (rightParent : right.Node)
    (agreement : FaithfulLabelledParentAgreement left right externalParent
      leftParent rightParent) :
    ChildNode left leftParent ≃ ChildNode right rightParent :=
  childEquivOfLabelCounts left right leftParent rightParent
    (faithfulExactExpansion_childLabelHistogram_eq molecule externalParent ligand left right
      leftFaithful rightFaithful leftParent rightParent agreement).labelCount

theorem FaithfulLabelledParentAgreement.childEquiv_map_label
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftParent : left.Node) (rightParent : right.Node)
    (agreement : FaithfulLabelledParentAgreement left right externalParent
      leftParent rightParent)
    (child : ChildNode left leftParent) :
    right.label ((agreement.childEquiv molecule externalParent ligand left right leftFaithful
      rightFaithful leftParent rightParent child).1) = left.label child.1 := by
  apply childEquivOfLabelCounts_map_label

/-- The selected exact-label child equivalence recursively carries the full agreement to every
matched real child pair. -/
noncomputable def FaithfulLabelledParentAgreement.childEquiv_realChildren
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftParent : left.Node) (rightParent : right.Node)
    (agreement : FaithfulLabelledParentAgreement left right externalParent
      leftParent rightParent)
    (child : ChildNode left leftParent)
    (childReal : ProvenanceRealAtom (left.label child.1).provenance) :
    FaithfulLabelledParentAgreement left right externalParent child.1
      (agreement.childEquiv molecule externalParent ligand left right leftFaithful rightFaithful
        leftParent rightParent child).1 := by
  let matched := agreement.childEquiv molecule externalParent ligand left right leftFaithful
    rightFaithful leftParent rightParent child
  apply agreement.realChildren molecule externalParent ligand left right leftFaithful rightFaithful
    leftParent rightParent child.1 matched.1 child.2 matched.2
  · exact (agreement.childEquiv_map_label molecule externalParent ligand left right leftFaithful
      rightFaithful leftParent rightParent child).symm
  · exact childReal

/-- Agreement for an arbitrary matched node pair.  Complete labels and depths always agree; when
the left node is real, the stronger parent agreement is available for recursive child matching.
Terminal nodes need no fictitious real-parent witness. -/
structure FaithfulNodeAgreement
    (left right : RootedDigraph Atom) (externalParent : Atom)
    (leftNode : left.Node) (rightNode : right.Node) : Type u where
  label_eq : left.label leftNode = right.label rightNode
  depth_eq : left.depth leftNode = right.depth rightNode
  real_agreement : ProvenanceRealAtom (left.label leftNode).provenance →
    FaithfulLabelledParentAgreement left right externalParent leftNode rightNode

/-- Rooted faithful expansions start with an arbitrary-node agreement at their roots. -/
noncomputable def FaithfulNodeAgreement.roots
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right) :
    FaithfulNodeAgreement left right externalParent left.root right.root where
  label_eq := leftFaithful.1.1.1.trans rightFaithful.1.1.1.symm
  depth_eq := left.root_depth.trans right.root_depth.symm
  real_agreement := fun _leftRootReal =>
    FaithfulLabelledParentAgreement.roots molecule externalParent ligand left right leftFaithful
      rightFaithful

/-- Every child of an arbitrarily matched node has a selected child on the right carrying the
same complete label, the same depth, and (when real) the recursively strengthened agreement. -/
noncomputable def FaithfulNodeAgreement.child
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftParent : left.Node) (rightParent : right.Node)
    (agreement : FaithfulNodeAgreement left right externalParent leftParent rightParent)
    (child : ChildNode left leftParent) :
    Σ matched : ChildNode right rightParent,
      FaithfulNodeAgreement left right externalParent child.1 matched.1 := by
  have parentReal := leftFaithful.real_of_hasChild molecule externalParent ligand left leftParent
    child.1 child.2
  let parentAgreement := agreement.real_agreement parentReal
  let matched := parentAgreement.childEquiv molecule externalParent ligand left right leftFaithful
    rightFaithful leftParent rightParent child
  refine ⟨matched, ?_⟩
  refine
    { label_eq := ?_
      depth_eq := ?_
      real_agreement := ?_ }
  · exact (parentAgreement.childEquiv_map_label molecule externalParent ligand left right
      leftFaithful rightFaithful leftParent rightParent child).symm
  · calc
      left.depth child.1 = left.depth leftParent + 1 := left.child_depth child.2
      _ = right.depth rightParent + 1 :=
        congrArg (fun depth => depth + 1) agreement.depth_eq
      _ = right.depth matched.1 := (right.child_depth matched.2).symm
  · intro childReal
    exact parentAgreement.childEquiv_realChildren molecule externalParent ligand left right
      leftFaithful rightFaithful leftParent rightParent child childReal

/-- One recursive step of the global node correspondence. -/
noncomputable def faithfulNodeMatchStep
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftAddressing : left.Addressing) (node : left.Node)
    (recurse : ∀ parent, left.child parent node →
      Σ matched : right.Node,
        FaithfulNodeAgreement left right externalParent parent matched) :
    Σ matched : right.Node,
      FaithfulNodeAgreement left right externalParent node matched := by
  by_cases nodeRoot : node = left.root
  · subst node
    exact ⟨right.root, FaithfulNodeAgreement.roots molecule externalParent ligand left right
      leftFaithful rightFaithful⟩
  · let parent := leftAddressing.parentOfNonroot node nodeRoot
    have parentEdge : left.child parent node :=
      leftAddressing.parentOfNonroot_child node nodeRoot
    let parentMatch := recurse parent parentEdge
    let childMatch := parentMatch.2.child molecule externalParent ligand left right leftFaithful
      rightFaithful parent parentMatch.1 ⟨node, parentEdge⟩
    exact ⟨childMatch.1.1, childMatch.2⟩

/-- Global certified node correspondence obtained by well-founded recursion through each node's
unique addressed parent.  This constructs a matched node for every left node; bijectivity and edge
reflection are subsequent theorems, not part of this definition. -/
noncomputable def faithfulNodeMatch
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftAddressing : left.Addressing) :
    ∀ node : left.Node,
      Σ matched : right.Node,
        FaithfulNodeAgreement left right externalParent node matched :=
  left.child_wellFounded.fix
    (faithfulNodeMatchStep molecule externalParent ligand left right leftFaithful rightFaithful
      leftAddressing)

theorem faithfulNodeMatch_equation
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftAddressing : left.Addressing) (node : left.Node) :
    faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
        leftAddressing node =
      faithfulNodeMatchStep molecule externalParent ligand left right leftFaithful rightFaithful
        leftAddressing node (fun parent _edge =>
          faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
            leftAddressing parent) := by
  rw [faithfulNodeMatch, WellFounded.fix_eq]

theorem faithfulNodeMatch_map_root
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftAddressing : left.Addressing) :
    (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
      leftAddressing left.root).1 = right.root := by
  rw [faithfulNodeMatch_equation molecule externalParent ligand left right leftFaithful
    rightFaithful leftAddressing left.root]
  simp [faithfulNodeMatchStep]

theorem faithfulNodeMatch_map_label
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftAddressing : left.Addressing) (node : left.Node) :
    left.label node = right.label
      (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
        leftAddressing node).1 :=
  (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
    leftAddressing node).2.label_eq

theorem faithfulNodeMatch_map_depth
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftAddressing : left.Addressing) (node : left.Node) :
    left.depth node = right.depth
      (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
        leftAddressing node).1 :=
  (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
    leftAddressing node).2.depth_eq

theorem faithfulNodeMatch_parentOfNonroot_child
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftAddressing : left.Addressing) (node : left.Node)
    (nodeNeRoot : node ≠ left.root) :
    right.child
      (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
        leftAddressing (leftAddressing.parentOfNonroot node nodeNeRoot)).1
      (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
        leftAddressing node).1 := by
  let parent := leftAddressing.parentOfNonroot node nodeNeRoot
  have parentEdge : left.child parent node :=
    leftAddressing.parentOfNonroot_child node nodeNeRoot
  let parentMatch := faithfulNodeMatch molecule externalParent ligand left right leftFaithful
    rightFaithful leftAddressing parent
  let childMatch := parentMatch.2.child molecule externalParent ligand left right leftFaithful
    rightFaithful parent parentMatch.1 ⟨node, parentEdge⟩
  have selectedEdge : right.child parentMatch.1 childMatch.1.1 := childMatch.1.2
  rw [faithfulNodeMatch_equation molecule externalParent ligand left right leftFaithful
    rightFaithful leftAddressing node]
  simpa [faithfulNodeMatchStep, nodeNeRoot, parent, parentEdge, parentMatch, childMatch] using
    selectedEdge

/-- The global certified node correspondence preserves every hierarchy edge. -/
theorem faithfulNodeMatch_map_child
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftAddressing : left.Addressing)
    {parent node : left.Node} (edge : left.child parent node) :
    right.child
      (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
        leftAddressing parent).1
      (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
        leftAddressing node).1 := by
  have nodeNeRoot : node ≠ left.root := by
    intro nodeRoot
    subst node
    exact leftAddressing.not_child_root parent edge
  have chosenParentEq : leftAddressing.parentOfNonroot node nodeNeRoot = parent :=
    leftAddressing.parent_unique (leftAddressing.parentOfNonroot_child node nodeNeRoot) edge
  have mappedEdge :=
    faithfulNodeMatch_parentOfNonroot_child molecule externalParent ligand left right leftFaithful
      rightFaithful leftAddressing node nodeNeRoot
  rw [chosenParentEq] at mappedEdge
  exact mappedEdge

/-- The exact child equivalence selected at one globally matched real parent. -/
noncomputable def faithfulNodeMatchChildEquiv
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftAddressing : left.Addressing) (parent : left.Node)
    (parentReal : ProvenanceRealAtom (left.label parent).provenance) :
    ChildNode left parent ≃ ChildNode right
      (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
        leftAddressing parent).1 :=
  ((faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
    leftAddressing parent).2.real_agreement parentReal).childEquiv molecule externalParent ligand
      left right leftFaithful rightFaithful parent
        (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
          leftAddressing parent).1

/-- The recursively constructed global map uses exactly its parent's selected finite child
equivalence. -/
theorem faithfulNodeMatch_eq_childEquiv
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftAddressing : left.Addressing)
    {parent node : left.Node} (edge : left.child parent node)
    (parentReal : ProvenanceRealAtom (left.label parent).provenance) :
    (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
      leftAddressing node).1 =
      (faithfulNodeMatchChildEquiv molecule externalParent ligand left right leftFaithful
        rightFaithful leftAddressing parent parentReal ⟨node, edge⟩).1 := by
  have nodeNeRoot : node ≠ left.root := by
    intro nodeRoot
    subst node
    exact leftAddressing.not_child_root parent edge
  have chosenParentEq : leftAddressing.parentOfNonroot node nodeNeRoot = parent :=
    leftAddressing.parent_unique (leftAddressing.parentOfNonroot_child node nodeNeRoot) edge
  subst parent
  rw [faithfulNodeMatch_equation molecule externalParent ligand left right leftFaithful
    rightFaithful leftAddressing node]
  simp [faithfulNodeMatchStep, nodeNeRoot, faithfulNodeMatchChildEquiv,
    FaithfulNodeAgreement.child]

/-- The global faithful node correspondence is injective: equal images have equal unique parents,
then the selected finite child equivalence separates the two siblings. -/
theorem faithfulNodeMatch_injective
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftAddressing : left.Addressing) :
    Function.Injective fun node =>
      (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
        leftAddressing node).1 := by
  rcases rightFaithful.1.2 with ⟨rightAddressing, _rightMultiplicities⟩
  intro first
  refine left.child_wellFounded.induction (C := fun first => ∀ second,
    (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
      leftAddressing first).1 =
      (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
        leftAddressing second).1 → first = second) first ?_
  intro first inductionHypothesis second mappedEq
  have depthEq : left.depth first = left.depth second := by
    calc
      left.depth first = right.depth
          (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
            leftAddressing first).1 :=
        faithfulNodeMatch_map_depth molecule externalParent ligand left right leftFaithful
          rightFaithful leftAddressing first
      _ = right.depth
          (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
            leftAddressing second).1 := congrArg right.depth mappedEq
      _ = left.depth second :=
        (faithfulNodeMatch_map_depth molecule externalParent ligand left right leftFaithful
          rightFaithful leftAddressing second).symm
  by_cases firstRoot : first = left.root
  · subst first
    have secondDepthZero : left.depth second = 0 := depthEq.symm.trans left.root_depth
    exact (eq_root_of_depth_eq_zero left second secondDepthZero).symm
  · have secondNeRoot : second ≠ left.root := by
      intro secondRoot
      subst second
      have firstDepthZero : left.depth first = 0 := depthEq.trans left.root_depth
      exact firstRoot (eq_root_of_depth_eq_zero left first firstDepthZero)
    let firstParent := leftAddressing.parentOfNonroot first firstRoot
    let secondParent := leftAddressing.parentOfNonroot second secondNeRoot
    have firstEdge : left.child firstParent first :=
      leftAddressing.parentOfNonroot_child first firstRoot
    have secondEdge : left.child secondParent second :=
      leftAddressing.parentOfNonroot_child second secondNeRoot
    have firstMappedEdge := faithfulNodeMatch_map_child molecule externalParent ligand left right
      leftFaithful rightFaithful leftAddressing firstEdge
    have secondMappedEdge := faithfulNodeMatch_map_child molecule externalParent ligand left right
      leftFaithful rightFaithful leftAddressing secondEdge
    have secondMappedEdgeAtFirst : right.child
        (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
          leftAddressing secondParent).1
        (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
          leftAddressing first).1 := by
      rw [mappedEq]
      exact secondMappedEdge
    have parentMappedEq := rightAddressing.parent_unique firstMappedEdge secondMappedEdgeAtFirst
    have parentEq : firstParent = secondParent :=
      inductionHypothesis firstParent firstEdge secondParent parentMappedEq
    have secondEdgeAtFirst : left.child firstParent second := by
      rw [parentEq]
      exact secondEdge
    have parentReal := leftFaithful.real_of_hasChild molecule externalParent ligand left firstParent
      first firstEdge
    let childEquiv := faithfulNodeMatchChildEquiv molecule externalParent ligand left right
      leftFaithful rightFaithful leftAddressing firstParent parentReal
    have firstLocal := faithfulNodeMatch_eq_childEquiv molecule externalParent ligand left right
      leftFaithful rightFaithful leftAddressing firstEdge parentReal
    have secondLocal := faithfulNodeMatch_eq_childEquiv molecule externalParent ligand left right
      leftFaithful rightFaithful leftAddressing secondEdgeAtFirst parentReal
    have localEq : childEquiv ⟨first, firstEdge⟩ =
        childEquiv ⟨second, secondEdgeAtFirst⟩ := by
      apply Subtype.ext
      exact firstLocal.symm.trans (mappedEq.trans secondLocal)
    exact congrArg Subtype.val (childEquiv.injective localEq)

/-- The global faithful node correspondence is a bijection.  Injectivity in both directions,
together with finiteness of both rooted digraphs, forces equality of their node cardinalities. -/
theorem faithfulNodeMatch_bijective
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftAddressing : left.Addressing) :
    Function.Bijective fun node =>
      (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
        leftAddressing node).1 := by
  classical
  letI : Fintype left.Node := left.nodeFintype
  letI : Fintype right.Node := right.nodeFintype
  rcases rightFaithful.1.2 with ⟨rightAddressing, _rightMultiplicities⟩
  have forwardInjective : Function.Injective fun node =>
      (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
        leftAddressing node).1 :=
    faithfulNodeMatch_injective molecule externalParent ligand left right leftFaithful
      rightFaithful leftAddressing
  have reverseInjective : Function.Injective fun node =>
      (faithfulNodeMatch molecule externalParent ligand right left rightFaithful leftFaithful
        rightAddressing node).1 :=
    faithfulNodeMatch_injective molecule externalParent ligand right left rightFaithful
      leftFaithful rightAddressing
  have forwardCardLe : Fintype.card left.Node ≤ Fintype.card right.Node :=
    Fintype.card_le_of_injective _ forwardInjective
  have reverseCardLe : Fintype.card right.Node ≤ Fintype.card left.Node :=
    Fintype.card_le_of_injective _ reverseInjective
  exact (Fintype.bijective_iff_injective_and_card _).2
    ⟨forwardInjective, Nat.le_antisymm forwardCardLe reverseCardLe⟩

/-- The global faithful node correspondence reflects as well as preserves child edges. -/
theorem faithfulNodeMatch_child_iff
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftAddressing : left.Addressing) {parent node : left.Node} :
    left.child parent node ↔
      right.child
        (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
          leftAddressing parent).1
        (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
          leftAddressing node).1 := by
  constructor
  · exact faithfulNodeMatch_map_child molecule externalParent ligand left right leftFaithful
      rightFaithful leftAddressing
  · intro rightEdge
    rcases rightFaithful.1.2 with ⟨rightAddressing, _rightMultiplicities⟩
    have nodeNeRoot : node ≠ left.root := by
      intro nodeRoot
      subst node
      rw [faithfulNodeMatch_map_root molecule externalParent ligand left right leftFaithful
        rightFaithful leftAddressing] at rightEdge
      exact rightAddressing.not_child_root _ rightEdge
    let canonicalParent := leftAddressing.parentOfNonroot node nodeNeRoot
    have canonicalEdge : left.child canonicalParent node :=
      leftAddressing.parentOfNonroot_child node nodeNeRoot
    have mappedCanonicalEdge := faithfulNodeMatch_map_child molecule externalParent ligand left
      right leftFaithful rightFaithful leftAddressing canonicalEdge
    have mappedParentEq := rightAddressing.parent_unique rightEdge mappedCanonicalEdge
    have parentEq : parent = canonicalParent :=
      faithfulNodeMatch_injective molecule externalParent ligand left right leftFaithful
        rightFaithful leftAddressing mappedParentEq
    subst parent
    exact canonicalEdge

/-- The recursive global match, packaged as a node equivalence. -/
noncomputable def faithfulNodeEquiv
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftAddressing : left.Addressing) : left.Node ≃ right.Node :=
  Equiv.ofBijective
    (fun node =>
      (faithfulNodeMatch molecule externalParent ligand left right leftFaithful rightFaithful
        leftAddressing node).1)
    (faithfulNodeMatch_bijective molecule externalParent ligand left right leftFaithful
      rightFaithful leftAddressing)

/-- Any two faithful exact expansions of the same molecular branch are isomorphic as rooted,
labelled, depth-graded digraphs. -/
noncomputable def faithfulExactExpansionIso
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftAddressing : left.Addressing) : RootedDigraph.Iso left right where
  toEquiv := faithfulNodeEquiv molecule externalParent ligand left right leftFaithful rightFaithful
    leftAddressing
  map_root := by
    simpa [faithfulNodeEquiv] using
      faithfulNodeMatch_map_root molecule externalParent ligand left right leftFaithful
        rightFaithful leftAddressing
  map_child := by
    intro parent node
    simpa [faithfulNodeEquiv] using
      faithfulNodeMatch_child_iff molecule externalParent ligand left right leftFaithful
        rightFaithful leftAddressing (parent := parent) (node := node)
  map_label := by
    intro node
    simpa [faithfulNodeEquiv] using
      faithfulNodeMatch_map_label molecule externalParent ligand left right leftFaithful
        rightFaithful leftAddressing node
  map_depth := by
    intro node
    simpa [faithfulNodeEquiv] using
      faithfulNodeMatch_map_depth molecule externalParent ligand left right leftFaithful
        rightFaithful leftAddressing node

/-- Representation independence for faithful exact expansion: no addressing choice is exposed in
the result, only existence of the rooted labelled isomorphism. -/
theorem faithfulExactExpansion_unique_up_to_iso
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right) :
    Nonempty (RootedDigraph.Iso left right) := by
  rcases leftFaithful.1.2 with ⟨leftAddressing, _leftMultiplicities⟩
  exact ⟨faithfulExactExpansionIso molecule externalParent ligand left right leftFaithful
    rightFaithful leftAddressing⟩

/-- Local category histograms shared by two matched parents.  These fields intentionally count
the whole multiple-bond and ring-duplicate categories; they make no claim that distance-bearing
labels have already been matched. -/
structure FaithfulChildCategoryHistogramAgreement
    (left right : RootedDigraph Atom)
    (leftParent : left.Node) (rightParent : right.Node) : Prop where
  total : ∀ atom,
    ChildAtomCount left leftParent atom = ChildAtomCount right rightParent atom
  multipleBondDuplicate : ∀ atom,
    ChildAtomProvenanceCount left leftParent atom ProvenanceMultipleBondDuplicate =
      ChildAtomProvenanceCount right rightParent atom ProvenanceMultipleBondDuplicate
  ringDuplicate : ∀ atom,
    ChildAtomProvenanceCount left leftParent atom ProvenanceRingDuplicate =
      ChildAtomProvenanceCount right rightParent atom ProvenanceRingDuplicate
  realAtom : ∀ atom,
    ChildAtomProvenanceCount left leftParent atom ProvenanceRealAtom =
      ChildAtomProvenanceCount right rightParent atom ProvenanceRealAtom

/-- Exact molecular multiplicities turn semantic agreement of two matched real parents into
equality of their atom/provenance-category child histograms.  Exact duplicate labels require the
stronger depth-aware invariant above and are intentionally not concluded here. -/
theorem faithfulExactExpansion_childCategoryHistogram_eq
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (left right : RootedDigraph Atom)
    (leftFaithful : FaithfulExactExpansion molecule externalParent ligand left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent ligand right)
    (leftParent : left.Node) (rightParent : right.Node)
    (agreement : FaithfulParentAgreement left right externalParent leftParent rightParent) :
    FaithfulChildCategoryHistogramAgreement left right leftParent rightParent := by
  rcases leftFaithful with
    ⟨⟨_leftLocal, ⟨_leftAddressing, leftMultiplicities⟩⟩,
      _leftRootBond, _leftAtomBearing, _leftDistances⟩
  rcases rightFaithful with
    ⟨⟨_rightLocal, ⟨_rightAddressing, rightMultiplicities⟩⟩,
      _rightRootBond, _rightAtomBearing, _rightDistances⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro atom
    have leftCounts := leftMultiplicities leftParent agreement.parentAtom
      agreement.left_atom agreement.left_real atom
    have rightCounts := rightMultiplicities rightParent agreement.parentAtom
      agreement.right_atom agreement.right_real atom
    rw [leftCounts.1, rightCounts.1, agreement.suppressed_iff atom]
  · intro atom
    have leftCounts := leftMultiplicities leftParent agreement.parentAtom
      agreement.left_atom agreement.left_real atom
    have rightCounts := rightMultiplicities rightParent agreement.parentAtom
      agreement.right_atom agreement.right_real atom
    exact leftCounts.2.1.trans rightCounts.2.1.symm
  · intro atom
    have leftCounts := leftMultiplicities leftParent agreement.parentAtom
      agreement.left_atom agreement.left_real atom
    have rightCounts := rightMultiplicities rightParent agreement.parentAtom
      agreement.right_atom agreement.right_real atom
    rw [leftCounts.2.2.1, rightCounts.2.2.1, agreement.ancestor_iff atom,
      agreement.suppressed_iff atom]
  · intro atom
    have leftCounts := leftMultiplicities leftParent agreement.parentAtom
      agreement.left_atom agreement.left_real atom
    have rightCounts := rightMultiplicities rightParent agreement.parentAtom
      agreement.right_atom agreement.right_real atom
    rw [leftCounts.2.2.2, rightCounts.2.2.2, agreement.ancestor_iff atom]

end RootedDigraph
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.faithfulExactExpansion_childCategoryHistogram_eq
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.Addressing.address_length_eq_depth
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.Addressing.strictAncestors_comparable
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.RingDuplicateDistanceAt.unique
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.duplicateDistancesCorrect_iff_intrinsic
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.faithfulExactExpansion_iff_intrinsic
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.FaithfulExactExpansion.realChild_atom_fresh
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.FaithfulExactExpansion.externalParent_not_ancestor
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.FaithfulExactExpansion.ancestorAtomAtDepth_unique
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.FaithfulLabelledParentAgreement.ofFaithful
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.FaithfulLabelledParentAgreement.roots
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.FaithfulLabelledParentAgreement.realChildren
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.FaithfulLabelledParentAgreement.ringDuplicateDistanceAt_iff
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.faithfulExactExpansion_childLabelHistogram_eq
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.FaithfulLabelledParentAgreement.childEquiv_map_label
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.FaithfulLabelledParentAgreement.childEquiv_realChildren
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.FaithfulNodeAgreement.roots
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.faithfulNodeMatch_map_label
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.faithfulNodeMatch_map_root
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.faithfulNodeMatch_map_depth
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.faithfulNodeMatch_map_child
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.faithfulNodeMatch_eq_childEquiv
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.faithfulNodeMatch_injective
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.faithfulNodeMatch_bijective
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.faithfulNodeMatch_child_iff
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.faithfulExactExpansion_unique_up_to_iso
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.FaithfulExactExpansion.multipleBondDuplicate_distance_eq_depth
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.RootedDigraph.FaithfulExactExpansion.ringDuplicate_distance_at
