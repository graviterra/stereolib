import TetraStereo.OneCenter.CIPAuthoritativeBranchComparator
import TetraStereo.OneCenter.ProductionCIPFaithfulAssembly

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open DeclarativeCIP

namespace RawMolecule

/-!
# Exact expansion for the width-unbounded authoritative compiler

The ordinary `CanonicalCompleteBuild` certificate records successful observations from the
resource-capped Rule-1a labeler.  It therefore cannot certify a successful authoritative build of
a mancude component beyond that operational cutoff.  The relations below retain the topology of
the authoritative source tree independently of which exact Rule-1a labeler supplied its labels.
This is the missing structural bridge needed for proof-carrying, width-unbounded molecule
discovery.
-/

/- A canonical source tree realizes exactly the molecular child relation, without identifying
that topological statement with either the capped or uncapped Rule-1a observation function. -/
mutual
  inductive CanonicalTreeStructurallyRealizes (mol : RawMolecule) :
      CanonicalBranchNode → CanonicalSourceTree → Prop
    | node (source : CanonicalBranchNode) (children : CanonicalSourceForest)
        (labelSupported : ∃ label,
          mol.canonicalRule1aLabelAuthoritative? source = some label)
        (childSources : List CanonicalBranchNode)
        (permutation : childSources.Perm (mol.canonicalChildren source))
        (childRealizations : CanonicalForestStructurallyRealizes mol childSources children) :
        CanonicalTreeStructurallyRealizes mol source (.node source children)

  inductive CanonicalForestStructurallyRealizes (mol : RawMolecule) :
      List CanonicalBranchNode → CanonicalSourceForest → Prop
    | nil : CanonicalForestStructurallyRealizes mol [] .nil
    | cons {source : CanonicalBranchNode} {tree : CanonicalSourceTree}
        {sources : List CanonicalBranchNode} {trees : CanonicalSourceForest}
        (head : CanonicalTreeStructurallyRealizes mol source tree)
        (tail : CanonicalForestStructurallyRealizes mol sources trees) :
        CanonicalForestStructurallyRealizes mol (source :: sources) (.cons tree trees)
end

theorem CanonicalForestStructurallyRealizes.length_eq
    {mol : RawMolecule} {sources : List CanonicalBranchNode}
    {forest : CanonicalSourceForest}
    (realizes : CanonicalForestStructurallyRealizes mol sources forest) :
    forest.toList.length = sources.length := by
  cases realizes with
  | nil => rfl
  | @cons source tree sources forest head tail =>
      simp [CanonicalSourceForest.toList, tail.length_eq]
termination_by sources.length

theorem CanonicalForestStructurallyRealizes.get
    {mol : RawMolecule} {sources : List CanonicalBranchNode}
    {forest : CanonicalSourceForest}
    (realizes : CanonicalForestStructurallyRealizes mol sources forest)
    (slot : ℕ) (sourceBound : slot < sources.length)
    (treeBound : slot < forest.toList.length) :
    CanonicalTreeStructurallyRealizes mol
      (sources.get ⟨slot, sourceBound⟩) (forest.toList.get ⟨slot, treeBound⟩) := by
  induction slot generalizing sources forest with
  | zero =>
      cases realizes with
      | nil => simp at sourceBound
      | cons head tail => exact head
  | succ slot inductionHypothesis =>
      cases realizes with
      | nil => simp at sourceBound
      | @cons source tree sources forest head tail =>
          exact inductionHypothesis tail (by simpa using sourceBound)
            (by simpa [CanonicalSourceForest.toList] using treeBound)

theorem CanonicalTreeStructurallyRealizes.subtree
    {mol : RawMolecule} {rootSource : CanonicalBranchNode}
    {tree subtree : CanonicalSourceTree}
    (realizes : CanonicalTreeStructurallyRealizes mol rootSource tree)
    (address : List ℕ) (lookup : tree.subtreeAt? address = some subtree) :
    ∃ source, CanonicalTreeStructurallyRealizes mol source subtree := by
  induction address generalizing rootSource tree with
  | nil =>
      simp only [CanonicalSourceTree.subtreeAt?] at lookup
      have treeEq : tree = subtree := Option.some.inj lookup
      subst subtree
      exact ⟨rootSource, realizes⟩
  | cons slot address inductionHypothesis =>
      cases realizes with
      | node source forest labelSupported childSources permutation children =>
          change forest.subtreeAt? slot address = some subtree at lookup
          rw [forest.subtreeAt?_eq_get?_bind] at lookup
          by_cases bound : slot < forest.toList.length
          · rw [List.getElem?_eq_getElem bound] at lookup
            simp only [Option.bind_some] at lookup
            have sourceBound : slot < childSources.length := by
              rwa [← children.length_eq]
            exact inductionHypothesis (children.get slot sourceBound bound) lookup
          · have outOfBounds : forest.toList.length ≤ slot := by omega
            rw [List.getElem?_eq_none outOfBounds] at lookup
            simp at lookup

theorem CanonicalTreeStructurallyRealizes.tree_eq_node
    {mol : RawMolecule} {source : CanonicalBranchNode} {tree : CanonicalSourceTree}
    (realizes : CanonicalTreeStructurallyRealizes mol source tree) :
    ∃ children, tree = .node source children := by
  cases realizes with
  | node source children labelSupported childSources permutation childRealizations =>
      exact ⟨children, rfl⟩

/-- Every occurrence in an authoritative realized source tree retains the successful uncapped
Rule-1a observation that allowed its compiler node to be constructed. -/
theorem CanonicalTreeStructurallyRealizes.rule1aLabelSupportedAt
    {mol : RawMolecule} {rootSource source : CanonicalBranchNode}
    {tree : CanonicalSourceTree}
    (realizes : CanonicalTreeStructurallyRealizes mol rootSource tree)
    (address : List ℕ) (sourceAt : tree.sourceAt? address = some source) :
    ∃ label, mol.canonicalRule1aLabelAuthoritative? source = some label := by
  unfold CanonicalSourceTree.sourceAt? at sourceAt
  cases subtreeEq : tree.subtreeAt? address with
  | none => simp [subtreeEq] at sourceAt
  | some subtree =>
      cases subtree with
      | node stored children =>
          simp only [subtreeEq, Option.map_some] at sourceAt
          have storedEq : stored = source := Option.some.inj sourceAt
          subst stored
          obtain ⟨realizedSource, subtreeRealizes⟩ :=
            realizes.subtree address subtreeEq
          cases subtreeRealizes with
          | node source children labelSupported childSources permutation childRealizations =>
              exact labelSupported

/-- Structural realization alone supplies the exact occurrence-level child equivalence required
by the independent hierarchical-digraph semantics. -/
theorem CanonicalTreeStructurallyRealizes.childrenExact
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (rootSource : CanonicalBranchNode) (tree : CanonicalSourceTree)
    (treeStored : key.sourceTree? = some tree)
    (realizes : CanonicalTreeStructurallyRealizes mol rootSource tree) :
    key.ChildrenExact mol := by
  intro parent parentSource parentSourceEq
  have sourceAt : tree.sourceAt? parent.1 = some parentSource := by
    simpa [key.sourceNodeAtAddress?_eq_tree_sourceAt tree treeStored] using parentSourceEq
  unfold CanonicalSourceTree.sourceAt? at sourceAt
  cases parentTreeEq : tree.subtreeAt? parent.1 with
  | none => simp [parentTreeEq] at sourceAt
  | some parentTree =>
      cases parentTree with
      | node storedParent children =>
          simp only [parentTreeEq, Option.map_some] at sourceAt
          have storedEq : storedParent = parentSource := Option.some.inj sourceAt
          subst storedParent
          obtain ⟨realizedParent, parentRealizes⟩ :=
            realizes.subtree parent.1 parentTreeEq
          cases parentRealizes with
          | node parentSource children labelSupported childSources permutation childRealizations =>
              obtain ⟨permutationEquiv, permutationGet⟩ :=
                TetraStereo.OneCenter.List.Perm.exists_finEquiv_get permutation
              let childSlots := hierarchyChildrenEquivSlots key parent
              let occupiedSlots := occupiedChildSlotsEquivFin key tree treeStored parent.1
                parentSource children parentTreeEq
              let sourceSlots : Fin children.toList.length ≃ Fin childSources.length :=
                finCongr childRealizations.length_eq
              let equivalence :
                  {child : key.HierarchyNode // key.HierarchyChild parent child} ≃
                    Fin (mol.canonicalChildren parentSource).length :=
                childSlots.trans (occupiedSlots.trans (sourceSlots.trans permutationEquiv))
              refine ⟨equivalence, ?_⟩
              intro child
              let occupied := childSlots child
              let forestIndex := occupiedSlots occupied
              let sourceIndex := sourceSlots forestIndex
              have forestLookup : children.subtreeAt? forestIndex.1 [] =
                  some (children.toList.get forestIndex) := by
                rw [children.subtreeAt?_eq_get?_bind,
                  List.getElem?_eq_getElem forestIndex.2]
                simp [CanonicalSourceTree.subtreeAt?]
              have childRealizes :=
                childRealizations.get forestIndex.1 sourceIndex.2 forestIndex.2
              obtain ⟨grandchildren, childTreeEq⟩ := childRealizes.tree_eq_node
              have addressEq : child.1.1 = parent.1 ++ [forestIndex.1] := by
                exact Classical.choose_spec child.2
              have lookup : key.sourceNodeAtAddress? child.1.1 =
                  some (childSources.get sourceIndex) := by
                rw [key.sourceNodeAtAddress?_eq_tree_sourceAt tree treeStored]
                unfold CanonicalSourceTree.sourceAt?
                rw [addressEq, tree.subtreeAt?_append, parentTreeEq]
                simp only [Option.bind_some]
                change (children.subtreeAt? forestIndex.1 []).map (fun subtree =>
                  match subtree with
                  | .node source _ => source) = some (childSources.get sourceIndex)
                rw [forestLookup, childTreeEq]
                rfl
              rw [lookup]
              apply congrArg some
              calc
                childSources.get sourceIndex =
                    (mol.canonicalChildren parentSource).get
                      (permutationEquiv sourceIndex) := permutationGet sourceIndex
                _ = (mol.canonicalChildren parentSource).get (equivalence child) := by
                  rfl

private theorem mapM_structuralRealizations
    {α β : Type*} (f : α → Option β) (complete : β → Bool)
    (R : α → β → Prop)
    (sound : ∀ a b, f a = some b → complete b = true → R a b) :
    ∀ as bs, as.mapM f = some bs → bs.all complete = true → List.Forall₂ R as bs
  | [], bs, computed, _ => by
      simp at computed
      subst bs
      exact List.Forall₂.nil
  | a :: as, bs, computed, allComplete => by
      rw [List.mapM_cons] at computed
      cases headComputed : f a with
      | none => simp [headComputed] at computed
      | some b =>
          cases tailComputed : as.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst bs
              simp only [List.all_cons, Bool.and_eq_true] at allComplete
              exact List.Forall₂.cons (sound a b headComputed allComplete.1)
                (mapM_structuralRealizations f complete R sound as tail tailComputed allComplete.2)

private theorem collectStructuralSourceForest
    (mol : RawMolecule) {sources : List CanonicalBranchNode}
    {keys : List CanonicalBranchKey}
    (relations : List.Forall₂ (fun source key =>
      ∃ tree, key.sourceTree? = some tree ∧
        CanonicalTreeStructurallyRealizes mol source tree) sources keys) :
    ∃ forest, canonicalSourceForest? keys = some forest ∧
      CanonicalForestStructurallyRealizes mol sources forest := by
  induction relations with
  | nil => exact ⟨.nil, rfl, .nil⟩
  | cons head tail inductionHypothesis =>
      obtain ⟨tree, treeStored, treeRealizes⟩ := head
      obtain ⟨forest, forestStored, forestRealizes⟩ := inductionHypothesis
      exact ⟨.cons tree forest,
        by simp [canonicalSourceForest?, treeStored, forestStored],
        .cons treeRealizes forestRealizes⟩

/-- Every successful complete execution of the width-unbounded compiler retains a recursive
source tree that realizes every molecular child occurrence exactly. -/
theorem buildCanonicalBranchKeyAuthoritative_structuralTree
    (mol : RawMolecule) :
    ∀ fuel node key,
    mol.buildCanonicalBranchKeyAuthoritative fuel node = some key →
      key.complete = true →
      ∃ tree, key.sourceTree? = some tree ∧
        CanonicalTreeStructurallyRealizes mol node tree := by
  intro fuel
  induction fuel with
  | zero =>
      intro node key computed complete
      unfold buildCanonicalBranchKeyAuthoritative at computed
      unfold canonicalRootKeyAuthoritative? at computed
      cases labelComputed : mol.canonicalRule1aLabelAuthoritative? node with
      | none => simp [labelComputed] at computed
      | some label =>
          simp [labelComputed] at computed
          subst key
          have terminal : mol.canonicalTerminal node = true := by
            simpa using complete
          refine ⟨.node node .nil, rfl,
            CanonicalTreeStructurallyRealizes.node node .nil ⟨label, labelComputed⟩ [] ?_ .nil⟩
          simp [mol.canonicalChildren_eq_nil_of_terminal node terminal]
  | succ fuel inductionHypothesis =>
      intro node key computed complete
      unfold buildCanonicalBranchKeyAuthoritative at computed
      by_cases terminal : mol.canonicalTerminal node = true
      · simp only [terminal, ↓reduceIte] at computed
        unfold canonicalRootKeyAuthoritative? at computed
        cases labelComputed : mol.canonicalRule1aLabelAuthoritative? node with
        | none => simp [labelComputed] at computed
        | some label =>
            simp [labelComputed] at computed
            subst key
            refine ⟨.node node .nil, rfl,
              CanonicalTreeStructurallyRealizes.node node .nil ⟨label, labelComputed⟩ [] ?_ .nil⟩
            simp [mol.canonicalChildren_eq_nil_of_terminal node terminal]
      · have terminalFalse : mol.canonicalTerminal node = false :=
          Bool.eq_false_of_not_eq_true terminal
        simp only [terminalFalse, Bool.false_eq_true, ↓reduceIte] at computed
        by_cases tooWide : authoritativeChildSlots < (mol.canonicalChildren node).length
        · simp [tooWide] at computed
        · simp only [tooWide, ↓reduceIte] at computed
          cases childrenComputed : (mol.canonicalChildren node).mapM
              (fun child => mol.buildCanonicalBranchKeyAuthoritative fuel child) with
          | none => simp [childrenComputed] at computed
          | some childKeys =>
              cases sortedComputed : sortCanonicalKeys? childKeys with
              | none => simp [childrenComputed, sortedComputed] at computed
              | some sorted =>
                  cases rootComputed : mol.canonicalRootKeyAuthoritative? node
                      (sorted.all fun child => child.complete) with
                  | none => simp [childrenComputed, sortedComputed, rootComputed] at computed
                  | some root =>
                      simp [childrenComputed, sortedComputed, rootComputed] at computed
                      subst key
                      have rootFacts :
                          root.complete = sorted.all (·.complete) ∧
                            root.sourceTree? = some (.node node .nil) ∧
                            ∃ label,
                              mol.canonicalRule1aLabelAuthoritative? node = some label := by
                        unfold canonicalRootKeyAuthoritative? at rootComputed
                        cases labelComputed : mol.canonicalRule1aLabelAuthoritative? node with
                        | none => simp [labelComputed] at rootComputed
                        | some label =>
                            simp [labelComputed] at rootComputed
                            subst root
                            exact ⟨rfl, rfl, label, rfl⟩
                      have sortedComplete : sorted.all (·.complete) = true := by
                        simpa [assembleCanonicalBranchKey, rootFacts.1] using complete
                      have sortedPerm : sorted.Perm childKeys :=
                        sortCanonicalKeys?_perm childKeys sorted sortedComputed
                      have childrenComplete : childKeys.all (·.complete) = true := by
                        rw [sortedPerm.all_eq] at sortedComplete
                        exact sortedComplete
                      have childRelations : List.Forall₂ (fun source childKey =>
                          ∃ tree, childKey.sourceTree? = some tree ∧
                            CanonicalTreeStructurallyRealizes mol source tree)
                          (mol.canonicalChildren node) childKeys := by
                        apply mapM_structuralRealizations
                          (fun child => mol.buildCanonicalBranchKeyAuthoritative fuel child)
                          CanonicalBranchKey.complete
                        intro child childKey childComputed childComplete
                        exact inductionHypothesis child childKey childComputed childComplete
                        exact childrenComputed
                        exact childrenComplete
                      have composed : Relation.Comp
                          (List.Forall₂ (fun source childKey =>
                            ∃ tree, childKey.sourceTree? = some tree ∧
                              CanonicalTreeStructurallyRealizes mol source tree))
                          List.Perm (mol.canonicalChildren node) sorted :=
                        ⟨childKeys, childRelations, sortedPerm.symm⟩
                      rw [List.forall₂_comp_perm_eq_perm_comp_forall₂] at composed
                      obtain ⟨sortedSources, sourcePerm, sortedRelations⟩ := composed
                      obtain ⟨forest, forestStored, forestRealizes⟩ :=
                        collectStructuralSourceForest mol sortedRelations
                      refine ⟨.node node forest, ?_,
                        CanonicalTreeStructurallyRealizes.node node forest rootFacts.2.2 sortedSources
                          sourcePerm.symm forestRealizes⟩
                      simp [assembleCanonicalBranchKey, rootFacts.2.1, forestStored]

/-- The public width-unbounded branch compiler therefore retains exact child occurrence coverage
at every address. -/
theorem branchCanonicalKeyAuthoritative?_rootedAt_childrenExact
    (mol : RawMolecule) (center ligand : ℕ) (key : CanonicalBranchKey)
    (computed : branchCanonicalKeyAuthoritative? mol center ligand = some key)
    (complete : key.complete = true) :
    key.RootedAt center ligand ∧ key.ChildrenExact mol := by
  unfold branchCanonicalKeyAuthoritative? at computed
  obtain ⟨tree, treeStored, realizes⟩ :=
    mol.buildCanonicalBranchKeyAuthoritative_structuralTree
      (2 * mol.atomCount + 2) (canonicalRoot center ligand) key computed complete
  have rooted : key.RootedAt center ligand := by
    unfold CanonicalBranchKey.RootedAt
    rw [key.sourceNodeAtAddress?_eq_tree_sourceAt tree treeStored]
    obtain ⟨children, treeEq⟩ := realizes.tree_eq_node
    subst tree
    rfl
  exact ⟨rooted, realizes.childrenExact mol key (canonicalRoot center ligand) tree treeStored⟩

theorem branchCanonicalKeyAuthoritative?_childrenExact
    (mol : RawMolecule) (center ligand : ℕ) (key : CanonicalBranchKey)
    (computed : branchCanonicalKeyAuthoritative? mol center ligand = some key)
    (complete : key.complete = true) : key.ChildrenExact mol :=
  (mol.branchCanonicalKeyAuthoritative?_rootedAt_childrenExact
    center ligand key computed complete).2

/-- Every source occurrence retained by a successful complete authoritative compilation has an
actual uncapped Rule-1a label; no default value is introduced at the proof boundary. -/
theorem branchCanonicalKeyAuthoritative?_rule1aLabelSupportedAt
    (mol : RawMolecule) (center ligand : ℕ) (key : CanonicalBranchKey)
    (computed : branchCanonicalKeyAuthoritative? mol center ligand = some key)
    (complete : key.complete = true) (address : List ℕ)
    (source : CanonicalBranchNode)
    (sourceAt : key.sourceNodeAtAddress? address = some source) :
    ∃ label, mol.canonicalRule1aLabelAuthoritative? source = some label := by
  unfold branchCanonicalKeyAuthoritative? at computed
  obtain ⟨tree, treeStored, realizes⟩ :=
    mol.buildCanonicalBranchKeyAuthoritative_structuralTree
      (2 * mol.atomCount + 2) (canonicalRoot center ligand) key computed complete
  rw [key.sourceNodeAtAddress?_eq_tree_sourceAt tree treeStored] at sourceAt
  exact realizes.rule1aLabelSupportedAt address sourceAt

/-- A successful complete authoritative branch compilation is a faithful exact expansion of the
physical molecular ligand graph.  Unlike the legacy discovery theorem, this certificate has no
global node-width cap and accepts exact uncapped mancude Rule-1a labels. -/
theorem branchCanonicalKeyAuthoritative?_faithfulExactExpansion
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (admitted : mol.Admissible)
    (computed : branchCanonicalKeyAuthoritative? mol center ligand = some key)
    (complete : key.complete = true)
    (rootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand) :
    RootedDigraph.FaithfulExactExpansion
      (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
      (key.toDeclarativeDigraph mol) := by
  have structural := mol.branchCanonicalKeyAuthoritative?_rootedAt_childrenExact
    center.val ligand.val key computed complete
  have hlocal := key.locallyAdmissibleExpansion_of_childrenExact
    mol center ligand admitted.1 structural.1 structural.2
  have multiplicities := key.atomChildMultiplicities_of_rootedAt_childrenExact
    mol center ligand admitted.1 admitted.2 structural.1 structural.2
  have atomChildren := key.atomBearingChildren_of_childrenExact
    mol center ligand admitted.1 structural.1 structural.2
  have distances := key.duplicateDistancesCorrect_of_childrenExact
    mol center ligand admitted.1 structural.1 structural.2
  exact RootedDigraph.faithfulExactExpansion_of_components
    (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
    (key.toDeclarativeDigraph mol) hlocal (key.declarativeAddressing mol)
    multiplicities rootBond atomChildren distances

end RawMolecule

/-! ## Proof-carrying authoritative branch execution -/

namespace AuthoritativeCIPDiscovery

/-- One successful complete execution of the uncapped authoritative branch compiler. -/
structure CompleteBranchDiscovery (mol : RawMolecule)
    (center : Fin mol.atomCount) (ligand : ℕ) where
  key : RawMolecule.CanonicalBranchKey
  accepted : branchCanonicalKeyAuthoritative? mol center.val ligand = some key
  complete : key.complete = true

namespace CompleteBranchDiscovery

/-- Execute the authoritative compiler and retain only a non-truncated result. -/
def discover? (mol : RawMolecule) (center : Fin mol.atomCount) (ligand : ℕ) :
    Option (CompleteBranchDiscovery mol center ligand) :=
  match computed : branchCanonicalKeyAuthoritative? mol center.val ligand with
  | none => none
  | some key =>
      if complete : key.complete = true then some ⟨key, computed, complete⟩ else none

@[simp] theorem discover?_eq_some
    {mol : RawMolecule} {center : Fin mol.atomCount} {ligand : ℕ}
    (discovery : CompleteBranchDiscovery mol center ligand) :
    discover? mol center ligand = some discovery := by
  unfold discover?
  split
  · rename_i computed
    have impossible : (none : Option RawMolecule.CanonicalBranchKey) = some discovery.key :=
      computed.symm.trans discovery.accepted
    simp at impossible
  · rename_i key computed
    have keyEq : key = discovery.key :=
      Option.some.inj (computed.symm.trans discovery.accepted)
    subst key
    split
    · congr
    · rename_i incomplete
      exact (incomplete discovery.complete).elim

theorem unique
    {mol : RawMolecule} {center : Fin mol.atomCount} {ligand : ℕ}
    (first second : CompleteBranchDiscovery mol center ligand) : first = second := by
  exact Option.some.inj ((discover?_eq_some first).symm.trans (discover?_eq_some second))

/-- Every retained physical authoritative branch realizes the complete independent molecular
digraph semantics, including exact duplicate multiplicity and root distance. -/
theorem faithfulExactExpansion
    {mol : RawMolecule} {center : Fin mol.atomCount} {ligandIndex : ℕ}
    (discovery : CompleteBranchDiscovery mol center ligandIndex)
    (ligand : Fin mol.atomCount) (ligandEq : ligand.val = ligandIndex)
    (admitted : mol.Admissible)
    (rootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand) :
    RootedDigraph.FaithfulExactExpansion
      (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
      (discovery.key.toDeclarativeDigraph mol) := by
  have accepted : branchCanonicalKeyAuthoritative? mol center.val ligand.val =
      some discovery.key := by
    simpa [ligandEq] using discovery.accepted
  exact mol.branchCanonicalKeyAuthoritative?_faithfulExactExpansion
    center ligand discovery.key admitted accepted discovery.complete rootBond

end CompleteBranchDiscovery

end AuthoritativeCIPDiscovery

end

end TetraStereo.OneCenter
