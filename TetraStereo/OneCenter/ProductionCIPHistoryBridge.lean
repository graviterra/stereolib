import TetraStereo.OneCenter.ProductionCIPFaithfulDistance

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

theorem List.mem_of_head?_eq_some {alpha : Type*} {value : alpha} {values : List alpha}
    (hhead : values.head? = some value) : value ∈ values := by
  cases values with
  | nil => simp at hhead
  | cons head tail =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst head
      exact List.mem_cons_self

namespace RawMolecule

theorem canonicalChildren_parent_eq
    (mol : RawMolecule) (parent child : CanonicalBranchNode)
    (hchild : child ∈ mol.canonicalChildren parent) :
    child.parent = parent.atom := by
  unfold canonicalChildren at hchild
  by_cases hleaf : parent.forcedLeaf
  · simp [hleaf] at hchild
  · simp only [hleaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hchild
    obtain ⟨copy, _, rfl⟩ := hchild
    rfl

end RawMolecule

namespace RawMolecule.CanonicalBranchKey

theorem externalParent_mem_source_history
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source) :
    center.1 ∈ source.history := by
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
      simp [RawMolecule.canonicalRoot]
  | tail hparent hchild inductionHypothesis =>
      intro source hsource
      rcases hcomplete _ with ⟨parentSource, hparentSource⟩
      rcases hexact _ parentSource hparentSource with ⟨equivalence, hlookup⟩
      let generated := (mol.canonicalChildren parentSource).get
        (equivalence ⟨_, hchild⟩)
      have hgeneratedMem : generated ∈ mol.canonicalChildren parentSource :=
        List.get_mem _ _
      have hsourceEq : source = generated :=
        Option.some.inj (hsource.symm.trans (hlookup ⟨_, hchild⟩))
      subst source
      rw [mol.canonicalChildren_history parentSource generated hgeneratedMem]
      exact List.mem_cons_of_mem _
        (inductionHypothesis parentSource hparentSource)

theorem ancestor_source_atom_mem_history
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (ancestor node : key.HierarchyNode)
    (ancestorSource source : CanonicalBranchNode)
    (hancestorSource : key.sourceNodeAtAddress? ancestor.1 = some ancestorSource)
    (hsource : key.sourceNodeAtAddress? node.1 = some source)
    (hpath : Relation.TransGen key.HierarchyChild ancestor node) :
    ancestorSource.atom ∈ source.history := by
  have hcomplete := key.sourceComplete_of_root_and_childrenExact mol
    (RawMolecule.canonicalRoot center ligand) hroot hexact
  have hhead := key.source_history_head_of_rootedAt_childrenExact mol
    center ligand hroot hexact ancestor ancestorSource hancestorSource
  induction hpath generalizing source with
  | single hedge =>
      have hchildren := key.childrenSound_of_childrenExact mol hexact
      have hgenerated := hchildren _ _ ancestorSource source hedge
        hancestorSource hsource
      rw [mol.canonicalChildren_history ancestorSource source hgenerated]
      exact List.mem_cons_of_mem _ (List.mem_of_head?_eq_some hhead)
  | @tail parent node hpath hedge inductionHypothesis =>
      rcases hcomplete parent with ⟨parentSource, hparentSource⟩
      have hparentMem := inductionHypothesis parentSource hparentSource
      have hchildren := key.childrenSound_of_childrenExact mol hexact
      have hgenerated := hchildren parent node parentSource source hedge
        hparentSource hsource
      rw [mol.canonicalChildren_history parentSource source hgenerated]
      exact List.mem_cons_of_mem _ hparentMem

theorem source_history_mem_iff_self_or_branchAncestorAtom
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source)
    (atom : Fin mol.atomCount) :
    atom.1 ∈ source.history ↔
      atom.1 = source.atom ∨
        RootedDigraph.BranchAncestorAtom (key.toDeclarativeDigraph mol) center atom node := by
  have hcomplete := key.sourceComplete_of_root_and_childrenExact mol
    (RawMolecule.canonicalRoot center ligand) hroot hexact
  have hchildren := key.childrenSound_of_childrenExact mol hexact
  have hcoherent := key.sourceCoherent_of_root_and_childrenExact mol center ligand
    hwellFormed hroot hexact
  constructor
  · intro hmem
    have hreverse : atom.1 ∈ source.history.reverse := List.mem_reverse.mpr hmem
    rcases List.mem_iff_getElem.mp hreverse with ⟨index, hindexBound, hindex⟩
    have hindex? : source.history.reverse[index]? = some atom.1 := by
      rw [List.getElem?_eq_getElem hindexBound, hindex]
    have hrealized := key.history_index_realized_of_rootedAt_childrenExact mol
      center ligand hroot hexact node source hsource index atom.1 hindex?
    rcases hrealized with hcenter | hselfOrAncestor
    · right
      left
      apply Fin.ext
      exact hcenter.2
    · rcases hselfOrAncestor with hself | hancestor
      · exact Or.inl hself.2
      · right
        right
        rcases hancestor with ⟨ancestor, hpath, ancestorSource,
            hancestorSource, hatom, _⟩
        refine ⟨ancestor, hpath, ?_⟩
        rcases Relation.TransGen.head'_iff.mp hpath with ⟨next, hnext, _⟩
        rcases hcomplete next with ⟨nextSource, hnextSource⟩
        have hreal := key.parentSource_real_of_hierarchyChild mol hchildren
          ancestor next ancestorSource nextSource hnext hancestorSource hnextSource
        have hancestorCoherent := hcoherent ancestor ancestorSource hancestorSource
        have hbound : ancestorSource.atom < mol.atomCount := by
          simpa [hreal] using hancestorCoherent.2
        change (key.declarativeLabel mol ancestor).atom? = some atom
        rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol ancestor ancestorSource
          hancestorSource, hreal]
        have hatomEq : (⟨ancestorSource.atom, hbound⟩ : Fin mol.atomCount) = atom := by
          apply Fin.ext
          exact hatom.symm
        rw [← hatomEq]
        simp [atomFin?, hbound]
  · intro h
    rcases h with hself | hbranch
    · rw [hself]
      exact List.mem_of_head?_eq_some
        (key.source_history_head_of_rootedAt_childrenExact mol center ligand
          hroot hexact node source hsource)
    · rcases hbranch with hcenter | hancestor
      · have hatomCenter : atom.1 = center.1 := congrArg Fin.val hcenter
        rw [hatomCenter]
        exact key.externalParent_mem_source_history mol center ligand hroot hexact
          node source hsource
      · rcases hancestor with ⟨ancestor, hpath, hlabel⟩
        rcases hcomplete ancestor with ⟨ancestorSource, hancestorSource⟩
        have hfin := key.atomFin_eq_of_declarativeLabel_atom_eq mol ancestor
          ancestorSource hancestorSource atom hlabel
        have hatom : ancestorSource.atom = atom.1 := by
          unfold atomFin? at hfin
          split at hfin
          next hbound =>
            exact congrArg Fin.val (Option.some.inj hfin)
          next hbound => simp at hfin
        rw [← hatom]
        exact key.ancestor_source_atom_mem_history mol center ligand hroot hexact
          ancestor node ancestorSource source hancestorSource hsource hpath

theorem source_history_mem_iff_branchAncestorAtom_of_adjacent
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source)
    (parentAtom atom : Fin mol.atomCount)
    (hparentLabel : (key.declarativeLabel mol node).atom? = some parentAtom)
    (hadjacent : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj parentAtom atom) :
    atom.1 ∈ source.history ↔
      RootedDigraph.BranchAncestorAtom (key.toDeclarativeDigraph mol) center atom node := by
  rw [key.source_history_mem_iff_self_or_branchAncestorAtom mol center ligand
    hwellFormed hroot hexact node source hsource atom]
  have hfin := key.atomFin_eq_of_declarativeLabel_atom_eq mol node source hsource
    parentAtom hparentLabel
  have hsourceEq : source.atom = parentAtom.1 := by
    unfold atomFin? at hfin
    split at hfin
    next hbound => exact congrArg Fin.val (Option.some.inj hfin)
    next hbound => simp at hfin
  constructor
  · intro h
    rcases h with hself | hbranch
    · have hatomEq : atom = parentAtom := by
        apply Fin.ext
        exact hself.trans hsourceEq
      subst atom
      simp [MoleculeGraph.Adj] at hadjacent
    · exact hbranch
  · exact Or.inr

theorem source_parent_eq_iff_suppressedParentAtom
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source)
    (atom : Fin mol.atomCount) :
    atom.1 = source.parent ↔
      RootedDigraph.SuppressedParentAtom
        (key.toDeclarativeDigraph mol) center atom node := by
  have hcomplete := key.sourceComplete_of_root_and_childrenExact mol
    (RawMolecule.canonicalRoot center ligand) hroot hexact
  have hchildren := key.childrenSound_of_childrenExact mol hexact
  have hcoherent := key.sourceCoherent_of_root_and_childrenExact mol center ligand
    hwellFormed hroot hexact
  let addressing := key.declarativeAddressing mol
  constructor
  · intro hatomParent
    by_cases hnodeRoot : node = (key.toDeclarativeDigraph mol).root
    · left
      refine ⟨hnodeRoot, ?_⟩
      have haddress : node.1 = [] := congrArg Subtype.val hnodeRoot
      have hsourceRoot : source = RawMolecule.canonicalRoot center ligand := by
        apply Option.some.inj
        exact hsource.symm.trans (by simpa [haddress] using hroot)
      apply Fin.ext
      simpa [hsourceRoot, RawMolecule.canonicalRoot] using hatomParent
    · right
      obtain ⟨parent, hedge, _⟩ := addressing.existsUnique_parent node hnodeRoot
      change key.HierarchyChild parent node at hedge
      rcases hcomplete parent with ⟨parentSource, hparentSource⟩
      have hgenerated := hchildren parent node parentSource source hedge
        hparentSource hsource
      have hparentEq := mol.canonicalChildren_parent_eq parentSource source hgenerated
      have hreal := key.parentSource_real_of_hierarchyChild mol hchildren
        parent node parentSource source hedge hparentSource hsource
      have hparentCoherent := hcoherent parent parentSource hparentSource
      have hbound : parentSource.atom < mol.atomCount := by
        simpa [hreal] using hparentCoherent.2
      refine ⟨parent, ?_, ?_⟩
      · exact hedge
      · change (key.declarativeLabel mol parent).atom? = some atom
        rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol parent parentSource
          hparentSource, hreal]
        have hatomEq : (⟨parentSource.atom, hbound⟩ : Fin mol.atomCount) = atom := by
          apply Fin.ext
          exact (hatomParent.trans hparentEq).symm
        rw [← hatomEq]
        simp [atomFin?, hbound]
  · intro hsuppressed
    rcases hsuppressed with hrootCase | hparentCase
    · rcases hrootCase with ⟨hnodeRoot, hatomCenter⟩
      have haddress : node.1 = [] := congrArg Subtype.val hnodeRoot
      have hsourceRoot : source = RawMolecule.canonicalRoot center ligand := by
        apply Option.some.inj
        exact hsource.symm.trans (by simpa [haddress] using hroot)
      simp [hsourceRoot, RawMolecule.canonicalRoot, hatomCenter]
    · rcases hparentCase with ⟨parent, hedge, hparentLabel⟩
      change key.HierarchyChild parent node at hedge
      rcases hcomplete parent with ⟨parentSource, hparentSource⟩
      have hgenerated := hchildren parent node parentSource source hedge
        hparentSource hsource
      have hparentEq := mol.canonicalChildren_parent_eq parentSource source hgenerated
      have hfin := key.atomFin_eq_of_declarativeLabel_atom_eq mol parent
        parentSource hparentSource atom hparentLabel
      have hsourceAtomEq : parentSource.atom = atom.1 := by
        unfold atomFin? at hfin
        split at hfin
        next hbound => exact congrArg Fin.val (Option.some.inj hfin)
        next hbound => simp at hfin
      exact hsourceAtomEq.symm.trans hparentEq.symm

end RawMolecule.CanonicalBranchKey

end
end OneCenter
end TetraStereo
