import TetraStereo.OneCenter.ProductionCIPExactExpansion

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

namespace RawMolecule

/-!
# Faithfulness of production duplicate-root distances

The production history begins with the current atom and ends with the external stereocenter.
This module proves that its Rule-1b payloads agree with the independent declarative addressing:
the external stereocenter occupies distance zero, and every other ring-duplicate target is a
represented strict ancestor at the recorded sphere.
-/

theorem firstNatIndex?_eq_some_of_mem (target : ℕ) :
    ∀ values : List ℕ, target ∈ values →
      ∃ index, firstNatIndex? target values = some index
  | [], hmem => by simp at hmem
  | value :: values, hmem => by
      by_cases heq : value = target
      · exact ⟨0, by simp [firstNatIndex?, heq]⟩
      · have htail : target ∈ values := by
          have hcases : target = value ∨ target ∈ values := by simpa using hmem
          exact hcases.resolve_left (fun hhead => heq hhead.symm)
        obtain ⟨index, hindex⟩ := firstNatIndex?_eq_some_of_mem target values htail
        exact ⟨index + 1, by simp [firstNatIndex?, heq, hindex]⟩

theorem canonicalHistoryDistance_eq_index_of_mem
    (node : CanonicalBranchNode) (atom : ℕ) (hmem : atom ∈ node.history) :
    ∃ index, firstNatIndex? atom node.history.reverse = some index ∧
      canonicalHistoryDistance node atom = index := by
  obtain ⟨index, hindex⟩ := firstNatIndex?_eq_some_of_mem atom
    node.history.reverse (List.mem_reverse.mpr hmem)
  exact ⟨index, hindex, by simp [canonicalHistoryDistance, hindex]⟩

/-- A generated ring duplicate records membership in the parent history, the exact history
distance, and an atom distinct from the parent itself. -/
theorem canonicalChildren_ringDuplicate_data
    (mol : RawMolecule) (parent child : CanonicalBranchNode)
    (hparentHead : parent.history.head? = some parent.atom)
    (hchild : child ∈ mol.canonicalChildren parent) (distance : ℕ)
    (hprovenance : child.provenance =
      CanonicalNodeProvenance.ringDuplicate distance) :
    child.atom ∈ parent.history ∧
      distance = canonicalHistoryDistance parent child.atom ∧
      child.atom ≠ parent.atom := by
  unfold canonicalChildren at hchild
  by_cases hleaf : parent.forcedLeaf
  · simp [hleaf] at hchild
  · simp only [hleaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hchild
    obtain ⟨copy, hcopy, rfl⟩ := hchild
    by_cases hmultiple : copy.2 != 0
    · simp [hmultiple] at hprovenance
    · have hcopyZero : copy.2 = 0 := by simpa using hmultiple
      by_cases hring : copy.1 ∈ parent.history
      · simp [hmultiple, hring] at hprovenance
        have hpositive : 0 < mol.canonicalBondOrder parent copy.1 := by
          obtain ⟨bond, hbond, hendpoints, hindex⟩ :=
            mol.canonicalChildCopies_source parent copy hcopy
          simpa [hcopyZero] using hindex
        have hrawPositive : 0 < mol.bondOrder parent.atom copy.1 :=
          mol.canonicalBondOrder_pos_imp_bondOrder_pos parent copy.1
            hparentHead hpositive
        refine ⟨hring, hprovenance.symm, ?_⟩
        change copy.1 ≠ parent.atom
        intro heq
        rw [heq] at hrawPositive
        have hzero := mol.bondOrder_self parent.atom
        exact (Nat.ne_of_gt hrawPositive) hzero
      · simp [hmultiple, hring] at hprovenance

end RawMolecule

namespace RawMolecule.CanonicalBranchKey

/-- Every source reached through exact production children retains a history headed by its atom. -/
theorem source_history_head_of_rootedAt_childrenExact
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source) :
    source.history.head? = some source.atom := by
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
      rfl
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
      exact mol.canonicalChildren_history_head parentSource generated hgeneratedMem

/-- An indexed production-history entry is exactly the external stereocenter, the current source,
or a represented strict ancestor.  The index from the reversed history is its declarative sphere. -/
theorem history_index_realized_of_rootedAt_childrenExact
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source) :
    ∀ index atom, source.history.reverse[index]? = some atom →
      (index = 0 ∧ atom = center.1) ∨
      (index = node.1.length + 1 ∧ atom = source.atom) ∨
      ∃ ancestor : key.HierarchyNode,
        Relation.TransGen key.HierarchyChild ancestor node ∧
          ∃ ancestorSource : CanonicalBranchNode,
            key.sourceNodeAtAddress? ancestor.1 = some ancestorSource ∧
              atom = ancestorSource.atom ∧
              index = ancestor.1.length + 1 := by
  have hcomplete := key.sourceComplete_of_root_and_childrenExact mol
    (RawMolecule.canonicalRoot center ligand) hroot hexact
  have hreachable := (key.toDeclarativeDigraph mol).reachable node
  change Relation.ReflTransGen key.HierarchyChild
    ⟨[], key.nil_mem_hierarchyAddresses⟩ node at hreachable
  revert source
  induction hreachable with
  | refl =>
      intro source hsource index atom hindex
      have hsourceEq : source = RawMolecule.canonicalRoot center ligand :=
        Option.some.inj (hsource.symm.trans hroot)
      subst source
      have hibound : index < 2 := by
        have := List.getElem?_eq_some_iff.mp hindex
        simpa [RawMolecule.canonicalRoot] using this.1
      have hi : index = 0 ∨ index = 1 := by omega
      rcases hi with rfl | rfl
      · left
        exact ⟨rfl, by simpa [RawMolecule.canonicalRoot] using hindex.symm⟩
      · right; left
        exact ⟨rfl, by simpa [RawMolecule.canonicalRoot] using hindex.symm⟩
  | @tail parent node hpath hchild inductionHypothesis =>
      intro source hsource index atom hindex
      rcases hcomplete parent with ⟨parentSource, hparentSource⟩
      have hparentDepth := key.source_depth_eq_address_length_succ mol center ligand
        hroot hexact parent parentSource hparentSource
      rcases hexact parent parentSource hparentSource with ⟨equivalence, hlookup⟩
      let generated := (mol.canonicalChildren parentSource).get
        (equivalence ⟨node, hchild⟩)
      have hgeneratedMem : generated ∈ mol.canonicalChildren parentSource :=
        List.get_mem _ _
      have hsourceEq : source = generated :=
        Option.some.inj (hsource.symm.trans (hlookup ⟨node, hchild⟩))
      subst source
      have hparentLength : parentSource.history.length = parent.1.length + 2 := by
        unfold CanonicalBranchNode.depth at hparentDepth
        omega
      rw [mol.canonicalChildren_history parentSource generated hgeneratedMem,
        List.reverse_cons, List.getElem?_append] at hindex
      by_cases hibefore : index < parentSource.history.reverse.length
      · simp only [hibefore, ↓reduceIte] at hindex
        rcases inductionHypothesis parentSource hparentSource index atom hindex with
          hcenter | hparentOrAncestor
        · exact Or.inl hcenter
        · rcases hparentOrAncestor with hparentSelf | hancestor
          · right; right
            refine ⟨parent, Relation.TransGen.single hchild, parentSource,
              hparentSource, hparentSelf.2, hparentSelf.1⟩
          · rcases hancestor with ⟨ancestor, hancestorPath, ancestorSource,
              hancestorSource, hatom, hdistance⟩
            right; right
            exact ⟨ancestor, hancestorPath.tail hchild, ancestorSource,
              hancestorSource, hatom, hdistance⟩
      · simp only [hibefore, ↓reduceIte] at hindex
        have htailBound : index - parentSource.history.reverse.length < 1 :=
          (List.getElem?_eq_some_iff.mp hindex).1
        have hindexEq : index = parentSource.history.length := by
          simp only [List.length_reverse] at hibefore htailBound
          omega
        have hatom : atom = generated.atom := by
          subst index
          simpa using hindex.symm
        right; left
        rcases hchild with ⟨slot, haddress⟩
        constructor
        · rw [haddress]
          simp only [List.length_append, List.length_singleton]
          omega
        · exact hatom

/-- Ring-duplicate payloads identify either the external stereocenter at distance zero or the
represented strict ancestor that carries the duplicated atom. -/
theorem ringDuplicate_distance_correct_of_childrenExact
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol) :
    ∀ parent child, key.HierarchyChild parent child → ∀ atom distance,
      key.declarativeLabel mol child =
          ⟨some atom, NodeProvenance.ringDuplicate distance⟩ →
        (atom = center ∧ distance = 0) ∨
          ∃ ancestor, Relation.TransGen key.HierarchyChild ancestor parent ∧
            (key.declarativeLabel mol ancestor).atom? = some atom ∧
            distance = ((key.declarativeAddressing mol).address ancestor).length + 1 := by
  have hcomplete := key.sourceComplete_of_root_and_childrenExact mol
    (RawMolecule.canonicalRoot center ligand) hroot hexact
  have hchildren := key.childrenSound_of_childrenExact mol hexact
  have hcoherent := key.sourceCoherent_of_root_and_childrenExact mol center ligand
    hwellFormed hroot hexact
  intro parent child hedge atom distance hlabel
  rcases hcomplete parent with ⟨parentSource, hparentSource⟩
  rcases hcomplete child with ⟨childSource, hchildSource⟩
  have hgenerated := hchildren parent child parentSource childSource hedge
    hparentSource hchildSource
  have hparentHead := key.source_history_head_of_rootedAt_childrenExact mol
    center ligand hroot hexact parent parentSource hparentSource
  have hchildCoherent := hcoherent child childSource hchildSource
  have hsourceProvenance : childSource.provenance =
      CanonicalNodeProvenance.ringDuplicate distance := by
    rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol child childSource hchildSource]
      at hlabel
    cases hp : childSource.provenance <;>
      simp [hp, declarativeProvenance] at hlabel ⊢
    exact hlabel.2
  have hchildBound : childSource.atom < mol.atomCount := by
    simpa [hsourceProvenance] using hchildCoherent.2
  have hatomFin : (⟨childSource.atom, hchildBound⟩ : Fin mol.atomCount) = atom := by
    have hlabelAtom : (key.declarativeLabel mol child).atom? = some atom := by
      rw [hlabel]
    have hfin := key.atomFin_eq_of_declarativeLabel_atom_eq mol child childSource
      hchildSource atom hlabelAtom
    have hsome : some (⟨childSource.atom, hchildBound⟩ : Fin mol.atomCount) = some atom := by
      simpa [atomFin?, hchildBound] using hfin
    exact Option.some.inj hsome
  obtain ⟨hhistory, hdistance, hneParent⟩ :=
    mol.canonicalChildren_ringDuplicate_data parentSource childSource hparentHead
      hgenerated distance hsourceProvenance
  obtain ⟨index, hfirstIndex, hcanonicalDistance⟩ :=
    RawMolecule.canonicalHistoryDistance_eq_index_of_mem parentSource childSource.atom hhistory
  have hhistoryGet := RawMolecule.firstNatIndex?_eq_some_imp_getElem?
    childSource.atom parentSource.history.reverse index hfirstIndex
  have hrealized := key.history_index_realized_of_rootedAt_childrenExact mol
    center ligand hroot hexact parent parentSource hparentSource
      index childSource.atom hhistoryGet
  have hdistanceIndex : distance = index := hdistance.trans hcanonicalDistance
  rcases hrealized with hcenter | hselfOrAncestor
  · left
    constructor
    · apply Fin.ext
      exact hatomFin.symm ▸ hcenter.2
    · exact hdistanceIndex.trans hcenter.1
  · rcases hselfOrAncestor with hself | hancestor
    · exact (hneParent hself.2).elim
    · rcases hancestor with ⟨ancestor, hancestorPath, ancestorSource,
        hancestorSource, hatomSource, hindexDistance⟩
      right
      refine ⟨ancestor, hancestorPath, ?_, ?_⟩
      · rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol ancestor ancestorSource
          hancestorSource]
        have hancestorCoherent := hcoherent ancestor ancestorSource hancestorSource
        rcases Relation.TransGen.head'_iff.mp hancestorPath with
          ⟨next, hnext, hrest⟩
        rcases hcomplete next with ⟨nextSource, hnextSource⟩
        have hreal := key.parentSource_real_of_hierarchyChild mol hchildren
          ancestor next ancestorSource nextSource hnext hancestorSource hnextSource
        have hancestorBound : ancestorSource.atom < mol.atomCount := by
          simpa [hreal] using hancestorCoherent.2
        have hancestorAtomFin :
            (⟨ancestorSource.atom, hancestorBound⟩ : Fin mol.atomCount) = atom := by
          apply Fin.ext
          exact hatomSource.symm.trans (congrArg Fin.val hatomFin)
        rw [← hancestorAtomFin]
        rw [hreal]
        simp [atomFin?, hancestorBound]
      · exact hdistanceIndex.trans hindexDistance

/-- The public production addressing satisfies the complete independent Rule-1b distance
semantics, including ring closure to the external stereocenter. -/
theorem duplicateDistancesCorrect_of_childrenExact
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol) :
    RootedDigraph.DuplicateDistancesCorrect (key.toDeclarativeDigraph mol) center
      (key.declarativeAddressing mol) := by
  intro parent child hedge
  change key.HierarchyChild parent child at hedge
  cases hlabel : (key.toDeclarativeDigraph mol).label child with
  | mk atom? provenance =>
      cases provenance with
      | realAtom => trivial
      | multipleBondDuplicate distance =>
          exact key.multipleBondDuplicate_distance_correct_of_childrenExact mol
            center ligand hroot hexact parent child hedge distance (by
              have hp := congrArg NodeLabel.provenance hlabel
              simpa [toDeclarativeDigraph] using hp)
      | ringDuplicate distance =>
          cases atom? with
          | none =>
              have hatomBearing := key.atomBearingChildren_of_childrenExact mol
                center ligand hwellFormed hroot hexact parent child hedge
              rcases hatomBearing with ⟨atom, hatom⟩
              rw [hlabel] at hatom
              simp at hatom
          | some atom =>
              simpa [toDeclarativeDigraph] using
                key.ringDuplicate_distance_correct_of_childrenExact mol center ligand
                  hwellFormed hroot hexact parent child hedge atom distance (by
                    simpa [toDeclarativeDigraph] using hlabel)
      | phantom distance => trivial
      | lonePair => trivial
      | auxiliary => trivial

end RawMolecule.CanonicalBranchKey

end
end OneCenter
end TetraStereo
