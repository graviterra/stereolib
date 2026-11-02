import TetraStereo.OneCenter.LocalizedAcyclicRerootNeighborCorrespondence
import TetraStereo.OneCenter.OfficialHierarchicalDigraph
import TetraStereo.KernelOnly

set_option autoImplicit false































































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput)

/-! ## The automorphism relation on actual reroot cursors -/

/-- Physical automorphism correspondence between two actual reroot cursors with the same fixed
original root.  The two cursors are related when their occurrences keep the original root and
their physical current atoms are `e`-related, and when the incoming cut is absent on both sides or
present on both sides with `e`-related physical current atoms.  The relation stores no desired
child list, depth, or frame; those are derived below. -/
structure LocalizedAutCursorCorrespondence
    {fuel : Nat}
    (e : input.moleculeGraph.Aut)
    (root : input.Atom)
    (source target : input.LocalizedRerootCursor fuel) : Prop where
  /-- The source occurrence keeps the fixed original root. -/
  source_root : source.occurrence.1.root = root
  /-- The target occurrence keeps the fixed original root. -/
  target_root : target.occurrence.1.root = root
  /-- The physical current atoms of the two cursors are related by the automorphism. -/
  current_maps :
    ∀ {a b : input.Atom},
      source.occurrence.1.node.current? = some a →
        target.occurrence.1.node.current? = some b →
          b = (e : Equiv.Perm input.Atom) a
  /-- The incoming cut is absent on both sides or present on both sides. -/
  previous_none : source.previous? = none ↔ target.previous? = none
  /-- The two incoming occurrences keep the original root and have `e`-related current atoms. -/
  previous_maps :
    ∀ {p q : input.LocalizedCIPOccurrence fuel},
      source.previous? = some p →
        target.previous? = some q →
          p.1.root = root ∧
            q.1.root = root ∧
              ∀ {a b : input.Atom},
                p.1.node.current? = some a →
                  q.1.node.current? = some b →
                    b = (e : Equiv.Perm input.Atom) a

/-- The correspondence is symmetric, with the inverse automorphism and the two cursors exchanged.
This is what lets the child correspondence be used in both directions without reproving the
physical-neighbor step. -/
theorem localizedAutCursorCorrespondence_symm
    {fuel : Nat} {e : input.moleculeGraph.Aut} {root : input.Atom}
    {source target : input.LocalizedRerootCursor fuel}
    (correspondence : LocalizedAutCursorCorrespondence input e root source target) :
    LocalizedAutCursorCorrespondence input e⁻¹ root target source where
  source_root := correspondence.target_root
  target_root := correspondence.source_root
  current_maps := by
    intro a b ha hb
    have mapped : a = (e : Equiv.Perm input.Atom) b := correspondence.current_maps hb ha
    have coefficient :
        ((e⁻¹ : input.moleculeGraph.Aut) : Equiv.Perm input.Atom) =
          ((e : Equiv.Perm input.Atom))⁻¹ := by
      simp
    rw [coefficient, mapped]
    exact (Equiv.symm_apply_apply (e : Equiv.Perm input.Atom) b).symm
  previous_none := correspondence.previous_none.symm
  previous_maps := by
    intro p q hp hq
    obtain ⟨qRoot, pRoot, atomMaps⟩ := correspondence.previous_maps hq hp
    refine ⟨pRoot, qRoot, ?_⟩
    intro a b ha hb
    have mapped : a = (e : Equiv.Perm input.Atom) b := atomMaps hb ha
    have coefficient :
        ((e⁻¹ : input.moleculeGraph.Aut) : Equiv.Perm input.Atom) =
          ((e : Equiv.Perm input.Atom))⁻¹ := by
      simp
    rw [coefficient, mapped]
    exact (Equiv.symm_apply_apply (e : Equiv.Perm input.Atom) b).symm

/-! ## Atom-bearing carrier occurrences -/



theorem occurrence_current_exists
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel) :
    ∃ atom : input.Atom, occurrence.1.node.current? = some atom :=
  Option.isSome_iff_exists.mp
    (input.declarativeLocalizedOccurrence_node_current_isSome
      ((input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2))

/-! ## (1) Official atom-label covariance -/

/-- **Official node atom-label covariance.**  Related actual cursors have equal
`officialNodeAtomLabel` under the physical automorphism.  Both carrier occurrences are real path
nodes, so both labels are `rawCIPAtomLabel` of the current atom, and `e` preserves atomic number
and mass. -/
theorem officialNodeAtomLabel_eq_of_correspondence
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} {e : input.moleculeGraph.Aut} {root : input.Atom}
    {source target : input.LocalizedRerootCursor fuel}
    (correspondence : LocalizedAutCursorCorrespondence input e root source target)
    {a b : input.Atom}
    (sourceCurrent : source.occurrence.1.node.current? = some a)
    (targetCurrent : target.occurrence.1.node.current? = some b) :
    input.moleculeGraph.officialNodeAtomLabel source.occurrence.1.node =
      input.moleculeGraph.officialNodeAtomLabel target.occurrence.1.node := by
  have sourceProvenance :
      source.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
    input.carrierOccurrence_provenance_real singleBonded acyclic source.occurrence
  have targetProvenance :
      target.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
    input.carrierOccurrence_provenance_real singleBonded acyclic target.occurrence
  have mapped : b = (e : Equiv.Perm input.Atom) a :=
    correspondence.current_maps sourceCurrent targetCurrent
  simp only [MoleculeGraph.officialNodeAtomLabel, sourceCurrent, targetCurrent,
    sourceProvenance, targetProvenance, mapped]
  simp [MoleculeGraph.rawCIPAtomLabel]

/-! ## (2) Stored Rule-1b root-distance covariance -/

/-- **History-length covariance from the actual simple physical paths.**  The stored history of a
related pair of actual carrier occurrences has the same length.  The source history is the
reverse support of the actual simple physical path from the original root; mapping that path
along the physical automorphism, correcting its endpoints with `Walk.copy` using the fixed root,
and comparing with the target's actual simple path by acyclicity yields the same simple walk, so
the supports and hence the stored histories have equal length. -/
theorem node_history_length_eq_of_correspondence
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} {e : input.moleculeGraph.Aut} {root : input.Atom}
    (rootFixed : (e : Equiv.Perm input.Atom) root = root)
    {source target : input.LocalizedRerootCursor fuel}
    (correspondence : LocalizedAutCursorCorrespondence input e root source target)
    {a b : input.Atom}
    (sourceCurrent : source.occurrence.1.node.current? = some a)
    (targetCurrent : target.occurrence.1.node.current? = some b) :
    source.occurrence.1.node.history.length = target.occurrence.1.node.history.length := by
  -- Actual real simple paths out of the original roots of the two occurrences.
  obtain ⟨a', p, aObserved, _aHead, _aProvenance, pPath, pSupport, _aPenultimate⟩ :=
    input.carrierOccurrence_realPath singleBonded acyclic source.occurrence
  obtain ⟨b', q, bObserved, _bHead, _bProvenance, qPath, qSupport, _bPenultimate⟩ :=
    input.carrierOccurrence_realPath singleBonded acyclic target.occurrence
  have aEq : a' = a := Option.some.inj (aObserved.symm.trans sourceCurrent)
  have bEq : b' = b := Option.some.inj (bObserved.symm.trans targetCurrent)
  have mapped : b = (e : Equiv.Perm input.Atom) a :=
    correspondence.current_maps sourceCurrent targetCurrent
  -- The physical automorphism as a graph homomorphism of the underlying simple graph.
  let hom : input.moleculeGraph.underlyingSimpleGraph →g
      input.moleculeGraph.underlyingSimpleGraph :=
    { toFun := fun v => (e : Equiv.Perm input.Atom) v
      map_rel' := by
        intro u v adjacent
        exact (MoleculeGraph.Aut.adj_iff (m := input.moleculeGraph) e u v).2 adjacent }
  have homInjective : Function.Injective hom := by
    intro u v h
    exact (e : Equiv.Perm input.Atom).injective h
  -- Endpoints: the fixed original root and the mapped current atom.
  have startEq : (e : Equiv.Perm input.Atom) source.occurrence.1.root = root := by
    rw [correspondence.source_root, rootFixed]
  have finishEq : (e : Equiv.Perm input.Atom) a' = b' := by
    rw [aEq, bEq, ← mapped]
  -- The mapped source path, corrected to start at the fixed root and end at the target atom.
  let mappedWalk : input.moleculeGraph.underlyingSimpleGraph.Walk root b' :=
    SimpleGraph.Walk.copy (p.map hom) startEq finishEq
  have mappedWalkPath : mappedWalk.IsPath :=
    (SimpleGraph.Walk.isPath_copy (p.map hom) startEq finishEq).2
      (SimpleGraph.Walk.map_isPath_of_injective
        (f := hom) (p := p) homInjective pPath)
  -- The target's actual simple path, corrected to start at the fixed root.
  let targetWalk : input.moleculeGraph.underlyingSimpleGraph.Walk root b' :=
    SimpleGraph.Walk.copy q correspondence.target_root rfl
  have targetWalkPath : targetWalk.IsPath :=
    (SimpleGraph.Walk.isPath_copy q correspondence.target_root rfl).2 qPath
  -- Acyclicity forces the two simple walks to coincide.
  have pathsEq := input.moleculeGraph.acyclic_path_unique acyclic
    (⟨mappedWalk, mappedWalkPath⟩ :
      input.moleculeGraph.underlyingSimpleGraph.Path root b')
    (⟨targetWalk, targetWalkPath⟩ :
      input.moleculeGraph.underlyingSimpleGraph.Path root b')
  have walksEq : mappedWalk = targetWalk := congrArg Subtype.val pathsEq
  have supportsEq : mappedWalk.support = targetWalk.support :=
    congrArg (fun walk => walk.support) walksEq
  have mappedSupportLength : mappedWalk.support.length = p.support.length := by
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.length_map]
  have targetSupportLength : targetWalk.support.length = q.support.length := by
    rw [SimpleGraph.Walk.support_copy]
  have supportsLengthEq : p.support.length = q.support.length := by
    have sameLength := congrArg List.length supportsEq
    omega
  have sourceHistoryLength :
      p.support.length = source.occurrence.1.node.history.length := by
    rw [← pSupport, List.length_reverse]
  have targetHistoryLength :
      q.support.length = target.occurrence.1.node.history.length := by
    rw [← qSupport, List.length_reverse]
  omega

/-- **(2) Stored Rule-1b root-distance covariance.**  Related actual cursors have equal stored
`rule1bRootDistance`.  Both occurrences are real path nodes, for which the stored Rule-1b
observation is the node depth, and the node depths agree by the history-length covariance derived
from the actual simple physical paths.  No desired depth preservation is assumed. -/
theorem rule1bRootDistance_eq_of_correspondence
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} {e : input.moleculeGraph.Aut} {root : input.Atom}
    (rootFixed : (e : Equiv.Perm input.Atom) root = root)
    {source target : input.LocalizedRerootCursor fuel}
    (correspondence : LocalizedAutCursorCorrespondence input e root source target)
    {a b : input.Atom}
    (sourceCurrent : source.occurrence.1.node.current? = some a)
    (targetCurrent : target.occurrence.1.node.current? = some b) :
    source.occurrence.1.node.rule1bRootDistance =
      target.occurrence.1.node.rule1bRootDistance := by
  have historyEq := input.node_history_length_eq_of_correspondence
    singleBonded acyclic rootFixed correspondence sourceCurrent targetCurrent
  have sourceProvenance :
      source.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
    input.carrierOccurrence_provenance_real singleBonded acyclic source.occurrence
  have targetProvenance :
      target.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
    input.carrierOccurrence_provenance_real singleBonded acyclic target.occurrence
  unfold OfficialCIPNode.rule1bRootDistance OfficialCIPNode.depth
  rw [sourceProvenance, targetProvenance, historyEq]

/-! ## (3) Actual child-list permutation -/

/-- **Child correspondence from the parent correspondence.**  A source child and a target child of
a related pair of actual expansions are related whenever the source child's physical current atom
`w` is the current atom of the source child and the target child's current atom is `e w`.

The proof only reads the actual invariants of the two expansions: every emitted child records its
source occurrence as incoming cut `previous?` and keeps the original root, so the incoming-cut
and root fields of the child relation follow from the parent relation. -/
theorem localizedAutCursorCorrespondence_of_children
    {fuel : Nat} {e : input.moleculeGraph.Aut} {root : input.Atom}
    {source target : input.LocalizedRerootCursor fuel}
    (correspondence : LocalizedAutCursorCorrespondence input e root source target)
    {sourceChildren targetChildren : List (input.LocalizedRerootCursor fuel)}
    (sourceComputed : input.localizedRerootChildren? source = some sourceChildren)
    (targetComputed : input.localizedRerootChildren? target = some targetChildren)
    {child targetChild : input.LocalizedRerootCursor fuel}
    (childMem : child ∈ sourceChildren)
    (targetChildMem : targetChild ∈ targetChildren)
    {w : input.Atom}
    (childCurrent : child.occurrence.1.node.current? = some w)
    (targetChildCurrent :
      targetChild.occurrence.1.node.current? = some ((e : Equiv.Perm input.Atom) w)) :
    LocalizedAutCursorCorrespondence input e root child targetChild where
  source_root :=
    (input.localizedRerootChildren?_root_eq source sourceChildren sourceComputed
      child childMem).trans correspondence.source_root
  target_root :=
    (input.localizedRerootChildren?_root_eq target targetChildren targetComputed
      targetChild targetChildMem).trans correspondence.target_root
  current_maps := by
    intro a b ha hb
    have aEq : a = w := Option.some.inj (ha.symm.trans childCurrent)
    have bEq : b = (e : Equiv.Perm input.Atom) w :=
      Option.some.inj (hb.symm.trans targetChildCurrent)
    rw [aEq, bEq]
  previous_none := by
    have childPrevious :=
      input.localizedRerootChildren?_previous_eq source sourceChildren sourceComputed
        child childMem
    have targetChildPrevious :=
      input.localizedRerootChildren?_previous_eq target targetChildren targetComputed
        targetChild targetChildMem
    rw [childPrevious, targetChildPrevious]
    simp
  previous_maps := by
    have childPrevious :=
      input.localizedRerootChildren?_previous_eq source sourceChildren sourceComputed
        child childMem
    have targetChildPrevious :=
      input.localizedRerootChildren?_previous_eq target targetChildren targetComputed
        targetChild targetChildMem
    intro p q hp hq
    have pEq : p = source.occurrence :=
      Option.some.inj (hp.symm.trans childPrevious)
    have qEq : q = target.occurrence :=
      Option.some.inj (hq.symm.trans targetChildPrevious)
    rw [pEq, qEq]
    exact ⟨correspondence.source_root, correspondence.target_root,
      correspondence.current_maps⟩











theorem exists_target_child_of_source_child
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ fuel)
    {e : input.moleculeGraph.Aut} {root : input.Atom}
    {source target : input.LocalizedRerootCursor fuel}
    (correspondence : LocalizedAutCursorCorrespondence input e root source target)
    {sourceChildren targetChildren : List (input.LocalizedRerootCursor fuel)}
    (sourceComputed : input.localizedRerootChildren? source = some sourceChildren)
    (targetComputed : input.localizedRerootChildren? target = some targetChildren)
    {child : input.LocalizedRerootCursor fuel} (childMem : child ∈ sourceChildren) :
    ∃ targetChild ∈ targetChildren,
      ∃ w : input.Atom,
        child.occurrence.1.node.current? = some w ∧
          targetChild.occurrence.1.node.current? =
            some ((e : Equiv.Perm input.Atom) w) ∧
            LocalizedAutCursorCorrespondence input e root child targetChild := by
  obtain ⟨w, childCurrent⟩ := input.occurrence_current_exists child.occurrence
  obtain ⟨o, sourceCurrent⟩ := input.occurrence_current_exists source.occurrence
  obtain ⟨o', targetCurrent⟩ := input.occurrence_current_exists target.occurrence
  have targetCurrentMap : o' = (e : Equiv.Perm input.Atom) o :=
    correspondence.current_maps sourceCurrent targetCurrent
  cases hSourcePrevious : source.previous? with
  | none =>
      -- Root cursor on both sides: the cut removes nothing.
      have targetPrevious : target.previous? = none :=
        correspondence.previous_none.mp hSourcePrevious
      have physical : input.moleculeGraph.Adj o w :=
        (input.localizedRerootChildren?_current_iff_adjacent_root singleBonded acyclic
          enough source hSourcePrevious sourceCurrent sourceChildren sourceComputed w).mp
          ⟨child, childMem, childCurrent⟩
      have targetAdjacent :
          input.moleculeGraph.Adj o' ((e : Equiv.Perm input.Atom) w) := by
        rw [targetCurrentMap]
        exact (MoleculeGraph.Aut.adj_iff (m := input.moleculeGraph) e o w).2 physical
      obtain ⟨targetChild, targetChildMem, targetChildCurrent⟩ :=
        (input.localizedRerootChildren?_current_iff_adjacent_root singleBonded acyclic
          enough target targetPrevious targetCurrent targetChildren targetComputed
          ((e : Equiv.Perm input.Atom) w)).mpr targetAdjacent
      exact ⟨targetChild, targetChildMem, w, childCurrent, targetChildCurrent,
        input.localizedAutCursorCorrespondence_of_children correspondence sourceComputed
          targetComputed childMem targetChildMem childCurrent targetChildCurrent⟩
  | some previous =>
      -- Incoming coordinate on both sides: the cut removes exactly the incoming atom.
      have targetNotNone : target.previous? ≠ none := by
        intro targetNone
        have sourceNone : source.previous? = none :=
          correspondence.previous_none.mpr targetNone
        rw [hSourcePrevious] at sourceNone
        cases sourceNone
      obtain ⟨targetPrevious, targetPreviousEq⟩ : ∃ q, target.previous? = some q := by
        cases hTarget : target.previous? with
        | none => exact (targetNotNone hTarget).elim
        | some q => exact ⟨q, rfl⟩
      obtain ⟨pAtom, previousCurrent⟩ := input.occurrence_current_exists previous
      obtain ⟨qAtom, targetPreviousCurrent⟩ :=
        input.occurrence_current_exists targetPrevious
      obtain ⟨previousRoot, targetPreviousRoot, previousCurrentMaps⟩ :=
        correspondence.previous_maps hSourcePrevious targetPreviousEq
      have sourceSameRoot : source.occurrence.1.root = previous.1.root :=
        correspondence.source_root.trans previousRoot.symm
      have targetSameRoot : target.occurrence.1.root = targetPrevious.1.root :=
        correspondence.target_root.trans targetPreviousRoot.symm
      have atomMap : qAtom = (e : Equiv.Perm input.Atom) pAtom :=
        previousCurrentMaps previousCurrent targetPreviousCurrent
      obtain ⟨adjacent, wNePrevious⟩ :=
        (input.localizedRerootChildren?_current_iff_adjacent_of_previous singleBonded acyclic
          enough source previous hSourcePrevious sourceSameRoot sourceCurrent previousCurrent
          sourceChildren sourceComputed w).mp ⟨child, childMem, childCurrent⟩
      have targetAdjacent :
          input.moleculeGraph.Adj o' ((e : Equiv.Perm input.Atom) w) := by
        rw [targetCurrentMap]
        exact (MoleculeGraph.Aut.adj_iff (m := input.moleculeGraph) e o w).2 adjacent
      have targetNe : (e : Equiv.Perm input.Atom) w ≠ qAtom := by
        rw [atomMap]
        intro imageEq
        exact wNePrevious ((e : Equiv.Perm input.Atom).injective imageEq)
      obtain ⟨targetChild, targetChildMem, targetChildCurrent⟩ :=
        (input.localizedRerootChildren?_current_iff_adjacent_of_previous singleBonded acyclic
          enough target targetPrevious targetPreviousEq targetSameRoot targetCurrent
          targetPreviousCurrent targetChildren targetComputed
          ((e : Equiv.Perm input.Atom) w)).mpr ⟨targetAdjacent, targetNe⟩
      exact ⟨targetChild, targetChildMem, w, childCurrent, targetChildCurrent,
        input.localizedAutCursorCorrespondence_of_children correspondence sourceComputed
          targetComputed childMem targetChildMem childCurrent targetChildCurrent⟩












theorem exists_permuted_children_forall₂_of_correspondence
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ fuel)
    {e : input.moleculeGraph.Aut} {root : input.Atom}
    {source target : input.LocalizedRerootCursor fuel}
    (correspondence : LocalizedAutCursorCorrespondence input e root source target)
    {sourceChildren targetChildren : List (input.LocalizedRerootCursor fuel)}
    (sourceComputed : input.localizedRerootChildren? source = some sourceChildren)
    (targetComputed : input.localizedRerootChildren? target = some targetChildren) :
    ∃ targetChildren' : List (input.LocalizedRerootCursor fuel),
      List.Perm targetChildren' targetChildren ∧
        List.Forall₂ (LocalizedAutCursorCorrespondence input e root)
          sourceChildren targetChildren' := by
  classical
  -- A single actual target child for every actual source child.
  let pick : (c : input.LocalizedRerootCursor fuel) → c ∈ sourceChildren →
      input.LocalizedRerootCursor fuel :=
    fun c cMem =>
      Classical.choose
        (input.exists_target_child_of_source_child singleBonded acyclic enough correspondence
          sourceComputed targetComputed cMem)
  have pickSpec : ∀ (c : input.LocalizedRerootCursor fuel) (cMem : c ∈ sourceChildren),
      pick c cMem ∈ targetChildren ∧
        ∃ w : input.Atom,
          c.occurrence.1.node.current? = some w ∧
            (pick c cMem).occurrence.1.node.current? =
              some ((e : Equiv.Perm input.Atom) w) ∧
              LocalizedAutCursorCorrespondence input e root c (pick c cMem) := by
    intro c cMem
    exact Classical.choose_spec
      (input.exists_target_child_of_source_child singleBonded acyclic enough correspondence
        sourceComputed targetComputed cMem)
  -- Extend the choice to a total function on cursors.
  let selection : input.LocalizedRerootCursor fuel → input.LocalizedRerootCursor fuel :=
    fun c => if cMem : c ∈ sourceChildren then pick c cMem else c
  have selectionSpec : ∀ (c : input.LocalizedRerootCursor fuel) (cMem : c ∈ sourceChildren),
      selection c ∈ targetChildren ∧
        ∃ w : input.Atom,
          c.occurrence.1.node.current? = some w ∧
            (selection c).occurrence.1.node.current? =
              some ((e : Equiv.Perm input.Atom) w) ∧
              LocalizedAutCursorCorrespondence input e root c (selection c) := by
    intro c cMem
    have definition : selection c = pick c cMem := by
      simp [selection, dif_pos cMem]
    rw [definition]
    exact pickSpec c cMem
  let image : List (input.LocalizedRerootCursor fuel) := sourceChildren.map selection
  -- The selection is injective on the actual source child list.
  have selectionInjective :
      ∀ left ∈ sourceChildren, ∀ right ∈ sourceChildren,
        selection left = selection right → left = right := by
    intro left leftMem right rightMem imageEq
    obtain ⟨wLeft, leftCurrent, leftImage, _⟩ := (selectionSpec left leftMem).2
    obtain ⟨wRight, rightCurrent, rightImage, _⟩ := (selectionSpec right rightMem).2
    have imageAtoms : some ((e : Equiv.Perm input.Atom) wLeft) =
        some ((e : Equiv.Perm input.Atom) wRight) := by
      rw [← leftImage, imageEq, rightImage]
    have atomsEq : wLeft = wRight :=
      (e : Equiv.Perm input.Atom).injective (Option.some.inj imageAtoms)
    have sameCurrent :
        left.occurrence.1.node.current? = right.occurrence.1.node.current? := by
      rw [leftCurrent, rightCurrent, atomsEq]
    exact input.localizedRerootChildren?_current_injective singleBonded acyclic
      source sourceChildren sourceComputed left leftMem right rightMem sameCurrent
  have imageNodup : (sourceChildren.map selection).Nodup := by
    apply List.Nodup.map_on
    · intro left leftMem right rightMem imageEq
      exact selectionInjective left leftMem right rightMem imageEq
    · exact input.localizedRerootChildren_nodup source sourceChildren
        (input.localizedRerootChildren?_sound source sourceChildren sourceComputed)
  have targetNodup : targetChildren.Nodup :=
    input.localizedRerootChildren_nodup target targetChildren
      (input.localizedRerootChildren?_sound target targetChildren targetComputed)
  -- The image is exactly the target child list, elementwise.
  have imageMembership : ∀ d, d ∈ image ↔ d ∈ targetChildren := by
    intro d
    constructor
    · intro imageMem
      rw [List.mem_map] at imageMem
      obtain ⟨c, cMem, rfl⟩ := imageMem
      exact (selectionSpec c cMem).1
    · intro targetMem
      -- Transport the target child back along the inverse automorphism.
      obtain ⟨c, cMem, w, targetCurrent, sourceImage, _⟩ :=
        input.exists_target_child_of_source_child singleBonded acyclic enough
          (e := e⁻¹) (root := root) (source := target) (target := source)
          (correspondence := input.localizedAutCursorCorrespondence_symm correspondence)
          (sourceChildren := targetChildren) (targetChildren := sourceChildren)
          targetComputed sourceComputed targetMem
      -- The chosen image of `c` is this very target child.
      have chosenEq : selection c = d := by
        apply input.localizedRerootChildren?_current_injective singleBonded acyclic
          target targetChildren targetComputed (selection c) (selectionSpec c cMem).1
          d targetMem
        obtain ⟨wChosen, chosenCurrent, chosenImage, _⟩ := (selectionSpec c cMem).2
        have atomEq : wChosen =
            ((e⁻¹ : input.moleculeGraph.Aut) : Equiv.Perm input.Atom) w :=
          Option.some.inj (chosenCurrent.symm.trans sourceImage)
        rw [chosenImage, atomEq, targetCurrent]
        congr 1
        have coefficient :
            ((e⁻¹ : input.moleculeGraph.Aut) : Equiv.Perm input.Atom) =
              ((e : Equiv.Perm input.Atom))⁻¹ := by
          simp
        rw [coefficient]
        exact Equiv.apply_symm_apply (e : Equiv.Perm input.Atom) w
      rw [← chosenEq]
      exact List.mem_map.mpr ⟨c, cMem, rfl⟩
  have imagePerm : List.Perm image targetChildren :=
    (List.perm_ext_iff_of_nodup imageNodup targetNodup).mpr imageMembership
  -- The pointwise relation on the aligned source list.
  have forall₂ : List.Forall₂ (LocalizedAutCursorCorrespondence input e root)
      sourceChildren image := by
    rw [show image = sourceChildren.map selection from rfl]
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    intro c cMem
    obtain ⟨_w, _current, _image, corresponding⟩ := (selectionSpec c cMem).2
    exact corresponding
  exact ⟨image, imagePerm, forall₂⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedAutCursorCorrespondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedAutCursorCorrespondence_symm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.occurrence_current_exists
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.officialNodeAtomLabel_eq_of_correspondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.node_history_length_eq_of_correspondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule1bRootDistance_eq_of_correspondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedAutCursorCorrespondence_of_children
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_target_child_of_source_child
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_permuted_children_forall₂_of_correspondence
