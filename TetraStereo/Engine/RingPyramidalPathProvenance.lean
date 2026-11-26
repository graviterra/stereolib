import TetraStereo.Engine.RingPyramidalPublication
import TetraStereo.OneCenter.LocalizedOutwardRule1bObserverEquivalence

/-! Path-sensitive provenance of physical arms at every real single-bond
occurrence. No degree-four, pyramidal-element or acyclicity assumption is needed. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPyramidalPathProvenance
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)

private theorem classified
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (atom : input.Atom)
    (meaning : target.1.node.provenance = .realAtom ∧ target.1.node.current? = some atom)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren?
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) = some children)
    (child : input.LocalizedRerootCursor carrierFuel)
    (present : child ∈ children) :
    ∃ w, child.occurrence.1.node.current? = some w ∧
      input.moleculeGraph.Adj atom w ∧
      ((∃ certificate : input.LocalizedParentFrameHistory target,
          child.occurrence = certificate.parent ∧
          certificate.parent.1.node.ActiveSimple ∧
          target.1.node.parent? = some w ∧
          w ∈ target.1.node.history) ∨
        (child.occurrence.1.node = target.1.node.extend w 0 ∧
          target.1.node.parent? ≠ some w ∧
          (w ∈ target.1.node.history →
            child.occurrence.1.node.provenance =
              OfficialCIPNodeProvenance.ringDuplicate
                (target.1.node.duplicateRootDistance w) ∧
            child.occurrence.1.node.isDuplicateLeaf = true ∧
            input.executableOfficialCIPChildren child.occurrence.1.node = []) ∧
          (w ∉ target.1.node.history →
            child.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom))) := by
  have oObserved : target.1.node.current? = some atom := meaning.2
  have real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom := meaning.1
  have frames := input.simpleBond_realCenter_childFrames target real children computed
  have framePresent : child.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1 := by
    rw [← frames.1]
    exact List.mem_map.mpr ⟨child, present, rfl⟩
  rw [localizedRerootNeighborFrames, List.mem_append] at framePresent
  rcases framePresent with parentPresent | outwardPresent
  · have nonroot : target.1.address ≠ [] := by
      rw [localizedCarrierParentFrames, List.mem_filter] at parentPresent
      obtain ⟨_, raw⟩ := parentPresent
      simp only [Bool.and_eq_true, beq_iff_eq] at raw
      obtain ⟨⟨_, lengthEq⟩, _⟩ := raw
      intro empty
      rw [empty] at lengthEq
      simp at lengthEq
    obtain ⟨certificate, parentAtom, parentCurrent, parentObserved, visited, adjacent, active,
        _member⟩ :=
      input.realCenter_parent_current target oObserved nonroot
    have singleton := certificate.carrierParentFrames_eq_singleton input
    have frameEq : child.occurrence.1 = certificate.parent.1 := by
      have member : child.occurrence.1 ∈ [certificate.parent.1] := by
        simpa [singleton] using parentPresent
      simpa using member
    have occurrenceEq : child.occurrence = certificate.parent := Subtype.ext frameEq
    refine ⟨parentAtom, ?_, adjacent, Or.inl ?_⟩
    · simpa [frameEq] using parentCurrent
    · exact ⟨certificate, occurrenceEq, active, parentObserved, visited⟩
  · obtain ⟨w, _slot, nodeEq, currentEq, _rootEq, _addressEq, _atSlot, notParent, adjacent⟩ :=
      input.simpleBond_outwardFrame_extend_zero singleBonded target oObserved real
        child.occurrence.1 outwardPresent
    refine ⟨w, currentEq, adjacent, Or.inr ⟨nodeEq, notParent, ?_, ?_⟩⟩
    · intro visited
      have provenance : child.occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.ringDuplicate
            (target.1.node.duplicateRootDistance w) := by
        rw [nodeEq]
        exact input.legitimateOccurrence_ring_provenance visited
      have leaf : child.occurrence.1.node.isDuplicateLeaf = true := by
        rw [OfficialCIPNode.isDuplicateLeaf, provenance]
        rfl
      have terminal : input.executableOfficialCIPChildren child.occurrence.1.node = [] := by
        simp [executableOfficialCIPChildren, leaf]
      exact ⟨provenance, leaf, terminal⟩
    · intro fresh
      rw [nodeEq, OfficialCIPNode.extend_provenance]
      exact OfficialCIPNode.childProvenance_real target.1.node w fresh


/-- An arm is real precisely for the incoming parent direction or a previously
unvisited atom. Every other visited direction is a terminal ring duplicate. -/
theorem arm_endpoint {i : Input} (q : Site i) (a w : i.certified.Atom)
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (arm : Arm i) (present : arm ∈ RingRetainedAuxiliary.frame i.certified q)
    (physical : arm.occurrence.val.node.current? = some w) :
    (arm.occurrence.val.node.provenance = .realAtom ↔
      q.val.node.parent? = some w ∨ w ∉ q.val.node.history) ∧
    (q.val.node.parent? ≠ some w → w ∈ q.val.node.history →
      arm.occurrence.val.node.provenance = .ringDuplicate (q.val.node.duplicateRootDistance w) ∧
      arm.occurrence.val.node.isDuplicateLeaf = true ∧
      i.certified.executableOfficialCIPChildren arm.occurrence.val.node = []) := by
  obtain ⟨v,atV,_,kind⟩ := classified i.certified i.single q a ⟨real,current⟩
    (RingRetainedAuxiliary.frame i.certified q)
    (i.certified.localizedRerootChildren?_eq_some_executable _) arm present
  have same : v = w := Option.some.inj (atV.symm.trans physical)
  subst v
  rcases kind with parent | outward
  · obtain ⟨certificate,eq,active,parent,visited⟩ := parent
    have childReal : arm.occurrence.val.node.provenance = .realAtom := by rw [eq]; exact active.1
    exact ⟨⟨fun _ => Or.inl parent,fun _ => childReal⟩,fun notParent _ => (notParent parent).elim⟩
  · obtain ⟨_,notParent,visited,fresh⟩ := outward
    refine ⟨?_,fun _ mem => visited mem⟩
    constructor
    · intro childReal
      right
      intro mem
      have duplicate := (visited mem).1
      rw [childReal] at duplicate
      contradiction
    · intro eligible
      rcases eligible with parent | unvisited
      · exact (notParent parent).elim
      · exact fresh unvisited

/-- Real carrier histories remain duplicate-free even on cyclic molecular graphs. -/
theorem history_nodup {i : Input} (q : Site i)
    (real : q.val.node.provenance = .realAtom) : q.val.node.history.Nodup :=
  (i.certified.localizedCIPOccurrence_activeSimple_of_provenance_real q real).2

/-- On one stored history a duplicate distance identifies the physical atom.
The first-index lookup proves this even without the stronger real-history Nodup fact. -/
theorem duplicate_distance_injective {V : Type} [DecidableEq V] (node : OfficialCIPNode V)
    {a b : V} (visitedA : a ∈ node.history) (visitedB : b ∈ node.history)
    (same : node.duplicateRootDistance a = node.duplicateRootDistance b) : a = b := by
  obtain ⟨ia,_,da,_,lookupA⟩ :=
    OutwardRule1bObserverEquivalence.duplicateRootDistance_eq_firstIndex node a visitedA
  obtain ⟨ib,_,db,_,lookupB⟩ :=
    OutwardRule1bObserverEquivalence.duplicateRootDistance_eq_firstIndex node b visitedB
  rw [da,db] at same
  subst ib
  exact Option.some.inj (lookupA.symm.trans lookupB)
/-- Original-root duplicate distance and distance backward from the active
occurrence are complementary indices of the same duplicate-free path. -/
theorem duplicate_distance_add_forward {V : Type} [DecidableEq V]
    (node : OfficialCIPNode V) (nodup : node.history.Nodup) (a : V)
    (visited : a ∈ node.history) :
    node.duplicateRootDistance a + node.history.idxOf a + 1 = node.history.length := by
  obtain ⟨index,_,distance,bound,lookup⟩ :=
    OutwardRule1bObserverEquivalence.duplicateRootDistance_eq_firstIndex node a visited
  rw [List.getElem?_reverse bound] at lookup
  obtain ⟨valid,atIndex⟩ := List.getElem?_eq_some_iff.mp lookup
  have forward := nodup.idxOf_getElem (node.history.length - 1 - index) valid
  rw [atIndex] at forward
  omega

/-- At every real occurrence, using original-root distances or forward path
indices from the active occurrence gives opposite strict orders on visited atoms.
In particular the conventions cannot agree on either strict comparison of two
distinct visited duplicate targets. -/
theorem duplicate_order_reversal {i : Input} (q : Site i)
    (real : q.val.node.provenance = .realAtom) {a b : i.certified.Atom}
    (visitedA : a ∈ q.val.node.history) (visitedB : b ∈ q.val.node.history) :
    (q.val.node.duplicateRootDistance a < q.val.node.duplicateRootDistance b ↔
      q.val.node.history.idxOf b < q.val.node.history.idxOf a) := by
  have ha := duplicate_distance_add_forward q.val.node (history_nodup q real) a visitedA
  have hb := duplicate_distance_add_forward q.val.node (history_nodup q real) b visitedB
  omega

private theorem path_head {i r h a} (p : RingGraphPaths.Path i r h a) :
    ∃ tail, h = a :: tail := by
  cases p <;> exact ⟨_, rfl⟩

private theorem ancestor_path {i r h a} (p : RingGraphPaths.Path i r h a)
    {w : i.certified.Atom} (visited : w ∈ h) :
    ∃ skipped retained, h = skipped ++ retained ∧ RingGraphPaths.Path i r retained w := by
  induction p with
  | origin =>
      simp only [List.mem_singleton] at visited
      subst w
      exact ⟨[], _, rfl, .origin⟩
  | @step h a next prior bond fresh ih =>
      rcases List.mem_cons.mp visited with eq | mem
      · subst w
        exact ⟨[], _, rfl, .step prior bond fresh⟩
      · obtain ⟨skipped, retained, eq, path⟩ := ih mem
        exact ⟨next :: skipped, retained, by simp [eq], path⟩

/-- A ring closure at a real occurrence shortcuts its path through the visited
ancestor. The retained retained records the common original-root part of both paths. -/
theorem nonreal_arm_shortcut {i : Input} (q : Site i) (a w : i.certified.Atom)
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (arm : Arm i) (present : arm ∈ RingRetainedAuxiliary.frame i.certified q)
    (physical : arm.occurrence.val.node.current? = some w)
    (nonreal : arm.occurrence.val.node.provenance ≠ .realAtom) :
    ∃ (short : Site i) (skipped retained : List i.certified.Atom),
      RingGraphPaths.Represents short q.val.root (a :: retained) a ∧
      q.val.node.history = skipped ++ retained ∧
      RingGraphPaths.Path i q.val.root retained w ∧
      2 ≤ skipped.length ∧
      (w ≠ q.val.root → 2 ≤ retained.length) ∧
      RingActiveDistanceSchedule.distance short < RingActiveDistanceSchedule.distance q := by
  have eligible := (arm_endpoint q a w real current arm present physical).1
  have notParent : q.val.node.parent? ≠ some w := fun h => nonreal (eligible.mpr (Or.inl h))
  have visited : w ∈ q.val.node.history := by
    by_contra h
    exact nonreal (eligible.mpr (Or.inr h))
  obtain ⟨v, atV, bond, _⟩ := classified i.certified i.single q a ⟨real,current⟩
    (RingRetainedAuxiliary.frame i.certified q)
    (i.certified.localizedRerootChildren?_eq_some_executable _) arm present
  have eqVW : v = w := Option.some.inj (atV.symm.trans physical)
  subst v
  obtain ⟨b, atB, path⟩ := RingGraphPaths.site_path q real
  have eqBA : b = a := Option.some.inj (atB.symm.trans current)
  subst b
  obtain ⟨skipped, retained, hist, ancestor⟩ := ancestor_path path visited
  obtain ⟨tail, suffixEq⟩ := path_head ancestor
  have prefixLength : 2 ≤ skipped.length := by
    cases skipped with
    | nil =>
        obtain ⟨rest, head⟩ := path_head path
        have aw : a = w := List.cons.inj (by simpa [head, suffixEq] using hist) |>.1
        subst w
        simp [MoleculeGraph.Adj, i.certified.moleculeGraph.bond_self] at bond
    | cons x xs =>
        cases xs with
        | nil =>
            apply False.elim
            apply notParent
            simp [OfficialCIPNode.parent?, hist, suffixEq]
        | cons y ys => simp
  have fresh : a ∉ retained := by
    obtain ⟨rest, head⟩ := path_head path
    have nodup := history_nodup q real
    rw [hist] at nodup
    have disjoint := (List.nodup_append.mp nodup).2.2
    have inPrefix : a ∈ skipped := by
      cases skipped with
      | nil => simp at prefixLength
      | cons x xs =>
          have ax : a = x := List.cons.inj (by simpa [head] using hist) |>.1
          simp [ax]
    exact fun mem => disjoint a inPrefix a mem rfl
  have shortcut := RingGraphPaths.Path.step ancestor
    ((i.certified.moleculeGraph.adj_symm).mp bond) fresh
  refine ⟨RingGraphPaths.site shortcut, skipped, retained,
    RingGraphPaths.represents_site shortcut, hist, ancestor, prefixLength, ?_, ?_⟩
  · intro nonroot
    cases ancestor with
    | origin => exact (nonroot rfl).elim
    | step prior _ _ =>
        obtain ⟨tail, eq⟩ := path_head prior
        simp [eq]
  · have shortLength := RingGraphPaths.path_length (RingGraphPaths.represents_site shortcut)
    have oldLength := RingGraphPaths.path_length
      (show RingGraphPaths.Represents q q.val.root q.val.node.history a from
        ⟨rfl,rfl,real,current⟩)
    rw [hist, List.length_append] at oldLength
    simp only [List.length_cons] at shortLength
    omega

/-- Among two distinct closure atoms at least one shortcut retains a nontrivial
original-root suffix, and hence the original first root arm. -/
theorem two_nonreal_arms_shortcut {i : Input} (q : Site i) (a w₁ w₂ : i.certified.Atom)
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (arm₁ arm₂ : Arm i)
    (present₁ : arm₁ ∈ RingRetainedAuxiliary.frame i.certified q)
    (present₂ : arm₂ ∈ RingRetainedAuxiliary.frame i.certified q)
    (physical₁ : arm₁.occurrence.val.node.current? = some w₁)
    (physical₂ : arm₂.occurrence.val.node.current? = some w₂)
    (nonreal₁ : arm₁.occurrence.val.node.provenance ≠ .realAtom)
    (nonreal₂ : arm₂.occurrence.val.node.provenance ≠ .realAtom)
    (distinct : w₁ ≠ w₂) :
    ∃ (short : Site i) (skipped retained : List i.certified.Atom),
      RingGraphPaths.Represents short q.val.root (a :: retained) a ∧
      q.val.node.history = skipped ++ retained ∧ 2 ≤ retained.length ∧
      RingActiveDistanceSchedule.distance short < RingActiveDistanceSchedule.distance q := by
  have choose (w : i.certified.Atom) (arm : Arm i)
      (present : arm ∈ RingRetainedAuxiliary.frame i.certified q)
      (physical : arm.occurrence.val.node.current? = some w)
      (nonreal : arm.occurrence.val.node.provenance ≠ .realAtom)
      (nonroot : w ≠ q.val.root) :
      ∃ (short : Site i) (skipped retained : List i.certified.Atom),
        RingGraphPaths.Represents short q.val.root (a :: retained) a ∧
        q.val.node.history = skipped ++ retained ∧ 2 ≤ retained.length ∧
        RingActiveDistanceSchedule.distance short < RingActiveDistanceSchedule.distance q := by
    obtain ⟨short, skipped, retained, rep, hist, _, _, length, closer⟩ :=
      nonreal_arm_shortcut q a w real current arm present physical nonreal
    exact ⟨short, skipped, retained, rep, hist, length nonroot, closer⟩
  by_cases first : w₁ = q.val.root
  · exact choose w₂ arm₂ present₂ physical₂ nonreal₂
      (fun second => distinct (first.trans second.symm))
  · exact choose w₁ arm₁ present₁ physical₁ nonreal₁ first

end TetraStereo.Engine.RingPyramidalPathProvenance
assert_kernel_only TetraStereo.Engine.RingPyramidalPathProvenance.arm_endpoint
assert_kernel_only TetraStereo.Engine.RingPyramidalPathProvenance.history_nodup
assert_kernel_only TetraStereo.Engine.RingPyramidalPathProvenance.duplicate_distance_injective

assert_kernel_only TetraStereo.Engine.RingPyramidalPathProvenance.duplicate_distance_add_forward
assert_kernel_only TetraStereo.Engine.RingPyramidalPathProvenance.duplicate_order_reversal

assert_kernel_only TetraStereo.Engine.RingPyramidalPathProvenance.nonreal_arm_shortcut
assert_kernel_only TetraStereo.Engine.RingPyramidalPathProvenance.two_nonreal_arms_shortcut
