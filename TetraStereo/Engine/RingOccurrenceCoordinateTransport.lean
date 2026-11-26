import TetraStereo.Engine.RingRetainedAuxiliary
import TetraStereo.KernelOnly

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Equality of semantic constitution transports atom IDs without any geometric hypothesis. -/
def sameMoleculeAtom {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule) : a.Atom ≃ b.Atom :=
  Equiv.cast (congrArg (fun m => Fin m.atomCount) h)

def sameMoleculeFrame {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule)
    (f : a.LocalizedCIPOccurrenceFrame) : b.LocalizedCIPOccurrenceFrame :=
  { root := sameMoleculeAtom h f.root
    address := f.address
    node := cast (congrArg (fun m => OfficialCIPNode (Fin m.atomCount)) h) f.node
    remaining := f.remaining }

/-- The independent bounded subtree relation is unchanged by changing spatial/diagram data. -/
theorem sameMolecule_subtree {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule)
    {root : a.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode a.Atom} {f : a.LocalizedCIPOccurrenceFrame}
    (derived : a.DeclarativeLocalizedOccurrenceSubtree root path fuel node f) :
    b.DeclarativeLocalizedOccurrenceSubtree (sameMoleculeAtom h root) path fuel
      (cast (congrArg (fun m => OfficialCIPNode (Fin m.atomCount)) h) node)
      (sameMoleculeFrame h f) := by
  rcases a with ⟨⟨⟨ma, sa, da⟩, wa⟩, ga⟩
  rcases b with ⟨⟨⟨mb, sb, db⟩, wb⟩, gb⟩
  dsimp at h
  subst mb
  simp only [sameMoleculeFrame, sameMoleculeAtom, Equiv.cast_apply, cast_eq] at *
  induction derived with
  | subtreeRoot path fuel node => constructor
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot descendant ih =>
    apply DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant (descendant := ih)
    convert childAtSlot using 1
    simp only [executableOfficialCIPChildren, executableOfficialChildCopies,
        executableOfficialNeighborCopies, moleculeGraph,
        MoleculeGraph.neighborFinset, MoleculeGraph.Adj, Atom]
    cases node.current? <;> cases node.parent? <;> rfl

/-- Every occurrence survives a coordinate change, with its entire address and node history. -/
theorem sameMolecule_mem {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule)
    {fuel : Nat} {f : a.LocalizedCIPOccurrenceFrame}
    (mem : f ∈ a.localizedOccurrences fuel) :
    sameMoleculeFrame h f ∈ b.localizedOccurrences fuel := by
  apply (b.mem_localizedOccurrences_iff fuel _).mpr
  have transported := sameMolecule_subtree h ((a.mem_localizedOccurrences_iff fuel f).mp mem)
  rcases a with ⟨⟨⟨ma, sa, da⟩, wa⟩, ga⟩
  rcases b with ⟨⟨⟨mb, sb, db⟩, wb⟩, gb⟩
  dsimp at h
  subst mb
  simpa [DeclarativeLocalizedOccurrence, DeclarativeLocalizedOccurrenceAtAtom,
    sameMoleculeFrame, sameMoleculeAtom] using transported

@[simp] theorem sameMoleculeFrame_symm {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule)
    (f : a.LocalizedCIPOccurrenceFrame) :
    sameMoleculeFrame h.symm (sameMoleculeFrame h f) = f := by
  rcases a with ⟨⟨⟨ma, sa, da⟩, wa⟩, ga⟩
  rcases b with ⟨⟨⟨mb, sb, db⟩, wb⟩, gb⟩
  dsimp at h
  subst mb
  rfl

theorem sameMolecule_mem_iff {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule)
    {fuel : Nat} {f : a.LocalizedCIPOccurrenceFrame} :
    sameMoleculeFrame h f ∈ b.localizedOccurrences fuel ↔
      f ∈ a.localizedOccurrences fuel := by
  constructor
  · intro member
    simpa using sameMolecule_mem h.symm member
  · exact sameMolecule_mem h

/-- An equivalence of the actual finite occurrence carriers. -/
def sameMoleculeOccurrenceEquiv {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule) (fuel : Nat) :
    a.LocalizedCIPOccurrence fuel ≃ b.LocalizedCIPOccurrence fuel where
  toFun f := ⟨sameMoleculeFrame h f.1, sameMolecule_mem h f.2⟩
  invFun f := ⟨sameMoleculeFrame h.symm f.1, sameMolecule_mem h.symm f.2⟩
  left_inv f := Subtype.ext (sameMoleculeFrame_symm h f.1)
  right_inv f := Subtype.ext (by simp)

/-- A reroot cursor transports both the current occurrence and the incoming cut. -/
def sameMoleculeCursor {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule) {fuel : Nat}
    (c : a.LocalizedRerootCursor fuel) : b.LocalizedRerootCursor fuel where
  occurrence := ⟨sameMoleculeFrame h c.occurrence.1, sameMolecule_mem h c.occurrence.2⟩
  previous? := c.previous?.map fun p => ⟨sameMoleculeFrame h p.1, sameMolecule_mem h p.2⟩

theorem sameMolecule_subtree_map {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule)
    (root : a.Atom) (fuel : Nat) (path : List Nat) (node : OfficialCIPNode a.Atom) :
    (a.localizedOccurrenceSubtree root fuel path node).map (sameMoleculeFrame h) =
      b.localizedOccurrenceSubtree (sameMoleculeAtom h root) fuel path
        (cast (congrArg (fun m => OfficialCIPNode (Fin m.atomCount)) h) node) := by
  rcases a with ⟨⟨⟨ma, sa, da⟩, wa⟩, ga⟩
  rcases b with ⟨⟨⟨mb, sb, db⟩, wb⟩, gb⟩
  dsimp at h
  subst mb
  let a : CertifiedLocalizedCIPInput := ⟨⟨⟨ma, sa, da⟩, wa⟩, ga⟩
  let b : CertifiedLocalizedCIPInput := ⟨⟨⟨ma, sb, db⟩, wb⟩, gb⟩
  have children : ∀ n : OfficialCIPNode a.Atom,
      a.executableOfficialCIPChildren n = b.executableOfficialCIPChildren n := by
    intro n
    unfold executableOfficialCIPChildren executableOfficialChildCopies
    cases n.current? <;> cases n.parent? <;> rfl
  induction fuel generalizing path node with
  | zero => rfl
  | succ fuel ih =>
    simp only [localizedOccurrenceSubtree, List.map_cons, List.map_flatMap]
    congr 1
    rw [children]
    apply List.flatMap_congr
    intro child _
    exact ih _ _

theorem sameMolecule_occurrences_map {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule) (fuel : Nat) :
    (a.localizedOccurrences fuel).map (sameMoleculeFrame h) = b.localizedOccurrences fuel := by
  have inj : Function.Injective (sameMoleculeFrame h) := by
    intro x y eq
    simpa using congrArg (sameMoleculeFrame h.symm) eq
  rw [localizedOccurrences, ← List.dedup_map_of_injective inj, List.map_flatMap]
  have subtree := fun root => sameMolecule_subtree_map h root (fuel+1) [] (OfficialCIPNode.root root)
  rcases a with ⟨⟨⟨ma, sa, da⟩, wa⟩, ga⟩
  rcases b with ⟨⟨⟨mb, sb, db⟩, wb⟩, gb⟩
  dsimp at h
  subst mb
  unfold localizedOccurrences
  congr 1
  apply List.flatMap_congr
  intro atom _
  simpa [localizedOccurrencesAtAtom, sameMoleculeAtom] using subtree atom

theorem sameMolecule_intended_map {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule) {fuel : Nat}
    (c : a.LocalizedRerootCursor fuel) :
    (a.intendedLocalizedRerootChildFrames c).map (sameMoleculeFrame h) =
      b.intendedLocalizedRerootChildFrames (sameMoleculeCursor h c) := by
  have carrier := sameMolecule_occurrences_map h fuel
  rcases a with ⟨⟨⟨ma, sa, da⟩, wa⟩, ga⟩
  rcases b with ⟨⟨⟨mb, sb, db⟩, wb⟩, gb⟩
  dsimp at h
  subst mb
  unfold intendedLocalizedRerootChildFrames localizedRerootNeighborFrames
    localizedCarrierParentFrames localizedCarrierOutwardChildFrames
  simp only [← carrier]
  rcases c with ⟨q, previous⟩
  cases previous <;> cases dup : q.val.node.isDuplicateLeaf <;>
    simp [dup, sameMoleculeCursor, sameMoleculeFrame, sameMoleculeAtom,
      List.filter_map, List.map_append, Function.comp_def]

/-- Ordered executable children commute, including the incoming direction on every child. -/
theorem sameMolecule_children_map {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule) {fuel : Nat}
    (c : a.LocalizedRerootCursor fuel) :
    (a.executableLocalizedRerootChildren c).map (sameMoleculeCursor h) =
      b.executableLocalizedRerootChildren (sameMoleculeCursor h c) := by
  let children := (a.executableLocalizedRerootChildren c).map (sameMoleculeCursor h)
  have derived : b.DeclarativeLocalizedRerootChildren (sameMoleculeCursor h c) children := by
    constructor
    · change (children.map (fun child => child.occurrence.1)) = _
      calc
        _ = ((a.executableLocalizedRerootChildren c).map (fun child => child.occurrence.1)).map
            (sameMoleculeFrame h) := by simp [children, List.map_map, sameMoleculeCursor]
        _ = _ := by rw [a.executableLocalizedRerootChildren_map c, sameMolecule_intended_map]
    · intro child member
      change child ∈ (a.executableLocalizedRerootChildren c).map (sameMoleculeCursor h) at member
      obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
      simp only [sameMoleculeCursor]
      rw [a.executableLocalizedRerootChildren_previous c source sourceMember]
      rfl
  have computed := (b.localizedRerootChildren?_eq_some_iff _ _).mpr derived
  rw [b.localizedRerootChildren?_eq_some_executable] at computed
  exact (Option.some.inj computed).symm

theorem sameMolecule_retained_frame_map {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule) {fuel : Nat}
    (q : a.LocalizedCIPOccurrence fuel) :
    (TetraStereo.Engine.RingRetainedAuxiliary.frame a q).map (sameMoleculeCursor h) =
      TetraStereo.Engine.RingRetainedAuxiliary.frame b (sameMoleculeOccurrenceEquiv h fuel q) := by
  exact sameMolecule_children_map h ⟨q, none⟩

/-- All three official atom-label projections are coordinate independent. -/
theorem sameMolecule_atomLabel {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule)
    (f : a.LocalizedCIPOccurrenceFrame) :
    b.moleculeGraph.officialNodeAtomLabel (sameMoleculeFrame h f).node =
      a.moleculeGraph.officialNodeAtomLabel f.node := by
  rcases a with ⟨⟨⟨ma, sa, da⟩, wa⟩, ga⟩
  rcases b with ⟨⟨⟨mb, sb, db⟩, wb⟩, gb⟩
  dsimp at h
  subst mb
  rfl

theorem sameMolecule_rule1b {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule)
    (f : a.LocalizedCIPOccurrenceFrame) :
    (sameMoleculeFrame h f).node.rule1bRootDistance = f.node.rule1bRootDistance := by
  rcases a with ⟨⟨⟨ma, sa, da⟩, wa⟩, ga⟩
  rcases b with ⟨⟨⟨mb, sb, db⟩, wb⟩, gb⟩
  dsimp at h
  subst mb
  rfl

/-- Every observed constitutional comparison on transported retained keys agrees. -/
theorem sameMolecule_compareObserved {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule)
    (left right : ExactOfficialRuleMajorKey a.Atom) :
    ExactOfficialRuleMajorKey.compareObserved b.moleculeGraph
      b.certified.input.molecule.semanticExactOfficialRule1aObservation
      (cast (congrArg (fun m => ExactOfficialRuleMajorKey (Fin m.atomCount)) h) left)
      (cast (congrArg (fun m => ExactOfficialRuleMajorKey (Fin m.atomCount)) h) right) =
    ExactOfficialRuleMajorKey.compareObserved a.moleculeGraph
      a.certified.input.molecule.semanticExactOfficialRule1aObservation left right := by
  rcases a with ⟨⟨⟨ma, sa, da⟩, wa⟩, ga⟩
  rcases b with ⟨⟨⟨mb, sb, db⟩, wb⟩, gb⟩
  dsimp at h
  subst mb
  rfl

/-- Physical walks transport on the same constitutional graph, independently of geometry. -/
def sameMoleculeWalk {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule)
    {x y : a.Atom} (walk : a.moleculeGraph.underlyingSimpleGraph.Walk x y) :
    b.moleculeGraph.underlyingSimpleGraph.Walk (sameMoleculeAtom h x) (sameMoleculeAtom h y) := by
  rcases a with ⟨⟨⟨ma, sa, da⟩, wa⟩, ga⟩
  rcases b with ⟨⟨⟨mb, sb, db⟩, wb⟩, gb⟩
  dsimp at h
  subst mb
  exact walk

theorem sameMoleculeWalk_isPath {a b : CertifiedLocalizedCIPInput}
    (h : a.certified.input.molecule = b.certified.input.molecule)
    {x y : a.Atom} (walk : a.moleculeGraph.underlyingSimpleGraph.Walk x y)
    (simple : walk.IsPath) : (sameMoleculeWalk h walk).IsPath := by
  rcases a with ⟨⟨⟨ma, sa, da⟩, wa⟩, ga⟩
  rcases b with ⟨⟨⟨mb, sb, db⟩, wb⟩, gb⟩
  dsimp at h
  subst mb
  exact simple

assert_kernel_only sameMolecule_subtree
assert_kernel_only sameMolecule_mem
assert_kernel_only sameMoleculeCursor
assert_kernel_only sameMoleculeOccurrenceEquiv
assert_kernel_only sameMolecule_mem_iff
assert_kernel_only sameMoleculeWalk
assert_kernel_only sameMolecule_subtree_map
assert_kernel_only sameMolecule_atomLabel
assert_kernel_only sameMolecule_rule1b
assert_kernel_only sameMolecule_compareObserved
assert_kernel_only sameMolecule_children_map
assert_kernel_only sameMolecule_retained_frame_map
assert_kernel_only sameMolecule_intended_map
assert_kernel_only sameMolecule_occurrences_map
assert_kernel_only sameMoleculeWalk_isPath
end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
