import TetraStereo.OneCenter.LocalizedRealizedTreeCutEmbedding
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput























variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
variable {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}

/-! ## Every actually reachable cursor is the source of an actual position -/

/-- **Coverage of positions by actual reachability.**  From a recursively realized tree and an
actual executable-child path from its source, the reached cursor is the source of an actual
position of the tree.

The proof is the plain `ReflTransGen` tail induction.  At a tail step the induction hypothesis
supplies a position whose decorated subtree has the current cursor as source; the child is
realized recursively, so its sorted children's sources are a permutation of the executable child
frame.  Membership of the next cursor in that frame therefore gives an actual sorted child slot,
and `positionChild` lifts that slot to a position. -/
theorem exists_position_of_actualChildReachable
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (reachable : input.ActualChildReachable tree.source cursor) :
    ∃ p : Position tree, positionSource p = cursor := by
  induction reachable with
  | refl => exact ⟨rootPosition tree, by simp⟩
  | @tail b c _path step ih =>
      obtain ⟨p, hp⟩ := ih
      let node := positionNode p
      have nodeRealizes : LocalizedCumulativeTreeRealizes input read node :=
        realizes_of_subtree realizes (positionNode_spec p)
      obtain ⟨perm, _executable⟩ := exists_sourcePerm_executable nodeRealizes
      have nodeSource : node.source = b := by
        simpa [node, positionSource] using hp
      have cursorMemExec : c ∈ input.executableLocalizedRerootChildren node.source := by
        simpa [nodeSource] using step
      have cursorMemMap : c ∈ node.children.map (fun child => child.source) :=
        perm.mem_iff.mpr cursorMemExec
      obtain ⟨child, childMem, childSource⟩ := List.mem_map.mp cursorMemMap
      obtain ⟨slot, slotBound, slotEq⟩ := List.mem_iff_getElem.mp childMem
      have nodeChild : positionNode (positionChild p slot slotBound) = child := by
        rw [positionNode_positionChild]
        exact slotEq
      refine ⟨positionChild p slot slotBound, ?_⟩
      rw [show positionSource (positionChild p slot slotBound) =
          (positionNode (positionChild p slot slotBound)).source from rfl]
      rw [nodeChild]
      exact childSource

/-! ## Surjectivity onto the physical cut branch -/






theorem exists_position_of_mem_cutBranch
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    {w : input.Atom}
    (mem : w ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom) :
    ∃ p : Position tree, positionAtom singleBonded acyclic p = w := by
  obtain ⟨target, reachable, targetObserved⟩ :=
    (input.actualChildReachable_current_iff_cutBranch_general singleBonded acyclic enough
      tree.source previous previousEq sameRoot valid oObserved pObserved incomingEdge w).mpr mem
  obtain ⟨p, hp⟩ := exists_position_of_actualChildReachable realizes reachable
  refine ⟨p, ?_⟩
  have observed := positionAtom_spec singleBonded acyclic p
  rw [hp] at observed
  exact Option.some.inj (observed.symm.trans targetObserved)

/-! ## The actual position/cut-branch equivalence -/






noncomputable def positionCutEquiv
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom) :
    Position tree ≃ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom :=
  Equiv.ofBijective
    (fun p : Position tree =>
      ⟨positionAtom singleBonded acyclic p,
        positionAtom_mem_cutBranch singleBonded acyclic enough realizes previous previousEq
          valid oObserved pObserved incomingEdge p⟩)
    ⟨fun p q imageEq =>
        positionAtom_injective singleBonded acyclic enough realizes previous previousEq
          sameRoot oObserved pObserved p q (congrArg Subtype.val imageEq),
      fun a => by
        obtain ⟨p, hp⟩ :=
          exists_position_of_mem_cutBranch singleBonded acyclic enough realizes previous
            previousEq valid sameRoot oObserved pObserved incomingEdge a.property
        exact ⟨p, Subtype.ext hp⟩⟩

/-- The forward map of `positionCutEquiv` is exactly the physical atom of the position. -/
@[simp] theorem positionCutEquiv_apply_coe
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (p : Position tree) :
    ((positionCutEquiv singleBonded acyclic enough realizes previous previousEq valid
        sameRoot oObserved pObserved incomingEdge p :
          AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom) :
        input.Atom) =
      positionAtom singleBonded acyclic p :=
  rfl

/-- The position recovered from a branch atom carries exactly that atom. -/
theorem positionAtom_positionCutEquiv_symm
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (a : AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom) :
    positionAtom singleBonded acyclic
        ((positionCutEquiv singleBonded acyclic enough realizes previous previousEq valid
          sameRoot oObserved pObserved incomingEdge).symm a) =
      (a : input.Atom) := by
  have h := congrArg Subtype.val
    (Equiv.apply_symm_apply
      (positionCutEquiv singleBonded acyclic enough realizes previous previousEq valid
        sameRoot oObserved pObserved incomingEdge) a)
  simpa only [positionCutEquiv_apply_coe] using h

/-- **The root position maps to the attachment atom.** -/
theorem positionCutEquiv_rootPosition
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom) :
    positionCutEquiv singleBonded acyclic enough realizes previous previousEq valid
        sameRoot oObserved pObserved incomingEdge (rootPosition tree) =
      ⟨oAtom,
        AcyclicCutBranchAutomorphism.cutBranch_mem_self input.moleculeGraph incomingEdge⟩ := by
  apply Subtype.ext
  rw [positionCutEquiv_apply_coe]
  exact positionAtom_rootPosition singleBonded acyclic tree oObserved

/-- **The equivalence preserves the actual Rule-1a atomic number.** -/
theorem positionCutEquiv_atomZ
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (p : Position tree) :
    input.moleculeGraph.atomZ
        ((positionCutEquiv singleBonded acyclic enough realizes previous previousEq valid
          sameRoot oObserved pObserved incomingEdge p :
            AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom) :
          input.Atom) =
      (positionNode p).atomicNumber := by
  rw [positionCutEquiv_apply_coe]
  exact (positionAtomicNumber_eq_atomZ singleBonded acyclic realizes p).symm

/-- **The equivalence preserves the actual Rule-2 isotope mass.** -/
theorem positionCutEquiv_atomMass
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (p : Position tree) :
    input.moleculeGraph.atomMass
        ((positionCutEquiv singleBonded acyclic enough realizes previous previousEq valid
          sameRoot oObserved pObserved incomingEdge p :
            AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom) :
          input.Atom) =
      (positionNode p).isotopeMass := by
  rw [positionCutEquiv_apply_coe]
  exact (positionIsotopeMass_eq_atomMass singleBonded acyclic realizes p).symm









theorem positionCutEquiv_adj_iff
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (p q : Position tree) :
    input.moleculeGraph.Adj
        ((positionCutEquiv singleBonded acyclic enough realizes previous previousEq valid
          sameRoot oObserved pObserved incomingEdge p :
            AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom) :
          input.Atom)
        ((positionCutEquiv singleBonded acyclic enough realizes previous previousEq valid
          sameRoot oObserved pObserved incomingEdge q :
            AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom) :
          input.Atom) ↔
      PositionAdjacent p q := by
  rw [positionCutEquiv_apply_coe, positionCutEquiv_apply_coe]
  exact positionAtom_adjacent_iff_positionAdjacent singleBonded acyclic enough realizes
    previous previousEq sameRoot valid oObserved pObserved incomingEdge p q

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.exists_position_of_actualChildReachable
assert_kernel_only TetraStereo.OneCenter.exists_position_of_mem_cutBranch
assert_kernel_only TetraStereo.OneCenter.positionCutEquiv
assert_kernel_only TetraStereo.OneCenter.positionCutEquiv_apply_coe
assert_kernel_only TetraStereo.OneCenter.positionAtom_positionCutEquiv_symm
assert_kernel_only TetraStereo.OneCenter.positionCutEquiv_rootPosition
assert_kernel_only TetraStereo.OneCenter.positionCutEquiv_atomZ
assert_kernel_only TetraStereo.OneCenter.positionCutEquiv_atomMass
assert_kernel_only TetraStereo.OneCenter.positionCutEquiv_adj_iff

end TetraStereo.OneCenter
