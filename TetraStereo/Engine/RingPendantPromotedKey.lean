import TetraStereo.Engine.RingPendantReferenceRoles
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmPrior

set_option autoImplicit false

namespace TetraStereo.Engine.RingPendantPromotedKey
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingPendantReferenceRoles (Side rawAtom)
open LocalizedCumulativeDecoratedTree (LocalizedRerootCursorIncomingParent)
open LocalizedMarkedRetainedPromotedKey (ordinaryKey?)
open LocalizedMarkedRetainedSparsePromotedKey (sparseCompareAt?)

/-- Verify a proposed side by examining every actual molecular bond. -/
def side? (i : Input) (gate first : RingRetainedTerminalClass.Atom i)
    (atoms : Finset (RingRetainedTerminalClass.Atom i)) : Option (Side i gate) :=
  if h : gate ∉ atoms ∧ first ∈ atoms ∧ i.molecule.toMoleculeGraph.Adj gate first ∧
      ∀ x ∉ atoms, ∀ y ∈ atoms, i.molecule.toMoleculeGraph.Adj x y → x = gate ∧ y = first then
    some ⟨atoms,first,h.1,h.2.1,h.2.2.1,h.2.2.2⟩
  else none

/-- The entry of a pendant side as an actual original-digraph child. Immediate
backtracking is cut at the parent and subsequent visits to the entry are leaves. -/
structure Outward {i : Input} {gate : i.certified.Atom} (s : Side i (rawAtom gate)) (arm : Arm i) where
  entry : i.certified.Atom
  first : rawAtom entry = s.first
  current : arm.occurrence.val.node.current? = some entry
  parent : arm.occurrence.val.node.parent? = some gate
  incoming : LocalizedRerootCursorIncomingParent i.certified arm

private theorem atom_eq {i : Input} {a b : i.certified.Atom} (h : rawAtom a = rawAtom b) : a = b :=
  Fin.ext (congrArg (fun z : RingRetainedTerminalClass.Atom i => z.val) h)

/-- Every node of the official subtree has an atom on the same side, including
ring-closure duplicates. A duplicate return to the entry cannot cross out. -/
theorem Outward.subtree {i gate} {s : Side i (rawAtom gate)} {arm : Arm i} (a : Outward s arm)
    {target : OfficialCIPNode i.certified.Atom}
    (path : Relation.ReflTransGen (fun p q => q ∈ i.certified.executableOfficialCIPChildren p)
      arm.occurrence.val.node target) : ∃ x, target.current? = some x ∧ rawAtom x ∈ s.atoms := by
  have keep : ∃ x, target.current? = some x ∧ rawAtom x ∈ s.atoms ∧ a.entry ∈ target.history ∧
      (x = a.entry → target.parent? = some gate ∨ target.isDuplicateLeaf = true) := by
    induction path with
    | refl =>
      have head := (i.certified.declarativeLocalizedOccurrence_node_history_head_eq_current
        ((i.certified.mem_localizedOccurrences_iff _ arm.occurrence.val).mp arm.occurrence.property)).trans a.current
      exact ⟨a.entry,a.current,a.first ▸ s.inside,List.mem_of_mem_head? head,fun _ => Or.inl a.parent⟩
    | @tail p q _ edge ih =>
      obtain ⟨x,read,interior,history,first⟩ := ih
      unfold executableOfficialCIPChildren at edge
      split at edge
      · simp at edge
      · rename_i active
        obtain ⟨⟨y,k⟩,copy,rfl⟩ := List.mem_map.mp edge
        obtain ⟨_,⟨z,zRead,adj⟩,noParent⟩ := i.certified.simpleBond_childCopy_eq_zero i.single p copy
        have zx := Option.some.inj (zRead.symm.trans read)
        subst z
        have inSide : rawAtom y ∈ s.atoms := by
          by_contra ext
          have edge' : i.molecule.toMoleculeGraph.Adj (rawAtom x) (rawAtom y) :=
            (LocalizedChemicalRingPhysicalSense.adj_iff i.molecule i.certified i.agreement i.admissible.1.1
              i.admissible.1.2 i.supported x y).mp adj
          obtain ⟨atGate,atFirst⟩ := s.crossing _ ext _ interior (i.molecule.toMoleculeGraph.adj_symm.mp edge')
          have back := first (atom_eq (atFirst.trans a.first.symm))
          rcases back with atParent | duplicate
          · exact noParent (atParent.trans (congrArg some (atom_eq atGate).symm))
          · exact active duplicate
        refine ⟨y,rfl,inSide,List.mem_cons_of_mem y history,?_⟩
        intro hy
        right
        apply MolecularEvidenceTree.isDuplicateLeaf_extend_of_ne
        intro real
        exact ((MolecularEvidenceTree.childProvenance_eq_realAtom_iff p y k).mp real).2 (hy ▸ history)
  obtain ⟨x,current,inside,_,_⟩ := keep
  exact ⟨x,current,inside⟩

/-- A remote mark cannot appear anywhere that the sparse marked builder reads
from this original cursor, including duplicated endpoints. -/
theorem Outward.absent {i gate} {s : Side i (rawAtom gate)} {arm : Arm i} (a : Outward s arm)
    (mark : i.certified.Atom) (outside : rawAtom mark ∉ s.atoms) (target : Arm i)
    (path : Relation.ReflTransGen (fun p q => q ∈ i.certified.executableLocalizedRerootChildren p) arm target) :
    target.occurrence.val.node.current? ≠ some mark := by
  obtain ⟨x,read,interior⟩ := a.subtree
    (LocalizedChemicalRingSealedCursorReference.cursor_forward_path i.certified arm target a.incoming path)
  intro atMark
  exact outside ((Option.some.inj (read.symm.trans atMark)) ▸ interior)

/-- A promoted comparison of two arbitrary-depth pendant arms reads precisely
the ordinary Rules 1–5 comparison at the same frozen view. This equality also
covers strict results, and includes the case where the mark is the attachment. -/
theorem sparse_eq_ordinary {i : Input} {gate : i.certified.Atom} (l r : Side i (rawAtom gate))
    (q : Site i) (view : i.certified.LocalizedDependencyView q)
    (mark : i.certified.Atom) (outerL : rawAtom mark ∉ l.atoms) (outerR : rawAtom mark ∉ r.atoms)
    (W D : Nat) (a b : Arm i) (ha : Outward l a) (hb : Outward r b)
    (validA : i.certified.LocalizedRerootCursorValid a) (validB : i.certified.LocalizedRerootCursorValid b)
    (ka kb : i.certified.LocalizedRerootCompoundRule45Key)
    (priorA : ordinaryKey? i.certified q view a = some ka)
    (priorB : ordinaryKey? i.certified q view b = some kb) :
    sparseCompareAt? i.certified q view mark W D a b =
      some (i.certified.compareLocalizedRerootCompoundThroughRule5 ka kb).ordering :=
  LocalizedChemicalRingAbsentReferenceKey.sparseCompareAt_eq_prior_of_absent i.certified q view mark W D a b
    validA validB (ha.absent mark outerL) (hb.absent mark outerR) ka kb priorA priorB

/-- An incident atom chosen at any proper ancestor of the original target
automatically meets the exclusion in the promoted-key theorem. -/
theorem older_mark_outside {i gate} (s : Side i (rawAtom gate)) (q : Site i)
    (real : q.val.node.provenance = .realAtom) (atGate : q.val.node.current? = some gate)
    (rootOutside : rawAtom q.val.root ∉ s.atoms) (old mark : i.certified.Atom)
    (past : old.val ∈ q.val.node.history.tail.map Fin.val) (bond : i.certified.moleculeGraph.Adj old mark) :
    rawAtom mark ∉ s.atoms := by
  have atRaw : q.val.node.current?.map Fin.val = some (rawAtom gate).val := by rw [atGate]; rfl
  have apart := RingTerminalReferenceRoles.ancestor_ne (old := rawAtom old) q real atRaw past
  have outer := s.ancestor_outside (old := rawAtom old) q real atRaw rootOutside past
  have connected : i.molecule.toMoleculeGraph.Adj (rawAtom old) (rawAtom mark) :=
    (LocalizedChemicalRingPhysicalSense.adj_iff i.molecule i.certified i.agreement i.admissible.1.1
      i.admissible.1.2 i.supported old mark).mp bond
  exact fun hit => apart ((s.choice_iff (rawAtom old,rawAtom mark) outer connected).mp hit).1

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedPromotedRanking LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedPromotedKey
open LocalizedChemicalRingPromotedConstitutionReadback
open LocalizedActualBoundaryObservationReadback LocalizedActualBoundaryPathRealization
open LocalizedActualOutwardRule1bEquivalence LocalizedCyclicGeneralRigidPriority
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)


/-- The physical frame's two complete refined keys remain equal when the older
reference is selected at a proper ancestor outside both pendant arms. The proof
uses the current published state at the exact target. -/
theorem refined_tie_of_ancestor {i : Input} (target : Site i) (gate old reference : i.certified.Atom)
    (l r : Side i (rawAtom gate)) (rootL : rawAtom target.val.root ∉ l.atoms)
    (rootR : rawAtom target.val.root ∉ r.atoms)
    (state : OccurrenceAuxState) (real : target.val.node.provenance = .realAtom)
    (atGate : target.val.node.current? = some gate) (past : old.val ∈ target.val.node.history.tail.map Fin.val)
    (issued : i.certified.moleculeGraph.Adj old reference)
    (unit : DetectedOccurrence i.certified.moleculeGraph) (targetUnit : i.certified.molecularFrameUnit target.val = unit.1)
    (W D : Nat) (left right : Fin 4)
    (ha : Outward l ((frames i.certified i.single state target real unit targetUnit).frame.cursorAt left))
    (hb : Outward r ((frames i.certified i.single state target real unit targetUnit).frame.cursorAt right))
    (prior : rawStateKeys i.certified i.single state target real unit targetUnit left =
      rawStateKeys i.certified i.single state target real unit targetUnit right) :
    refinedKey i.certified i.single state target real unit targetUnit reference W D left =
      refinedKey i.certified i.single state target real unit targetUnit reference W D right := by
  let frame := frames i.certified i.single state target real unit targetUnit
  let view := rawStateView i.certified state target
  have priorL := build?_prior i.certified target view reference W D _ _ _
    (compiled_built i.certified i.single state target real unit targetUnit reference W D left)
  have priorR := build?_prior i.certified target view reference W D _ _ _
    (compiled_built i.certified i.single state target real unit targetUnit reference W D right)
  have sparse := sparse_eq_ordinary l r target view reference
    (older_mark_outside l target real atGate rootL old reference past issued)
    (older_mark_outside r target real atGate rootR old reference past issued)
    W D (frame.frame.cursorAt left) (frame.frame.cursorAt right) ha hb
    (slot_valid i.certified i.single state target real unit targetUnit left)
    (slot_valid i.certified i.single state target real unit targetUnit right) _ _ priorL priorR
  rw [LocalizedMarkedRetainedSparsePromotedKey.sparseCompareAt?_eq,
    compiled_prior i.certified i.single state target real unit targetUnit reference W D left,
    compiled_prior i.certified i.single state target real unit targetUnit reference W D right] at sparse
  have full := frame.fullOrdering (rawStateDescriptorMap_tetrahedral i.certified state)
    i.single unit targetUnit left right
  have keysEq : frame.retainedKeys unit left = frame.retainedKeys unit right := prior
  rw [keysEq, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at full
  rw [full] at sparse
  have refined := before_eq_refined i.certified i.single state target real unit targetUnit reference W D
    left right
  change compareAt? i.certified target view reference W D (frame.frame.cursorAt left)
    (frame.frame.cursorAt right) = _ at refined
  rw [sparse] at refined
  exact (refined_compare_eq_iff _ _).mp (Option.some.inj refined).symm
end TetraStereo.Engine.RingPendantPromotedKey

assert_kernel_only TetraStereo.Engine.RingPendantPromotedKey.Outward.subtree
assert_kernel_only TetraStereo.Engine.RingPendantPromotedKey.Outward.absent
assert_kernel_only TetraStereo.Engine.RingPendantPromotedKey.sparse_eq_ordinary

assert_kernel_only TetraStereo.Engine.RingPendantPromotedKey.older_mark_outside

assert_kernel_only TetraStereo.Engine.RingPendantPromotedKey.refined_tie_of_ancestor
