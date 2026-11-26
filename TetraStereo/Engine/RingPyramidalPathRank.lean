import TetraStereo.Engine.RingTerminalLigandOrder

/-! Executable path-aware rank using only raw atom/bond records and the stored
physical path. It reconstructs neither a ligand digraph nor an auxiliary view. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPyramidalPathRank
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingPyramidalSource (Directions slots atomId)
open RingPyramidalTwoShell (direction)
open private direction_rank from TetraStereo.Engine.RingPyramidalConstitution

def realEndpoint (history : List Nat) (parent : Option Nat) (w : Nat) : Bool :=
  decide (parent = some w ∨ w ∉ history)

def rank (m : RawMolecule) (focus : Nat) (history : List Nat) (parent : Option Nat)
    (w : Nat) : List RingRetainedChemicalTrace.Word :=
  let real := realEndpoint history parent w
  let row := if real then RingSecondShellDecision.shell m focus w else []
  [[[RingAtomicNeighborOrder.atomicNumber m w],row],
    [[if row = [] then if real then 0 else m.atomCount + 1 - history.reverse.idxOf w else 0]]]

def atSite (i : Input) (q : Site i) (a : i.certified.Atom) (w : Nat) :=
  rank i.molecule a.val (q.val.node.history.map Fin.val) (q.val.node.parent?.map Fin.val) w

private theorem mapped_idx {k : Nat} (xs : List (Fin k)) (w : Fin k) :
    (xs.map Fin.val).idxOf w.val = xs.idxOf w := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases eqn : a = w
    · subst a; simp
    · have ne : a.val ≠ w.val := fun eq => eqn (Fin.ext eq)
      simpa only [List.map_cons,List.idxOf_cons_ne _ ne,List.idxOf_cons_ne _ eqn] using congrArg Nat.succ ih

private theorem original_index {i : Input} (q : Site i)
    (real : q.val.node.provenance = .realAtom) (w : i.certified.Atom)
    (visited : w ∈ q.val.node.history) :
    (q.val.node.history.map Fin.val).reverse.idxOf w.val = q.val.node.duplicateRootDistance w := by
  obtain ⟨index,_,distance,bound,lookup⟩ :=
    OutwardRule1bObserverEquivalence.duplicateRootDistance_eq_firstIndex q.val.node w visited
  have rb : index < q.val.node.history.reverse.length := by simpa using bound
  have get : q.val.node.history.reverse[index] = w := by
    simpa only [List.getElem?_eq_getElem rb,Option.some.injEq] using lookup
  have nd : q.val.node.history.reverse.Nodup := List.nodup_reverse.mpr (RingPyramidalPathProvenance.history_nodup q real)
  have idx := nd.idxOf_getElem index rb
  rw [get] at idx
  rw [← List.map_reverse,mapped_idx,idx,distance]

/-- The raw path rank equals the actual retained-direction rank at every real
occurrence, including parent arms and terminal closures. -/
theorem rank_direction {i : Input} {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (d : Directions i q) (s : Fin 3) :
    atSite i q a (atomId d s) = RingTerminalLigandOrder.rank (direction d s) := by
  have classify := RingPyramidalPathProvenance.arm_endpoint q a (d.atom s)
    real current (d.arm s) (d.mem s) (d.real s)
  have member : (d.atom s).val ∈ q.val.node.history.map Fin.val ↔ d.atom s ∈ q.val.node.history := by
    simp only [List.mem_map,Fin.val_inj]
    simp
  have parent : q.val.node.parent?.map Fin.val = some (d.atom s).val ↔
      q.val.node.parent? = some (d.atom s) := by
    cases q.val.node.parent? <;> simp [Fin.ext_iff]
  have endpoint : realEndpoint (q.val.node.history.map Fin.val)
      (q.val.node.parent?.map Fin.val) (d.atom s).val = true ↔
      (d.arm s).occurrence.val.node.provenance = .realAtom := by
    simp only [realEndpoint,decide_eq_true_eq,parent,member]
    exact classify.1.symm
  have rowEq : RingTerminalLigandOrder.twoRows (direction d s) =
      [[RingAtomicNeighborOrder.atomicNumber i.molecule (atomId d s)],
        if (d.arm s).occurrence.val.node.provenance = .realAtom then
          RingSecondShellDecision.shell i.molecule a.val (atomId d s) else []] := by
    simp [RingTerminalLigandOrder.twoRows,RingSecondShellDecision.prefixFor,
      RingAllLigandTwoShell.siteAtom,current,direction,d.real s,atomId]
  unfold RingTerminalLigandOrder.rank RingTerminalLigandOrder.bonus
  rw [rowEq]
  by_cases childReal : (d.arm s).occurrence.val.node.provenance = .realAtom
  · have yes := endpoint.mpr childReal
    simp [atSite,rank,
      yes,childReal,RingTerminalLigandOrder.duplicate,direction,atomId]
  · have notParent : q.val.node.parent? ≠ some (d.atom s) := fun back => childReal (classify.1.mpr (Or.inl back))
    have visited : d.atom s ∈ q.val.node.history := by
      by_contra off
      exact childReal (classify.1.mpr (Or.inr off))
    have duplicate := (classify.2 notParent visited).1
    have no : realEndpoint (q.val.node.history.map Fin.val)
        (q.val.node.parent?.map Fin.val) (d.atom s).val = false := by
      cases h : realEndpoint _ _ _ with
      | false => rfl
      | true => exact (childReal (endpoint.mp h)).elim
    simp [atSite,rank,
      no,RingTerminalLigandOrder.duplicate,direction,atomId,duplicate,
      original_index q real (d.atom s) visited]

/-- Every framed pyramidal enumeration lists exactly the raw physical neighbor
IDs; neither auxiliary path nor enumeration order changes their multiplicity. -/
theorem neighbors_perm {i : Input} {q : Site i} {a : i.certified.Atom}
    (d : Directions i q) (selected : RingPyramidalPublication.focusP i q = some a) :
    (slots.map (atomId d)).Perm (RingAtomicNeighborOrder.neighbors i.molecule a.val) := by
  have hp := RingPhysicalFrameBridge.focusP_phosphorus selected
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3 := by
    simp only [RingPyramidalPublication.phosphorus,Bool.and_eq_true,decide_eq_true_eq] at hp
    exact hp.2
  have size := (RingAtomicNeighborOrder.degree_eq i a).symm.trans degree
  let enum := RingAtomicNeighborOrder.enumeration i a size
  obtain ⟨e,matched⟩ := direction_rank d selected enum
  have perm := (Equiv.Perm.map_finRange_perm e).map (fun s => (enum s).val.val)
  rw [List.map_map] at perm
  have keyEq : atomId d = fun s => (enum (e s)).val.val :=
    funext fun s => congrArg Fin.val (matched s)
  rw [keyEq]
  have base : (List.finRange 3).map (fun s => (enum s).val.val) =
      RingAtomicNeighborOrder.neighbors i.molecule a.val := RingAtomicNeighborOrder.enumeration_ids i a size
  exact perm.trans (List.Perm.of_eq base)
end TetraStereo.Engine.RingPyramidalPathRank
assert_kernel_only TetraStereo.Engine.RingPyramidalPathRank.rank_direction
assert_kernel_only TetraStereo.Engine.RingPyramidalPathRank.neighbors_perm
