import Mathlib.Data.List.NodupEquivFin
import TetraStereo.Engine.RingTerminalTwinRefusal

/-! A graph-only partial specification for the first atomic-number comparison.
It works in original atom IDs and uses no CIP digraph, sphere or auxiliary store. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingAtomicNeighborOrder
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingRawRenumbering (molecularRecord)
open RingHydrogenSpelling (TwinPair)
open RingStereoSiblingPass (order legal_order)

def atomicNumber (m : RawMolecule) (n : Nat) : Nat :=
  ((m.atoms[n]?).map (fun atom => atom.element.atomicNumber)).getD 0

/-- One ID per bonded atom, in descending atomic number. -/
def neighbors (m : RawMolecule) (a : Nat) : List Nat :=
  order (atomicNumber m) ((List.range m.atomCount).filter fun n => 0 < m.bondOrder a n)

theorem mem_neighbors {m : RawMolecule} {a n : Nat} :
    n ∈ neighbors m a ↔ n < m.atomCount ∧ 0 < m.bondOrder a n := by
  unfold neighbors
  rw [(legal_order (atomicNumber m) _).perm.mem_iff]
  simp

private theorem neighbors_nodup (m : RawMolecule) (a : Nat) : (neighbors m a).Nodup :=
  (legal_order (atomicNumber m) _).perm.nodup_iff.mpr ((List.nodup_range).filter _)

def separated (m : RawMolecule) (a : Nat) : Bool :=
  decide (((neighbors m a).map (atomicNumber m)).Nodup)

private theorem raw_adj (i : Input) (a b : i.certified.Atom) :
    i.certified.moleculeGraph.Adj a b ↔ 0 < i.molecule.bondOrder a.val b.val :=
  LocalizedChemicalRingPhysicalSense.adj_iff i.molecule i.certified i.agreement
    i.admissible.1.1 i.admissible.1.2 i.supported a b

private theorem bound (i : Input) (a : i.certified.Atom) : a.val < i.molecule.atomCount := by
  rw [←i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1]
  exact a.isLt

private def toAtom (i : Input) (n : Nat) (h : n < i.molecule.atomCount) : i.certified.Atom :=
  ⟨n,by rw [i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1]; exact h⟩

private def neighborEquiv (i : Input) (a : i.certified.Atom) :
    {n // n ∈ neighbors i.molecule a.val} ≃ i.certified.moleculeGraph.Neighbor a where
  toFun n := ⟨toAtom i _ (mem_neighbors.mp n.property).1,(raw_adj i a _).mpr (mem_neighbors.mp n.property).2⟩
  invFun b := ⟨b.val.val,mem_neighbors.mpr ⟨bound i b.val,(raw_adj i a _).mp b.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def enumeration (i : Input) (a : i.certified.Atom) {d : Nat} (size : (neighbors i.molecule a.val).length = d) :
    Fin d ≃ i.certified.moleculeGraph.Neighbor a :=
  ((finCongr size.symm).trans ((neighbors_nodup _ _).getEquiv _)).trans (neighborEquiv i a)

theorem degree_eq (i : Input) (a : i.certified.Atom) :
    Fintype.card (i.certified.moleculeGraph.Neighbor a) = (neighbors i.molecule a.val).length := by
  simpa using (Fintype.card_congr (enumeration i a rfl)).symm

def record (i : Input) (a : i.certified.Atom) : AtomSpec := i.molecule.atoms[a.val]'(bound i a)

theorem written (i : Input) (a : i.certified.Atom) :
    i.molecule.atoms[a.val]? = some (record i a) := List.getElem?_eq_getElem (bound i a)

theorem enumeration_descending (i : Input) (a : i.certified.Atom) {d : Nat}
    (size : (neighbors i.molecule a.val).length = d) (sep : separated i.molecule a.val = true) :
    StrictAnti (fun k => (record i ((enumeration i a size) k).val).element.atomicNumber) := by
  have nodup := of_decide_eq_true sep
  have decr := (legal_order (atomicNumber i.molecule)
    ((List.range i.molecule.atomCount).filter fun n => 0 < i.molecule.bondOrder a.val n)).descending
  change ((neighbors i.molecule a.val).map (atomicNumber i.molecule)).Pairwise (· ≥ ·) at decr
  have strict := (decr.and nodup).imp (fun h => lt_of_le_of_ne h.1 (Ne.symm h.2))
  intro k l before
  have facts := List.pairwise_iff_getElem.mp strict k l (by simp [size]) (by simp [size]) before
  have z (j : Fin d) : atomicNumber i.molecule ((enumeration i a size j).val.val) =
      (record i ((enumeration i a size) j).val).element.atomicNumber := by simp [atomicNumber,written]
  change (record i ((enumeration i a size) l).val).element.atomicNumber <
    (record i ((enumeration i a size) k).val).element.atomicNumber
  rw [←z l,←z k]
  simp only [List.getElem_map] at facts
  exact facts

theorem enumeration_ids (i : Input) (a : i.certified.Atom) {d : Nat}
    (size : (neighbors i.molecule a.val).length = d) :
    (List.finRange d).map (fun k => (enumeration i a size k).val.val) = neighbors i.molecule a.val := by
  apply List.ext_getElem
  · simp [size]
  · intros; simp [enumeration,neighborEquiv,toAtom,List.Nodup.getEquiv]

/-- Two equal molecular records whose only bonds are single bonds to this parent. -/
def terminalTwins (m : RawMolecule) (a : Nat) : Prop :=
  ∃ u ∈ neighbors m a, ∃ v ∈ neighbors m a, u ≠ v ∧
    (m.atoms[u]?).map molecularRecord = (m.atoms[v]?).map molecularRecord ∧
    ∀ n ∈ List.range m.atomCount, m.bondOrder u n = (if n = a then 1 else 0) ∧
      m.bondOrder v n = (if n = a then 1 else 0)

instance (m : RawMolecule) (a : Nat) : Decidable (terminalTwins m a) := by
  unfold terminalTwins
  infer_instance

theorem twinPair_of_test (i : Input) (a : i.certified.Atom) (four : (neighbors i.molecule a.val).length = 4)
    (twins : terminalTwins i.molecule a.val) : ∃ p : TwinPair i, p.c.val = a := by
  obtain ⟨u,hu,v,hv,ne,records,edges⟩ := twins
  let c : i.certified.TetrahedralCenter := ⟨a,(i.certified.moleculeGraph.mem_tetrahedralCenterSet a).mpr
    ((degree_eq i a).trans four)⟩
  let U := toAtom i u (mem_neighbors.mp hu).1
  let V := toAtom i v (mem_neighbors.mp hv).1
  refine ⟨⟨c,U,V,fun eqn => ne (congrArg Fin.val eqn),records,?_,?_⟩,rfl⟩
  · intro b
    simpa only [Fin.ext_iff] using (edges b.val (List.mem_range.mpr (bound i b))).1
  · intro b
    simpa only [Fin.ext_iff] using (edges b.val (List.mem_range.mpr (bound i b))).2

/-- A completed refusal or a priority-ordered list of physical point IDs. -/
inductive Decision where
  | refuse
  | ranked (points : List Nat)
  deriving DecidableEq, Repr

def neutralPyramidal (m : RawMolecule) (a : Nat) : Bool :=
  (m.atoms[a]?).any (fun atom => ((atom.element == .P || atom.element == .As || atom.element == .Sb) ||
    (atom.element == .N && RingPyramidalNitrogen.constrainedRaw m a)) && atom.charge == 0 && !atom.aromatic)

/-- Cheap record and element gates precede structural nitrogen search. -/
def neutralPyramidalFast (m : RawMolecule) (a : Nat) : Bool :=
  (m.atoms[a]?).any fun atom => atom.charge == 0 && !atom.aromatic &&
    ((atom.element == .P || atom.element == .As || atom.element == .Sb) ||
      (atom.element == .N && RingPyramidalNitrogen.constrainedRaw m a))

@[csimp] theorem neutralPyramidal_fast : @neutralPyramidal = @neutralPyramidalFast := by
  funext m a
  unfold neutralPyramidal neutralPyramidalFast
  cases lookup : m.atoms[a]? with
  | none => rfl
  | some atom =>
    apply Bool.eq_iff_iff.mpr
    simp only [Option.any_some,Bool.and_eq_true,Bool.or_eq_true]
    aesop

/-- A partial graph-only decision. A tied first shell outside the terminal-twin
class leaves the decision open for later rules. -/
def classify? (m : RawMolecule) (a : Nat) : Option Decision :=
  if a < m.atomCount then
    let ns := neighbors m a
    if ns.length = 4 then
      if separated m a then some (.ranked ns)
      else if terminalTwins m a then some .refuse else none
    else if neutralPyramidal m a && ns.length == 3 then
      if separated m a then some (.ranked (ns ++ [a])) else none
    else some .refuse
  else none

/-- The degree-three gate runs before the potentially expensive nitrogen test. -/
def classifyFast? (m : RawMolecule) (a : Nat) : Option Decision :=
  if a < m.atomCount then
    let ns := neighbors m a
    if ns.length = 4 then
      if separated m a then some (.ranked ns)
      else if terminalTwins m a then some .refuse else none
    else if ns.length == 3 && neutralPyramidal m a then
      if separated m a then some (.ranked (ns ++ [a])) else none
    else some .refuse
  else none

@[csimp] theorem classify_fast : @classify? = @classifyFast? := by
  funext m a
  simp only [classify?,classifyFast?,Bool.and_comm]

def Decision.read (d : Decision) (x : SpatialConfiguration) : Option RingNestedActivePair.Labels :=
  match d with
  | .refuse => none
  | .ranked points =>
    (LocalizedGenericMarkedRecalculation.readback? (RingWrittenPHReadings.geometry x) points).map
      fun h => (.chiral h,.chiral h.swap)

/-- Direct requested rows, in order, computed solely from atom and bond records
and the four physical points for each assigned center. -/
def directReport? (m : RawMolecule) (x : SpatialConfiguration) (ids : List Nat) : Option RingGroupedReport.Report :=
  ids.mapM fun a => (classify? m a).map fun d => (a,d.read x)

end TetraStereo.Engine.RingAtomicNeighborOrder
assert_kernel_only TetraStereo.Engine.RingAtomicNeighborOrder.enumeration_descending
assert_kernel_only TetraStereo.Engine.RingAtomicNeighborOrder.twinPair_of_test

assert_kernel_only TetraStereo.Engine.RingAtomicNeighborOrder.neutralPyramidal_fast
assert_kernel_only TetraStereo.Engine.RingAtomicNeighborOrder.classify_fast
