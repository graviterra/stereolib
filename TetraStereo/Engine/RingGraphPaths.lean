import TetraStereo.Engine.RingSphereQueue

/-! Real visits in a retained ring digraph are precisely the simple bonded paths of the
original molecular graph. Paths are written newest atom first, as in the molecular reader.
The construction includes the empty walk at its root. -/

set_option autoImplicit false

namespace TetraStereo.Engine.RingGraphPaths
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (distance)

inductive Path (i : Input) (root : i.certified.Atom) : List i.certified.Atom → i.certified.Atom → Prop where
  | origin : Path i root [root] root
  | step {history current next} (prior : Path i root history current)
      (bond : i.certified.moleculeGraph.Adj current next) (fresh : next ∉ history) :
      Path i root (next :: history) next

def Represents {i : Input} (q : Site i) (root : i.certified.Atom)
    (history : List i.certified.Atom) (atom : i.certified.Atom) : Prop :=
  q.val.root = root ∧ q.val.node.history = history ∧
  q.val.node.provenance = .realAtom ∧ q.val.node.current? = some atom

/-- Follow the atom history and reconstruct each original child slot. Each step selects the bonded atom
from the current node’s child inventory. -/
private def position (i : Input) (r : i.certified.Atom) :
    List i.certified.Atom → OfficialCIPNode i.certified.Atom × List Nat
  | [] => (.root r,[])
  | a :: h =>
    if h = [] then (.root r,[]) else
      let p := position i r h
      (p.1.extend a 0, p.2 ++ [i.certified.executableOfficialChildCopySlot p.1 a 0])

private theorem nonempty {i r h a} (p : Path i r h a) : h ≠ [] := by cases p <;> simp

private theorem position_spec {i r h a} (p : Path i r h a) :
    let pos := position i r h
    SimpleOccurrencePath i.certified r pos.1 pos.2 ∧ pos.1.history = h ∧ pos.1.current? = some a := by
  induction p with
  | origin => exact ⟨.root,rfl,rfl⟩
  | step prior bond fresh ih =>
    obtain ⟨valid,hist,atom⟩ := ih
    have newAtom := fun mem => fresh (hist ▸ mem)
    simp only [position,if_neg (nonempty prior)]
    exact ⟨.step valid atom bond (fun eqn => newAtom (i.certified.parent_mem_history_of_parent? eqn))
      newAtom,by rw [OfficialCIPNode.extend_history,hist],rfl⟩

/-- Executable conversion of a graph path to its retained site, without searching the carrier. -/
def site {i r h a} (p : Path i r h a) : Site i :=
  let leg := LegitimateOccurrence.simple (position_spec p).1
  ⟨_,i.certified.legitimateOccurrence_mem_localizedOccurrences_of_fuel leg
    (Nat.le_succ_of_le (i.certified.legitimateOccurrence_address_length_le_atomCount leg))⟩

theorem represents_site {i r h a} (p : Path i r h a) : Represents (site p) r h a :=
  ⟨rfl,(position_spec p).2.1,i.certified.simpleOccurrencePath_provenance (position_spec p).1,
    (position_spec p).2.2⟩

theorem unique_site {i r h a} {q t : Site i}
    (hq : Represents q r h a) (ht : Represents t r h a) : q = t := by
  apply i.certified.molecularFrameUnit_injective_on_simpleBonded_carrier i.single
  simp only [molecularFrameUnit,hq.1,ht.1,hq.2.1,ht.2.1]

/-- Every simple path gives one full address in the retained digraph, even when several
simple paths have the same endpoints. No connectedness or acyclicity assumption is needed. -/
theorem path_site {i r h a} (p : Path i r h a) : ∃! q : Site i, Represents q r h a := by
  exact ⟨site p,represents_site p,fun _ other => unique_site other (represents_site p)⟩

private theorem ofSimple {i : Input} {r n addr} (p : SimpleOccurrencePath i.certified r n addr) :
    ∃ a, n.current? = some a ∧ Path i r n.history a := by
  induction p with
  | root => exact ⟨_,rfl,.origin⟩
  | step prev atom bond _ fresh ih =>
    obtain ⟨a,ha,prior⟩ := ih
    obtain rfl := Option.some.inj (ha.symm.trans atom)
    exact ⟨_,rfl,.step prior bond fresh⟩

theorem site_path {i : Input} (q : Site i) (real : q.val.node.provenance = .realAtom) :
    ∃ a, q.val.node.current? = some a ∧ Path i q.val.root q.val.node.history a :=
  ofSimple (i.certified.simpleOccurrencePath_of_carrier_real i.single q real)

theorem path_length {i r h a} {q : Site i} (rep : Represents q r h a) :
    h.length = distance q + 1 := by
  rw [← rep.2.1]
  exact i.certified.carrierOccurrence_history_length_eq_address_succ q

/-- The complete auxiliary inventory can be specified with bonds, simple paths and valence. -/
theorem auxiliary_iff {i : Input} (r : i.certified.Atom) (q : Site i) :
    RingSphereQueue.candidate r q ↔ ∃ h a, Path i r h a ∧ Represents q r h a ∧
      a ≠ r ∧ Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by
  rw [RingSphereQueue.candidate_iff]
  constructor
  · rintro ⟨root,real,a,atom,other,four⟩
    obtain ⟨b,hb,path⟩ := site_path q real
    obtain rfl := Option.some.inj (hb.symm.trans atom)
    exact ⟨_,_,root ▸ path,⟨root,rfl,real,hb⟩,other,four⟩
  · rintro ⟨h,a,_,rep,other,four⟩
    exact ⟨rep.1,rep.2.2.1,a,rep.2.2.2,other,four⟩

end TetraStereo.Engine.RingGraphPaths

assert_kernel_only TetraStereo.Engine.RingGraphPaths.path_site
assert_kernel_only TetraStereo.Engine.RingGraphPaths.site_path
assert_kernel_only TetraStereo.Engine.RingGraphPaths.auxiliary_iff
