import TetraStereo.Engine.RingChemicalReport

/-! Compatibility of the former P/As inventory on a fixed prepared graph.
This theorem deliberately makes no claim about raw hydrogen variant generation. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPyramidalInventoryConservation
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (View Cell)

/-- The independent former element policy. -/
def oldElement (e : Element) : Bool := e == .P || e == .As

def selectedBy (element : Element → Bool) (i : Input) (a : i.certified.Atom) : Bool :=
  (i.molecule.atoms[a.val]?).any (fun atom =>
    element atom.element && atom.charge == 0 && !atom.aromatic) &&
    decide (Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3)

def oldSelected := selectedBy oldElement

def oldEligible (i : Input) (a : i.certified.Atom) : Bool :=
  decide (Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4) || oldSelected i a

def focusBy (element : Element → Bool) (i : Input) (q : Site i) : Option i.certified.Atom :=
  if q.val.node.provenance = .realAtom then q.val.node.current?.filter (selectedBy element i) else none

def publishBy (element : Element → Bool) (i : Input) (q : Site i) (r : View i) : Cell :=
  match focusBy element i q with
  | some a => some (RingPyramidalPublication.pLabels i q r a)
  | none => RingFullPathConstitution.fastPublish i q r

def oldPublish := publishBy oldElement

/-- Absence of the antimony extension on the already prepared graph. -/
def NoSelectedSb (i : Input) : Prop :=
  ∀ a : i.certified.Atom, selectedBy (fun e => e == .Sb) i a = false

/-- Original bridgehead-only absence predicate. -/
def NoSelectedBridgeheadN (i : Input) : Prop :=
  ∀ a : i.certified.Atom,
    (selectedBy (fun e => e == .N) i a && RingBridgeheadNitrogen.constrained i a) = false

/-- Absence of all added nitrogen classes on the prepared graph. -/
def NoSelectedNitrogen (i : Input) : Prop :=
  ∀ a : i.certified.Atom,
    (selectedBy (fun e => e == .N) i a && RingPyramidalNitrogen.constrained i a) = false

/-- An N-free prepared atom list is sufficient to exclude the new nitrogen region. -/
theorem NoSelectedNitrogen.of_no_element {i : Input}
    (free : ∀ atom ∈ i.molecule.atoms, atom.element ≠ .N) : NoSelectedNitrogen i := by
  intro a
  unfold selectedBy
  cases lookup : i.molecule.atoms[a.val]? with
  | none => simp
  | some atom =>
    have ne := free atom (List.mem_of_getElem? lookup)
    simp [ne]

theorem NoSelectedBridgeheadN.of_no_element {i : Input}
    (free : ∀ atom ∈ i.molecule.atoms, atom.element ≠ .N) : NoSelectedBridgeheadN i := by
  intro a
  cases lookup : i.molecule.atoms[a.val]? with
  | none => simp [selectedBy,lookup]
  | some atom => simp [selectedBy,lookup,free atom (List.mem_of_getElem? lookup)]

/-- An Sb-free prepared atom list is a sufficient, simpler hypothesis. -/
theorem NoSelectedSb.of_no_element {i : Input}
    (free : ∀ atom ∈ i.molecule.atoms, atom.element ≠ .Sb) : NoSelectedSb i := by
  intro a
  unfold selectedBy
  cases lookup : i.molecule.atoms[a.val]? with
  | none => simp
  | some atom =>
    have ne := free atom (List.mem_of_getElem? lookup)
    simp [ne]

theorem selector_eq {i : Input} (absent : NoSelectedSb i) (nitrogenAbsent : NoSelectedNitrogen i) :
    oldSelected i = RingPyramidalPublication.phosphorus i := by
  funext a
  have off := absent a
  have noN := nitrogenAbsent a
  unfold oldSelected selectedBy oldElement RingPyramidalPublication.phosphorus at *
  cases lookup : i.molecule.atoms[a.val]? with
  | none => simp
  | some atom =>
    simp only [lookup,Option.any_some] at off noN ⊢
    clear absent nitrogenAbsent
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,Bool.or_eq_true]
    have noSb : ¬ ((atom.element == .Sb) = true ∧ (atom.charge == 0) = true ∧
        (!atom.aromatic) = true ∧
        decide (Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3) = true) := by
      intro h
      simp [h.1,h.2.1,h.2.2.1,h.2.2.2] at off
    have noNitrogen : ¬ ((atom.element == .N) = true ∧
        RingPyramidalNitrogen.constrained i a = true ∧ (atom.charge == 0) = true ∧
        (!atom.aromatic) = true ∧
        decide (Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3) = true) := by
      intro h
      simp [h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2] at noN
    aesop

theorem eligible_eq {i : Input} (absent : NoSelectedSb i) (nitrogenAbsent : NoSelectedNitrogen i) :
    oldEligible i = RingPyramidalPublication.eligible i := by
  funext a
  simp only [oldEligible,RingPyramidalPublication.eligible,selector_eq absent nitrogenAbsent]

theorem focus_eq {i : Input} (absent : NoSelectedSb i) (nitrogenAbsent : NoSelectedNitrogen i) :
    focusBy oldElement i = RingPyramidalPublication.focusP i := by
  funext q
  unfold focusBy RingPyramidalPublication.focusP
  change (if _ then q.val.node.current?.filter (oldSelected i) else none) = _
  rw [selector_eq absent nitrogenAbsent]

/-- Equality holds across every reader, including partial and unready readers. -/
theorem local_eq {i : Input} (absent : NoSelectedSb i) (nitrogenAbsent : NoSelectedNitrogen i) :
    oldPublish i = RingPyramidalPublication.publish i := by
  funext q r
  simp only [oldPublish,publishBy,RingPyramidalPublication.publish,focus_eq absent nitrogenAbsent]
  rfl

/-- The old policy builds its own bonded-path queue. -/
def oldQueue (i : Input) (root : i.certified.Atom) := RingEligibleGraph.queue i (oldEligible i) root

theorem old_inventory (i : Input) (root : i.certified.Atom) :
    RingEligibleGraph.Inventory (oldEligible i) root (oldQueue i root) :=
  RingEligibleGraph.inventory i (oldEligible i) root

theorem queue_eq {i : Input} (absent : NoSelectedSb i) (nitrogenAbsent : NoSelectedNitrogen i) (root : i.certified.Atom) :
    oldQueue i root = RingEligibleGraph.queue i (RingPyramidalPublication.eligible i) root := by
  unfold oldQueue
  rw [eligible_eq absent nitrogenAbsent]

/-- The addressed store agrees after every sphere, not merely at the final root. -/
theorem stored_eq {i : Input} (absent : NoSelectedSb i) (nitrogenAbsent : NoSelectedNitrogen i) (root : i.certified.Atom) (top k : Nat) :
    RingSphereQueue.stored (oldPublish i) root (oldQueue i root) top k =
    RingSphereQueue.stored (RingPyramidalPublication.publish i) root
      (RingEligibleGraph.queue i (RingPyramidalPublication.eligible i) root) top k := by
  rw [local_eq absent nitrogenAbsent,queue_eq absent nitrogenAbsent]

theorem run_eq {i : Input} (absent : NoSelectedSb i) (nitrogenAbsent : NoSelectedNitrogen i) (root : i.certified.Atom) (k : Nat) :
    RingSphereQueue.run (oldPublish i) root (oldQueue i root) k =
    RingSphereQueue.run (RingPyramidalPublication.publish i) root
      (RingEligibleGraph.queue i (RingPyramidalPublication.eligible i) root) k := by
  rw [local_eq absent nitrogenAbsent,queue_eq absent nitrogenAbsent]

def oldRoot (i : Input) (a : i.certified.Atom) :=
  RingEligibleGraph.root i (oldEligible i) (oldPublish i) a

theorem root_eq {i : Input} (absent : NoSelectedSb i) (nitrogenAbsent : NoSelectedNitrogen i) : oldRoot i = RingChemicalGraphProof.root i := by
  unfold oldRoot RingChemicalGraphProof.root
  rw [eligible_eq absent nitrogenAbsent,local_eq absent nitrogenAbsent]

def oldReport (i : Input) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun a => (oldRoot i a).map fun v => (a.val,v)

/-- Every complete prepared report is unchanged outside the newly selected region.
The atom request may contain any order or multiplicity. -/
theorem report_eq {i : Input} (absent : NoSelectedSb i) (nitrogenAbsent : NoSelectedNitrogen i) (atoms : List i.certified.Atom) :
    oldReport i atoms = RingChemicalReport.report? i atoms := by
  unfold oldReport RingChemicalReport.report?
  rw [root_eq absent nitrogenAbsent]
  rfl

assert_kernel_only NoSelectedNitrogen.of_no_element
assert_kernel_only NoSelectedSb.of_no_element
assert_kernel_only selector_eq
assert_kernel_only eligible_eq
assert_kernel_only local_eq
assert_kernel_only old_inventory
assert_kernel_only queue_eq
assert_kernel_only stored_eq
assert_kernel_only run_eq
assert_kernel_only root_eq
assert_kernel_only report_eq
end TetraStereo.Engine.RingPyramidalInventoryConservation
