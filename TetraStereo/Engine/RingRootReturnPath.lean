import TetraStereo.Engine.RingPromotionCut

/-! # A root-deleted chain between two root neighbours reaches an origin-zero duplicate

Let `q` be an outward retained cursor whose official node is `rootFromEdge r x`. If a simple
chain of bonded atoms avoiding `r` runs from `x` to another atom bonded to `r`, then the
retained expansion below `q` follows that chain atom by atom and its last atom has a child that
is the ring duplicate of `r`, whose provenance is `.ringDuplicate 0`.

The only fuel is the carrier depth. `edge_root_return` takes it as `rest.length < remaining`;
`arm_edge_root_return` derives it from the atom count.
-/

set_option autoImplicit false

namespace TetraStereo.Engine.RingRootReturnPath
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingRetainedChemicalTrace (Reaches)
open RingRetainedConstitution (Cursor)

/-! ## Chains -/

/-- `a` is bonded to the head of `rest`, and each atom of `rest` to the next one. -/
def chainLinked (input : CertifiedLocalizedCIPInput) : input.Atom → List input.Atom → Prop
  | _, [] => True
  | a, b :: rest => input.moleculeGraph.Adj a b ∧ chainLinked input b rest

/-- The last atom of `a :: rest`. -/
def chainEnd {α : Type} : α → List α → α
  | a, [] => a
  | _, b :: rest => chainEnd b rest

/-! ## List and node helpers -/

private theorem slot_of_mem {α : Type} {value : α} {values : List α} (present : value ∈ values) :
    ∃ slot, (value, slot) ∈ values.zipIdx := by
  rw [List.mem_iff_getElem] at present
  rcases present with ⟨slot, slotBound, valueAtSlot⟩
  refine ⟨slot, ?_⟩
  have zippedBound : slot < values.zipIdx.length := by
    simpa using slotBound
  have zippedPresent : values.zipIdx[slot] ∈ values.zipIdx :=
    List.getElem_mem zippedBound
  rw [List.getElem_zipIdx] at zippedPresent
  simpa [valueAtSlot] using zippedPresent

/-- A stored parent is one of the stored history atoms. -/
theorem parent_mem {V : Type} [DecidableEq V] (node : OfficialCIPNode V) {z : V}
    (h : node.parent? = some z) : z ∈ node.history := by
  rcases node with ⟨current, history, provenance⟩
  rcases history with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [OfficialCIPNode.parent?] at h
  · simp [OfficialCIPNode.parent?] at h
  · have eqn : b = z := by simpa [OfficialCIPNode.parent?] using h
    simp [eqn]

/-- The parent of a generated child is the newest history atom of its source. -/
theorem parent_extend {V : Type} [DecidableEq V] (node : OfficialCIPNode V) (z : V) (copy : Nat) :
    (node.extend z copy).parent? = node.history.head? := by
  rcases node with ⟨current, history, provenance⟩
  cases history <;> rfl

/-- The zero copy of the oldest history atom is the ring duplicate at distance zero. -/
theorem extend_root_provenance {V : Type} [DecidableEq V] (node : OfficialCIPNode V) (root : V)
    (newer : List V) (history : node.history = newer ++ [root]) :
    (node.extend root 0).provenance = OfficialCIPNodeProvenance.ringDuplicate 0 := by
  have present : root ∈ node.history := by rw [history]; simp
  have reversed : node.history.reverse = root :: newer.reverse := by rw [history]; simp
  have distance : node.duplicateRootDistance root = 0 := by
    unfold OfficialCIPNode.duplicateRootDistance
    rw [reversed, firstIndexOf?_cons_self]
    rfl
  rw [OfficialCIPNode.extend_provenance, OfficialCIPNode.childProvenance_ring_duplicate _ _ present,
    distance]

/-- From an outward cursor on a real node with positive remaining depth, every bonded atom other
than the stored parent is the atom of an actual retained child one address slot deeper. -/
theorem cursorStep {i : Input} {d : Nat} (q : Cursor i.certified d)
    {current neighbor : i.certified.Atom}
    (hcurrent : q.occurrence.1.node.current? = some current)
    (real : q.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (positive : 0 < q.occurrence.1.remaining)
    (outward : ∀ previous, q.previous? = some previous →
      previous.1.address.length ≤ q.occurrence.1.address.length)
    (adjacent : i.certified.moleculeGraph.Adj current neighbor)
    (notParent : q.occurrence.1.node.parent? ≠ some neighbor) :
    ∃ c, c ∈ i.certified.executableLocalizedRerootChildren q ∧
      c.occurrence.1.node = q.occurrence.1.node.extend neighbor 0 ∧
      c.occurrence.1.address.length = q.occurrence.1.address.length + 1 ∧
      c.occurrence.1.remaining = q.occurrence.1.remaining - 1 ∧
      c.previous? = some q.occurrence := by
  have leaf : q.occurrence.1.node.isDuplicateLeaf = false := by
    simp [OfficialCIPNode.isDuplicateLeaf, real]
  have member := i.certified.extend_zero_mem_executableOfficialCIPChildren_of_real q.occurrence.1.node current neighbor real hcurrent adjacent notParent
  obtain ⟨slot, atSlot⟩ := slot_of_mem member
  have notIncoming : ∀ previous, q.previous? = some previous →
      q.occurrence.1.address ++ [slot] ≠ previous.1.address := by
    intro previous eqn same
    have short := outward previous eqn
    have len := congrArg List.length same
    simp only [List.length_append, List.length_cons, List.length_nil] at len
    omega
  obtain ⟨children, c, computed, present, shape⟩ :=
    i.certified.exists_mem_localizedRerootChildren_of_executable_child q leaf positive _ slot
      atSlot notIncoming
  have actual : children = i.certified.executableLocalizedRerootChildren q :=
    Option.some.inj (computed.symm.trans (i.certified.localizedRerootChildren?_eq_some_executable q))
  subst actual
  have nodeEq := congrArg
    (fun frame : i.certified.LocalizedCIPOccurrenceFrame => frame.node) shape
  have lengthEq := congrArg
    (fun frame : i.certified.LocalizedCIPOccurrenceFrame => frame.address.length) shape
  have remainingEq := congrArg
    (fun frame : i.certified.LocalizedCIPOccurrenceFrame => frame.remaining) shape
  refine ⟨c, present, nodeEq, ?_, remainingEq,
    i.certified.executableLocalizedRerootChildren_previous q c present⟩
  simpa using lengthEq

/-! ## Walking the chain -/

/-- **Path to cursor.** Start at an outward cursor on a real node whose oldest history atom is
`root`. Follow a chain of fresh, pairwise distinct, successively bonded atoms `rest`. If the last
chain atom is bonded to `root`, and `root` is not that atom's stored parent, the retained
expansion reaches the origin-zero ring duplicate. The depth hypothesis is one retained level per
chain atom plus one for the duplicate. -/
theorem outward_root_return {i : Input} {d : Nat} (root : i.certified.Atom) :
    ∀ (rest : List i.certified.Atom) (current : i.certified.Atom) (q : Cursor i.certified d),
      q.occurrence.1.node.current? = some current →
      q.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
      (∃ newer, q.occurrence.1.node.history = newer ++ [root]) →
      q.occurrence.1.node.history.head? ≠ some root →
      (rest = [] → q.occurrence.1.node.parent? ≠ some root) →
      (∀ previous, q.previous? = some previous →
        previous.1.address.length ≤ q.occurrence.1.address.length) →
      rest.length < q.occurrence.1.remaining →
      chainLinked i.certified current rest →
      rest.Nodup →
      (∀ z ∈ rest, z ∉ q.occurrence.1.node.history) →
      i.certified.moleculeGraph.Adj (chainEnd current rest) root →
      ∃ v, Reaches i q v ∧
        v.occurrence.1.node.provenance = OfficialCIPNodeProvenance.ringDuplicate 0
  | [], current, q, hcurrent, real, ex, _, parent, outward, fuel, _, _, _, close => by
      obtain ⟨newer, history⟩ := ex
      have close' : i.certified.moleculeGraph.Adj current root := close
      have positive : 0 < q.occurrence.1.remaining := Nat.lt_of_le_of_lt (Nat.zero_le _) fuel
      obtain ⟨c, present, node, _, _, _⟩ :=
        cursorStep q hcurrent real positive outward close' (parent rfl)
      exact ⟨c, .descend present .here,
        (congrArg OfficialCIPNode.provenance node).trans
          (extend_root_provenance q.occurrence.1.node root newer history)⟩
  | z :: rest, current, q, hcurrent, real, ex, head, _, outward, fuel, linked, nodup, fresh,
      close => by
      obtain ⟨newer, history⟩ := ex
      have linked' : i.certified.moleculeGraph.Adj current z ∧ chainLinked i.certified z rest :=
        linked
      have close' : i.certified.moleculeGraph.Adj (chainEnd z rest) root := close
      have fuel' : rest.length + 1 < q.occurrence.1.remaining := by simpa using fuel
      have distinct : z ∉ rest ∧ rest.Nodup := List.nodup_cons.mp nodup
      have zFresh : z ∉ q.occurrence.1.node.history := fresh z (by simp)
      have notParent : q.occurrence.1.node.parent? ≠ some z :=
        fun same => zFresh (parent_mem _ same)
      obtain ⟨c, present, node, len, remaining, previous⟩ :=
        cursorStep q hcurrent real (by omega) outward linked'.1 notParent
      have childCurrent : c.occurrence.1.node.current? = some z :=
        (congrArg OfficialCIPNode.current? node).trans (OfficialCIPNode.extend_current? _ _ _)
      have childReal : c.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
        (congrArg OfficialCIPNode.provenance node).trans
          ((OfficialCIPNode.extend_provenance _ _ _).trans
            (OfficialCIPNode.childProvenance_real _ _ zFresh))
      have childHistory : c.occurrence.1.node.history = z :: q.occurrence.1.node.history :=
        (congrArg OfficialCIPNode.history node).trans (OfficialCIPNode.extend_history _ _ _)
      have childEx : ∃ newer', c.occurrence.1.node.history = newer' ++ [root] :=
        ⟨z :: newer, by rw [childHistory, history, List.cons_append]⟩
      have childHead : c.occurrence.1.node.history.head? ≠ some root := by
        intro same
        have eqn : z = root :=
          Option.some.inj ((congrArg List.head? childHistory).symm.trans same)
        exact zFresh (by rw [eqn, history]; simp)
      have childParent : rest = [] → c.occurrence.1.node.parent? ≠ some root :=
        fun _ same => head
          (((congrArg OfficialCIPNode.parent? node).trans (parent_extend _ _ _)).symm.trans same)
      have childOutward : ∀ before, c.previous? = some before →
          before.1.address.length ≤ c.occurrence.1.address.length := by
        intro before eqn
        cases Option.some.inj (previous.symm.trans eqn)
        omega
      have childFuel : rest.length < c.occurrence.1.remaining := by omega
      have childFresh : ∀ w ∈ rest, w ∉ c.occurrence.1.node.history := by
        intro w hw inside
        rw [childHistory] at inside
        rcases List.mem_cons.mp inside with same | old
        · exact distinct.1 (by rw [← same]; exact hw)
        · exact fresh w (List.mem_cons_of_mem _ hw) old
      obtain ⟨v, reach, tag⟩ := outward_root_return root rest z c childCurrent childReal childEx
        childHead childParent childOutward childFuel linked'.2 distinct.2 childFresh close'
      exact ⟨v, .descend present reach, tag⟩

/-- **Path realization at a first-sphere node, explicit depth.** `q` carries `rootFromEdge r x`
and was not entered from deeper in the tree. `x :: rest` is a bonded chain, simple and avoiding
`r`, ending at a second atom bonded to `r`. -/
theorem edge_root_return {i : Input} {d : Nat} (q : Cursor i.certified d)
    {r x : i.certified.Atom}
    (node : q.occurrence.val.node = OfficialCIPNode.rootFromEdge r x)
    (outward : ∀ previous, q.previous? = some previous →
      previous.val.address.length ≤ q.occurrence.val.address.length)
    (rest : List i.certified.Atom) (nonempty : rest ≠ [])
    (linked : chainLinked i.certified x rest)
    (simple : (r :: x :: rest).Nodup)
    (fuel : rest.length < q.occurrence.val.remaining)
    (close : i.certified.moleculeGraph.Adj (chainEnd x rest) r) :
    ∃ v, Reaches i q v ∧
      v.occurrence.val.node.provenance = OfficialCIPNodeProvenance.ringDuplicate 0 := by
  have rootOutside : r ∉ x :: rest := (List.nodup_cons.mp simple).1
  have tail : x ∉ rest ∧ rest.Nodup := List.nodup_cons.mp (List.nodup_cons.mp simple).2
  have ne : x ≠ r := fun same => rootOutside (by simp [same])
  have hx : q.occurrence.val.node.current? = some x := congrArg OfficialCIPNode.current? node
  have real : q.occurrence.val.node.provenance = OfficialCIPNodeProvenance.realAtom :=
    congrArg OfficialCIPNode.provenance node
  have history : q.occurrence.val.node.history = [x, r] := congrArg OfficialCIPNode.history node
  have fresh : ∀ z ∈ rest, z ∉ q.occurrence.val.node.history := by
    intro z hz inside
    rw [history] at inside
    rcases List.mem_cons.mp inside with same | old
    · exact tail.1 (by rw [← same]; exact hz)
    · have same : z = r := List.mem_singleton.mp old
      exact rootOutside (List.mem_cons_of_mem _ (by rw [← same]; exact hz))
  exact outward_root_return r rest x q hx real ⟨[x], history⟩
    (fun same => ne (Option.some.inj ((congrArg List.head? history).symm.trans same)))
    (fun empty => absurd empty nonempty) outward fuel linked tail.2 fresh close

/-- **Path realization at a first-sphere arm, depth from cardinality.** At the molecular carrier
depth `atomCount + 1` an address of length one leaves `atomCount + 1` levels, while a simple
chain avoiding `r` has at most `atomCount - 1` atoms. -/
theorem arm_edge_root_return {i : Input} (q : RingActivePairs.Arm i) {r x : i.certified.Atom}
    (node : q.occurrence.val.node = OfficialCIPNode.rootFromEdge r x)
    (one : q.occurrence.val.address.length = 1)
    (outward : ∀ previous, q.previous? = some previous →
      previous.val.address.length ≤ q.occurrence.val.address.length)
    (rest : List i.certified.Atom) (nonempty : rest ≠ [])
    (linked : chainLinked i.certified x rest)
    (simple : (r :: x :: rest).Nodup)
    (close : i.certified.moleculeGraph.Adj (chainEnd x rest) r) :
    ∃ v, Reaches i q v ∧
      v.occurrence.val.node.provenance = OfficialCIPNodeProvenance.ringDuplicate 0 := by
  have fuel : rest.length < q.occurrence.val.remaining := by
    have grade := i.certified.localizedCIPOccurrence_depthGrade q.occurrence
    have card := simple.length_le_card
    simp only [Fintype.card_fin, List.length_cons] at card
    omega
  exact edge_root_return q node outward rest nonempty linked simple fuel close

/-! ## Reading the chain end -/

/-- The chain end is the last element of the chain as a list. -/
theorem chainEnd_eq_getLast {α : Type} : ∀ (a : α) (rest : List α),
    chainEnd a rest = (a :: rest).getLast (List.cons_ne_nil a rest)
  | _, [] => rfl
  | _, b :: rest => chainEnd_eq_getLast b rest

end TetraStereo.Engine.RingRootReturnPath

assert_kernel_only TetraStereo.Engine.RingRootReturnPath.arm_edge_root_return
