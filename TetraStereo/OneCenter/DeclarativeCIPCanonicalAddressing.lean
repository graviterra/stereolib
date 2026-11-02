import TetraStereo.OneCenter.DeclarativeCIPConstitutional
import TetraStereo.Certificate.CanonicalSphereKey
import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

open Certificate.CanonicalSphereKey (Key assemble sortDesc keyObservation slotOf WellShaped pad)

noncomputable section

open scoped Classical

universe u


























variable {Atom : Type u}

namespace RootedDigraph

local instance (graph : RootedDigraph Atom) : Fintype graph.Node := graph.nodeFintype

/-! ## Addresses, depth, and occupancy -/

theorem Addressing.address_length_eq_depth {graph : RootedDigraph Atom}
    (addressing : graph.Addressing) (node : graph.Node) :
    (addressing.address node).length = graph.depth node := by
  have hreachable := graph.reachable node
  induction hreachable with
  | refl => simp [addressing.root_address, graph.root_depth]
  | @tail parent node _ hedge ih =>
      rcases (addressing.child_iff parent node).1 hedge with ⟨slot, hslot⟩
      rw [hslot, graph.child_depth hedge]
      simp [ih]

/-- Every prefix of an occupied address is occupied. -/
theorem Addressing.prefix_occupied {graph : RootedDigraph Atom}
    (addressing : graph.Addressing) (node : graph.Node) :
    ∀ pre post, addressing.address node = pre ++ post →
      ∃ ancestor, addressing.address ancestor = pre := by
  have hreachable := graph.reachable node
  induction hreachable with
  | refl =>
      intro pre post h
      rw [addressing.root_address] at h
      have hpre : pre = [] := (List.append_eq_nil_iff.1 h.symm).1
      exact ⟨graph.root, by rw [addressing.root_address, hpre]⟩
  | @tail parent node _ hedge ih =>
      intro pre post h
      rcases (addressing.child_iff parent node).1 hedge with ⟨slot, hslot⟩
      rcases List.eq_nil_or_concat post with hpost | ⟨post', last, hpost⟩
      · exact ⟨node, by rw [h, hpost, List.append_nil]⟩
      · rw [hslot, hpost, List.concat_eq_append, ← List.append_assoc] at h
        exact ih pre post' (List.append_inj_left' h rfl)

/-- The depth bound of a finite rooted digraph. -/
def height (graph : RootedDigraph Atom) : ℕ :=
  Finset.univ.sup graph.depth

theorem depth_le_height (graph : RootedDigraph Atom) (node : graph.Node) :
    graph.depth node ≤ graph.height :=
  Finset.le_sup (f := graph.depth) (Finset.mem_univ node)

/-- The width bound of a finite rooted digraph: no node has more children than nodes exist. -/
def width (graph : RootedDigraph Atom) : ℕ :=
  Fintype.card graph.Node

/-- Children of a node, in an arbitrary list order. -/
def childList (graph : RootedDigraph Atom) (node : graph.Node) : List graph.Node :=
  (Finset.univ.filter (graph.child node)).toList

theorem mem_childList (graph : RootedDigraph Atom) {node child : graph.Node} :
    child ∈ graph.childList node ↔ graph.child node child := by
  simp [childList]

theorem childList_nodup (graph : RootedDigraph Atom) (node : graph.Node) :
    (graph.childList node).Nodup :=
  Finset.nodup_toList _

end RootedDigraph

open RootedDigraph

/-! ## Rule values -/

/-- The natural-number observation compared by one constitutional rule at a position. -/
def ruleValue [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom) :
    ConstitutionalRule → List ℕ → Option (NodeLabel Atom) → ℕ
  | .rule1aAtomicNumber, _, label => nodeAtomicNumber molecule label
  | .rule1bDuplicateNodeProximity, position, label => nodeRule1bRootDistance position label
  | .rule2AtomicMass, _, label => nodeAtomicMass molecule label

/-- The relational outcome of one constitutional rule on two observed values. -/
def RuleValueOutcome : ConstitutionalRule → ℕ → ℕ → Ordering → Prop
  | .rule1aAtomicNumber => DescendingNatOutcome
  | .rule1bDuplicateNodeProximity => Rule1bDistanceOutcome
  | .rule2AtomicMass => DescendingNatOutcome

theorem constitutionalNodeOutcome_iff_ruleValue [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (rule : ConstitutionalRule) (position : List ℕ)
    (left right : Option (NodeLabel Atom)) (outcome : Ordering) :
    ConstitutionalNodeOutcome molecule rule position left right outcome ↔
      RuleValueOutcome rule (ruleValue molecule rule position left)
        (ruleValue molecule rule position right) outcome := by
  cases rule <;> rfl

theorem ruleValue_eq_of_length_eq [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (rule : ConstitutionalRule) {first second : List ℕ}
    (h : first.length = second.length) (label : Option (NodeLabel Atom)) :
    ruleValue molecule rule first label = ruleValue molecule rule second label := by
  cases rule
  · rfl
  · exact nodeRule1bRootDistance_eq_of_length_eq h label
  · rfl

/-- Priority orientation: larger values rank higher.  Rule 1b prefers the smaller distance. -/
def priorityValue : ConstitutionalRule → ℕ → ℤ
  | .rule1aAtomicNumber, value => value
  | .rule1bDuplicateNodeProximity, value => -(value : ℤ)
  | .rule2AtomicMass, value => value

theorem priorityValue_injective (rule : ConstitutionalRule) :
    Function.Injective (priorityValue rule) := by
  intro first second h
  cases rule <;> simp [priorityValue] at h <;> exact h

/-- Position of a rule's component in the rule-major vector key. -/
def ruleIndex : ConstitutionalRule → ℕ
  | .rule1aAtomicNumber => 0
  | .rule1bDuplicateNodeProximity => 1
  | .rule2AtomicMass => 2

section Keys

variable [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  (graph : RootedDigraph Atom)

local instance : Fintype graph.Node := graph.nodeFintype

/-- Priority-oriented observation of `rule` at a represented node of the given depth. -/
def nodeObservation (rule : ConstitutionalRule) (node : graph.Node) : ℤ :=
  priorityValue rule
    (ruleValue molecule rule (List.replicate (graph.depth node) 0) (some (graph.label node)))

/-- One rule's component, laid out over a ranked list of child vector keys. -/
def ruleComponent (W D : ℕ) (rule : ConstitutionalRule) (node : graph.Node)
    (ranked : List (List (Key ℤ))) : Key ℤ :=
  assemble W D (nodeObservation molecule graph rule node)
    (ranked.map fun key => key.getD (ruleIndex rule) [])

/-- Rule-major vector key of a node.  Children are ranked by their own vector keys in
descending lexicographic order, so Rule 1a dominates Rule 1b, which dominates Rule 2. -/
def ruleKey (W D : ℕ) (node : graph.Node) : List (Key ℤ) :=
  let ranked := sortDesc ((graph.childList node).attach.map fun child => ruleKey W D child.1)
  [ruleComponent molecule graph W D .rule1aAtomicNumber node ranked,
    ruleComponent molecule graph W D .rule1bDuplicateNodeProximity node ranked,
    ruleComponent molecule graph W D .rule2AtomicMass node ranked]
termination_by graph.height + 1 - graph.depth node
decreasing_by
  have hchild := (graph.mem_childList).1 child.2
  have hdepth := graph.child_depth hchild
  have hle := graph.depth_le_height child.1
  omega

theorem ruleKey_eq (W D : ℕ) (node : graph.Node) :
    ruleKey molecule graph W D node =
      let ranked := sortDesc ((graph.childList node).map (ruleKey molecule graph W D))
      [ruleComponent molecule graph W D .rule1aAtomicNumber node ranked,
        ruleComponent molecule graph W D .rule1bDuplicateNodeProximity node ranked,
        ruleComponent molecule graph W D .rule2AtomicMass node ranked] := by
  rw [ruleKey]
  simp only [List.attach_map_val]

theorem ruleKey_getD (W D : ℕ) (rule : ConstitutionalRule) (node : graph.Node) :
    (ruleKey molecule graph W D node).getD (ruleIndex rule) [] =
      ruleComponent molecule graph W D rule node
        (sortDesc ((graph.childList node).map (ruleKey molecule graph W D))) := by
  rw [ruleKey_eq]
  cases rule <;> rfl

omit [Fintype Atom] [DecidableEq Atom] in
/-- Well-founded induction from the leaves toward the root. -/
theorem node_induction {motive : graph.Node → Prop}
    (step : ∀ node, (∀ child, graph.child node child → motive child) → motive node) :
    ∀ node, motive node := by
  intro node
  induction hmeasure : graph.height + 1 - graph.depth node using Nat.strong_induction_on
    generalizing node with
  | _ measure ih =>
      apply step
      intro child hchild
      have hdepth := graph.child_depth hchild
      have hle := graph.depth_le_height child
      exact ih (graph.height + 1 - graph.depth child) (by omega) child rfl

theorem ruleKey_wellShaped (W D : ℕ) (rule : ConstitutionalRule) :
    ∀ node, WellShaped W D ((ruleKey molecule graph W D node).getD (ruleIndex rule) []) := by
  intro node
  revert rule
  refine node_induction graph (motive := fun node => ∀ rule,
    WellShaped W D ((ruleKey molecule graph W D node).getD (ruleIndex rule) [])) ?_ node
  intro node ih rule
  rw [ruleKey_getD]
  apply Certificate.CanonicalSphereKey.assemble_wellShaped
  intro key hkey
  obtain ⟨vector, hvector, rfl⟩ := List.mem_map.1 hkey
  obtain ⟨child, hchild, rfl⟩ :=
    List.mem_map.1 (Certificate.CanonicalSphereKey.sortDesc_mem hvector)
  exact ih child ((graph.mem_childList).1 hchild) rule

end Keys

/-! ## The canonical addressing family -/

section Family

variable [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  {graph : RootedDigraph Atom}

local instance : Fintype graph.Node := graph.nodeFintype

/-- Slot `slot` below `parent` is occupied exactly for `slot < count`. -/
def DenseAt (addressing : graph.Addressing) (parent : graph.Node) (count : ℕ) : Prop :=
  ∀ slot,
    (∃ child, addressing.address child = addressing.address parent ++ [slot]) ↔ slot < count

/-- Sibling slots form an initial segment of the natural numbers at every node. -/
def Dense (addressing : graph.Addressing) : Prop :=
  ∀ parent, ∃ count, DenseAt addressing parent count

/-- Siblings in increasing slot order have weakly decreasing keys. -/
def KeySorted {K : Type*} [LinearOrder K] (key : graph.Node → K)
    (addressing : graph.Addressing) : Prop :=
  ∀ parent first second firstSlot secondSlot,
    addressing.address first = addressing.address parent ++ [firstSlot] →
      addressing.address second = addressing.address parent ++ [secondSlot] →
        firstSlot < secondSlot → key second ≤ key first

/-- The admissible canonical addressings of a rooted digraph. -/
def CanonicalAddressing (addressing : graph.Addressing) : Prop :=
  Dense addressing ∧ KeySorted (ruleKey molecule graph graph.width graph.height) addressing

/-- The node at a sibling slot, if any. -/
def childAt (addressing : graph.Addressing) (parent : graph.Node) (slot : ℕ) :
    Option graph.Node :=
  if h : ∃ child, addressing.address child = addressing.address parent ++ [slot] then
    some (Classical.choose h)
  else none

omit [Fintype Atom] [DecidableEq Atom] in
theorem childAt_eq_some_iff (addressing : graph.Addressing) (parent : graph.Node) (slot : ℕ)
    (child : graph.Node) :
    childAt addressing parent slot = some child ↔
      addressing.address child = addressing.address parent ++ [slot] := by
  unfold childAt
  split
  · rename_i h
    constructor
    · intro heq
      cases heq
      exact Classical.choose_spec h
    · intro haddr
      congr 1
      exact addressing.address_injective ((Classical.choose_spec h).trans haddr.symm)
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    exact fun haddr => h ⟨child, haddr⟩

/-- Children in slot order. -/
def slotList (addressing : graph.Addressing) (parent : graph.Node) (count : ℕ) :
    List graph.Node :=
  (List.range count).map fun slot => (childAt addressing parent slot).getD parent

omit [Fintype Atom] [DecidableEq Atom] in
theorem slotList_getD_of_lt {addressing : graph.Addressing} {parent : graph.Node} {count : ℕ}
    (hdense : DenseAt addressing parent count) {slot : ℕ} (hslot : slot < count) :
    ∃ child, (slotList addressing parent count)[slot]? = some child ∧
      addressing.address child = addressing.address parent ++ [slot] := by
  obtain ⟨child, hchild⟩ := (hdense slot).2 hslot
  refine ⟨child, ?_, hchild⟩
  have hat := (childAt_eq_some_iff addressing parent slot child).2 hchild
  simp [slotList, List.getElem?_range hslot, hat]

omit [Fintype Atom] [DecidableEq Atom] in
theorem slotList_perm {addressing : graph.Addressing} {parent : graph.Node} {count : ℕ}
    (hdense : DenseAt addressing parent count) :
    (slotList addressing parent count).Perm (graph.childList parent) := by
  apply (List.perm_ext_iff_of_nodup ?_ (graph.childList_nodup parent)).2
  · intro child
    rw [graph.mem_childList, addressing.child_iff]
    simp only [slotList, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨slot, hslot, rfl⟩
      obtain ⟨found, hfound⟩ := (hdense slot).2 hslot
      have hat := (childAt_eq_some_iff addressing parent slot found).2 hfound
      exact ⟨slot, by rw [hat]; exact hfound⟩
    · rintro ⟨slot, hslot⟩
      have hlt := (hdense slot).1 ⟨child, hslot⟩
      have hat := (childAt_eq_some_iff addressing parent slot child).2 hslot
      exact ⟨slot, hlt, by rw [hat]; rfl⟩
  · apply List.Nodup.map_on _ List.nodup_range
    intro first hfirst second hsecond heq
    simp only [List.mem_range] at hfirst hsecond
    obtain ⟨c₁, hc₁⟩ := (hdense first).2 hfirst
    obtain ⟨c₂, hc₂⟩ := (hdense second).2 hsecond
    have h₁ := (childAt_eq_some_iff addressing parent first c₁).2 hc₁
    have h₂ := (childAt_eq_some_iff addressing parent second c₂).2 hc₂
    rw [h₁, h₂] at heq
    simp only [Option.getD_some] at heq
    subst heq
    have := hc₁.symm.trans hc₂
    simpa using this

omit [Fintype Atom] [DecidableEq Atom] in
/-- Under a key-sorted dense addressing, the canonical ranking of children is the slot order. -/
theorem sortDesc_childKeys_eq_slotOrder {K : Type*} [LinearOrder K] (key : graph.Node → K)
    {addressing : graph.Addressing} {parent : graph.Node} {count : ℕ}
    (hdense : DenseAt addressing parent count) (hsorted : KeySorted key addressing) :
    sortDesc ((graph.childList parent).map key) =
      (slotList addressing parent count).map key := by
  rw [Certificate.CanonicalSphereKey.sortDesc_eq_of_perm ((slotList_perm hdense).symm.map key)]
  apply Certificate.CanonicalSphereKey.sortDesc_of_pairwise
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.length_map, slotList, List.length_range] at hi hj
  obtain ⟨ci, hci, hai⟩ := slotList_getD_of_lt hdense hi
  obtain ⟨cj, hcj, haj⟩ := slotList_getD_of_lt hdense hj
  obtain ⟨_, hgi⟩ := List.getElem?_eq_some_iff.1 hci
  obtain ⟨_, hgj⟩ := List.getElem?_eq_some_iff.1 hcj
  simp only [List.getElem_map]
  rw [hgi, hgj]
  exact hsorted parent ci cj i j hai haj hij

/-! ## Observations at addresses -/

/-- The priority-oriented observation of `rule` at an address; `⊥` if unoccupied. -/
def addressObservation (addressing : graph.Addressing) (rule : ConstitutionalRule)
    (position : List ℕ) : WithBot ℤ :=
  if h : ∃ node, addressing.address node = position then
    (nodeObservation molecule graph rule (Classical.choose h) : WithBot ℤ)
  else ⊥

theorem addressObservation_of_address (addressing : graph.Addressing) (rule : ConstitutionalRule)
    (node : graph.Node) :
    addressObservation molecule addressing rule (addressing.address node) =
      (nodeObservation molecule graph rule node : WithBot ℤ) := by
  have h : ∃ found, addressing.address found = addressing.address node := ⟨node, rfl⟩
  unfold addressObservation
  rw [dif_pos h]
  congr 2
  exact addressing.address_injective (Classical.choose_spec h)

theorem addressObservation_of_unoccupied (addressing : graph.Addressing)
    (rule : ConstitutionalRule) {position : List ℕ}
    (h : ∀ node, addressing.address node ≠ position) :
    addressObservation molecule addressing rule position = ⊥ := by
  unfold addressObservation
  rw [dif_neg (by simpa using h)]

/-- **Canonical observation theorem.**  Under a canonical addressing, the observation at address
`addressing.address node ++ path` is the canonical key observation of `node` at sphere
`path.length`, dense slot `slotOf W path`.  The right side is independent of the addressing. -/
theorem addressObservation_eq_keyObservation (W D : ℕ) {addressing : graph.Addressing}
    (hdense : Dense addressing) (hsorted : KeySorted (ruleKey molecule graph W D) addressing)
    (rule : ConstitutionalRule) :
    ∀ (path : List ℕ) (node : graph.Node),
      (∀ slot ∈ path, slot < W) → path.length ≤ D →
      keyObservation ((ruleKey molecule graph W D node).getD (ruleIndex rule) [])
          path.length (slotOf W path) =
        addressObservation molecule addressing rule (addressing.address node ++ path)
  | [], node, _, _ => by
      rw [List.append_nil, addressObservation_of_address, ruleKey_getD]
      simp [keyObservation, ruleComponent, assemble, slotOf]
  | slot :: path, node, hdigits, hlength => by
      have hs : slot < W := hdigits slot (by simp)
      have hpath : ∀ i ∈ path, i < W := fun i hi => hdigits i (by simp [hi])
      have hpl : path.length < D := by simp at hlength; omega
      have hbound := Certificate.CanonicalSphereKey.slotOf_lt hpath
      obtain ⟨count, hcount⟩ := hdense node
      have hranked := sortDesc_childKeys_eq_slotOrder (ruleKey molecule graph W D) hcount hsorted
      have hkeys : ∀ key ∈
          ((slotList addressing node count).map (ruleKey molecule graph W D)).map
            (fun key => key.getD (ruleIndex rule) []), WellShaped W D key := by
        intro key hkey
        obtain ⟨vector, hvector, rfl⟩ := List.mem_map.1 hkey
        obtain ⟨child, _, rfl⟩ := List.mem_map.1 hvector
        exact ruleKey_wellShaped molecule graph W D rule child
      rw [ruleKey_getD, hranked]
      simp only [keyObservation, ruleComponent, assemble, List.length_cons, slotOf,
        List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map,
        List.getElem?_range hpl, Option.map_some, Option.getD_some,
        Certificate.CanonicalSphereKey.getD_flatMap_range _ _ W
          (fun i _ => Certificate.CanonicalSphereKey.slotLevel_length hkeys hpl i) hs hbound]
      by_cases hocc : slot < count
      · obtain ⟨child, hchild, haddr⟩ := slotList_getD_of_lt hcount hocc
        have ih := addressObservation_eq_keyObservation W D hdense hsorted rule path child hpath
          (by omega)
        have hpos : addressing.address node ++ slot :: path = addressing.address child ++ path := by
          rw [haddr]; simp
        rw [hpos, ← ih]
        have hk : path.length <
            ((ruleKey molecule graph W D child).getD (ruleIndex rule) []).length := by
          rw [(ruleKey_wellShaped molecule graph W D rule child).1]
          omega
        have hk' : path.length <
            ((ruleKey molecule graph W D child)[ruleIndex rule]?.getD []).length := by
          simpa [List.getD_eq_getElem?_getD] using hk
        simp [keyObservation, List.getD_eq_getElem?_getD, List.getElem?_map, hchild,
          List.getElem?_eq_getElem hk']
      · have hnone : ((slotList addressing node count).map (ruleKey molecule graph W D))[slot]? =
            none := by
          simp [slotList]
          omega
        have hunocc :
            ∀ found, addressing.address found ≠ addressing.address node ++ slot :: path := by
          intro found hfound
          obtain ⟨ancestor, hancestor⟩ := addressing.prefix_occupied found
            (addressing.address node ++ [slot]) path (by rw [hfound]; simp)
          exact hocc ((hcount slot).1 ⟨ancestor, hancestor⟩)
        rw [addressObservation_of_unoccupied molecule addressing rule hunocc]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hnone, Option.map_none,
          Option.getD_none, List.getElem?_nil, pad, List.getElem?_replicate]
        split <;> rfl

/-! ## Occupied addresses lie inside the canonical key -/

omit [Fintype Atom] [DecidableEq Atom] in
theorem count_le_width {addressing : graph.Addressing} {parent : graph.Node} {count : ℕ}
    (hdense : DenseAt addressing parent count) : count ≤ graph.width := by
  let pick : Fin count → graph.Node := fun slot => Classical.choose ((hdense slot).2 slot.2)
  have hinj : Function.Injective pick := by
    intro first second h
    have h₁ := Classical.choose_spec ((hdense first).2 first.2)
    have h₂ := Classical.choose_spec ((hdense second).2 second.2)
    have heq : addressing.address parent ++ [(first : ℕ)] =
        addressing.address parent ++ [(second : ℕ)] := by
      rw [← h₁, ← h₂]
      exact congrArg addressing.address h
    exact Fin.ext (by simpa using heq)
  simpa [RootedDigraph.width] using Fintype.card_le_of_injective pick hinj

omit [Fintype Atom] [DecidableEq Atom] in
theorem address_slots_lt_width {addressing : graph.Addressing} (hdense : Dense addressing)
    (node : graph.Node) : ∀ slot ∈ addressing.address node, slot < graph.width := by
  have hreachable := graph.reachable node
  induction hreachable with
  | refl => simp [addressing.root_address]
  | @tail parent node _ hedge ih =>
      rcases (addressing.child_iff parent node).1 hedge with ⟨last, hlast⟩
      obtain ⟨count, hcount⟩ := hdense parent
      have hlt : last < count := (hcount last).1 ⟨node, hlast⟩
      have hle := count_le_width hcount
      intro slot hslot
      rw [hlast, List.mem_append, List.mem_singleton] at hslot
      rcases hslot with hslot | rfl
      · exact ih slot hslot
      · omega

omit [Fintype Atom] [DecidableEq Atom] in
theorem address_length_le_height (addressing : graph.Addressing) (node : graph.Node) :
    (addressing.address node).length ≤ graph.height := by
  rw [addressing.address_length_eq_depth]
  exact graph.depth_le_height node

/-- **Addressing independence of observations.**  Two canonical addressings of one rooted digraph
observe the same value of every constitutional rule at every address. -/
theorem addressObservation_canonical_eq {first second : graph.Addressing}
    (hfirst : CanonicalAddressing molecule first) (hsecond : CanonicalAddressing molecule second)
    (rule : ConstitutionalRule) (position : List ℕ) :
    addressObservation molecule first rule position =
      addressObservation molecule second rule position := by
  by_cases hin : (∀ slot ∈ position, slot < graph.width) ∧ position.length ≤ graph.height
  · have h₁ := addressObservation_eq_keyObservation molecule graph.width graph.height
      hfirst.1 hfirst.2 rule position graph.root hin.1 hin.2
    have h₂ := addressObservation_eq_keyObservation molecule graph.width graph.height
      hsecond.1 hsecond.2 rule position graph.root hin.1 hin.2
    rw [first.root_address, List.nil_append] at h₁
    rw [second.root_address, List.nil_append] at h₂
    rw [← h₁, ← h₂]
  · have hout : ∀ addressing : graph.Addressing, Dense addressing →
        ∀ node, addressing.address node ≠ position := by
      intro addressing hdense node hnode
      exact hin ⟨hnode ▸ address_slots_lt_width hdense node,
        hnode ▸ address_length_le_height addressing node⟩
    rw [addressObservation_of_unoccupied molecule first rule (hout first hfirst.1),
      addressObservation_of_unoccupied molecule second rule (hout second hsecond.1)]

/-! ## Constitutional outcomes read only address observations -/

/-- The label at an address, if occupied. -/
def addressLabel (addressing : graph.Addressing) (position : List ℕ) :
    Option (NodeLabel Atom) :=
  if h : ∃ node, addressing.address node = position then
    some (graph.label (Classical.choose h))
  else none

omit [Fintype Atom] [DecidableEq Atom] in
theorem labelAt_iff_eq_addressLabel (addressing : graph.Addressing) (position : List ℕ)
    (label : Option (NodeLabel Atom)) :
    RootedDigraph.Addressing.LabelAt graph addressing position label ↔
      label = addressLabel addressing position := by
  constructor
  · rintro (⟨node, hnode, rfl⟩ | ⟨rfl, hempty⟩)
    · have h : ∃ found, addressing.address found = position := ⟨node, hnode⟩
      unfold addressLabel
      rw [dif_pos h]
      congr 2
      exact addressing.address_injective (hnode.trans (Classical.choose_spec h).symm)
    · unfold addressLabel
      rw [dif_neg (by simpa using hempty)]
  · rintro rfl
    unfold addressLabel
    split
    · rename_i h
      exact Or.inl ⟨Classical.choose h, Classical.choose_spec h, rfl⟩
    · rename_i h
      exact Or.inr ⟨rfl, by simpa using h⟩

theorem constitutionalOutcomeAt_iff {left right : RootedDigraph Atom}
    (leftAddressing : left.Addressing) (rightAddressing : right.Addressing)
    (rule : ConstitutionalRule) (position : List ℕ) (outcome : Ordering) :
    ConstitutionalOutcomeAt molecule rule left leftAddressing right rightAddressing position
        outcome ↔
      RuleValueOutcome rule
        (ruleValue molecule rule position (addressLabel leftAddressing position))
        (ruleValue molecule rule position (addressLabel rightAddressing position)) outcome := by
  unfold ConstitutionalOutcomeAt
  simp only [labelAt_iff_eq_addressLabel, constitutionalNodeOutcome_iff_ruleValue]
  constructor
  · rintro ⟨_, _, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, _, rfl, rfl, h⟩

theorem ruleValue_eq_of_addressObservation_eq {first second : graph.Addressing}
    (rule : ConstitutionalRule) (position : List ℕ)
    (h : addressObservation molecule first rule position =
      addressObservation molecule second rule position) :
    ruleValue molecule rule position (addressLabel first position) =
      ruleValue molecule rule position (addressLabel second position) := by
  unfold addressObservation at h
  unfold addressLabel
  by_cases h₁ : ∃ node, first.address node = position <;>
    by_cases h₂ : ∃ node, second.address node = position
  · rw [dif_pos h₁, dif_pos h₂] at h ⊢
    have hobs := priorityValue_injective rule (WithBot.coe_injective h)
    have hlen₁ : (List.replicate (graph.depth (Classical.choose h₁)) 0).length =
        position.length := by
      rw [List.length_replicate, ← first.address_length_eq_depth, Classical.choose_spec h₁]
    have hlen₂ : (List.replicate (graph.depth (Classical.choose h₂)) 0).length =
        position.length := by
      rw [List.length_replicate, ← second.address_length_eq_depth, Classical.choose_spec h₂]
    rw [← ruleValue_eq_of_length_eq molecule rule hlen₁,
      ← ruleValue_eq_of_length_eq molecule rule hlen₂]
    exact hobs
  · rw [dif_pos h₁, dif_neg h₂] at h
    exact (WithBot.coe_ne_bot h).elim
  · rw [dif_neg h₁, dif_pos h₂] at h
    exact (WithBot.coe_ne_bot h.symm).elim
  · rw [dif_neg h₁, dif_neg h₂]

/-- **Addressing independence of hierarchy outcomes.**  For every constitutional rule, the
first-difference outcome of two rooted digraphs is the same for every choice of canonical
addressings of each. -/
theorem hierarchyOutcome_canonical_iff {left right : RootedDigraph Atom}
    {leftFirst leftSecond : left.Addressing} {rightFirst rightSecond : right.Addressing}
    (hleftFirst : CanonicalAddressing molecule leftFirst)
    (hleftSecond : CanonicalAddressing molecule leftSecond)
    (hrightFirst : CanonicalAddressing molecule rightFirst)
    (hrightSecond : CanonicalAddressing molecule rightSecond)
    (rule : ConstitutionalRule) (outcome : Ordering) :
    ConstitutionalHierarchyOutcome molecule rule left leftFirst right rightFirst outcome ↔
      ConstitutionalHierarchyOutcome molecule rule left leftSecond right rightSecond outcome := by
  apply FirstDifferenceOutcome.congr
  intro position outcome
  rw [constitutionalOutcomeAt_iff, constitutionalOutcomeAt_iff,
    ruleValue_eq_of_addressObservation_eq molecule rule position
      (addressObservation_canonical_eq molecule hleftFirst hleftSecond rule position),
    ruleValue_eq_of_addressObservation_eq molecule rule position
      (addressObservation_canonical_eq molecule hrightFirst hrightSecond rule position)]

end Family

/-! ## Every addressed rooted digraph has a canonical addressing -/

section Existence

variable [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  {graph : RootedDigraph Atom} (base : graph.Addressing)

local instance : Fintype graph.Node := graph.nodeFintype

/-- Descending order of nodes by a key. -/
def KeyDesc {K : Type*} [LinearOrder K] (key : graph.Node → K) (x y : graph.Node) : Prop :=
  key y ≤ key x

instance {K : Type*} [LinearOrder K] (key : graph.Node → K) : DecidableRel (KeyDesc key) :=
  fun x y => inferInstanceAs (Decidable (key y ≤ key x))

instance {K : Type*} [LinearOrder K] (key : graph.Node → K) : Std.Total (KeyDesc key) :=
  ⟨fun x y => le_total (key y) (key x)⟩

instance {K : Type*} [LinearOrder K] (key : graph.Node → K) : IsTrans graph.Node (KeyDesc key) :=
  ⟨fun _ _ _ h₁ h₂ => le_trans h₂ h₁⟩

/-- The parent of a non-root node in the tree-shaped addressed digraph. -/
def parentOf (node : graph.Node) : graph.Node :=
  if h : node = graph.root then graph.root
  else Classical.choose (base.existsUnique_parent node h).exists

omit [Fintype Atom] [DecidableEq Atom] in
theorem parentOf_child {node : graph.Node} (h : node ≠ graph.root) :
    graph.child (parentOf base node) node := by
  unfold parentOf
  rw [dif_neg h]
  exact Classical.choose_spec (base.existsUnique_parent node h).exists

omit [Fintype Atom] [DecidableEq Atom] in
include base in
theorem ne_root_of_child {parent node : graph.Node} (h : graph.child parent node) :
    node ≠ graph.root := by
  rintro rfl
  exact base.not_child_root parent h

omit [Fintype Atom] [DecidableEq Atom] in
theorem parentOf_eq {parent node : graph.Node} (h : graph.child parent node) :
    parentOf base node = parent :=
  base.parent_unique (parentOf_child base (ne_root_of_child base h)) h

/-- Children ranked in descending vector-key order. -/
def rankedChildren (parent : graph.Node) : List graph.Node :=
  (graph.childList parent).insertionSort (KeyDesc (ruleKey molecule graph graph.width graph.height))

theorem mem_rankedChildren {parent child : graph.Node} :
    child ∈ rankedChildren molecule parent ↔ graph.child parent child := by
  rw [rankedChildren, List.mem_insertionSort, graph.mem_childList]

theorem rankedChildren_nodup (parent : graph.Node) : (rankedChildren molecule parent).Nodup :=
  (List.perm_insertionSort _ _).nodup_iff.2 (graph.childList_nodup parent)

/-- Canonical address: the parent's canonical address followed by the rank among siblings. -/
def canonicalAddress (node : graph.Node) : List ℕ :=
  if _hroot : node = graph.root then []
  else canonicalAddress (parentOf base node) ++
    [(rankedChildren molecule (parentOf base node)).idxOf node]
termination_by graph.depth node
decreasing_by
  have := graph.child_depth (parentOf_child base _hroot)
  omega

theorem canonicalAddress_root : canonicalAddress molecule base graph.root = [] := by
  rw [canonicalAddress, dif_pos rfl]

theorem canonicalAddress_child {parent node : graph.Node} (h : graph.child parent node) :
    canonicalAddress molecule base node =
      canonicalAddress molecule base parent ++ [(rankedChildren molecule parent).idxOf node] := by
  rw [canonicalAddress, dif_neg (ne_root_of_child base h), parentOf_eq base h]

theorem canonicalAddress_eq_nil_iff (node : graph.Node) :
    canonicalAddress molecule base node = [] ↔ node = graph.root := by
  constructor
  · intro h
    by_contra hne
    rw [canonicalAddress_child molecule base (parentOf_child base hne)] at h
    simp at h
  · rintro rfl
    exact canonicalAddress_root molecule base

theorem canonicalAddress_injective : Function.Injective (canonicalAddress molecule base) := by
  intro first
  have hreachable := graph.reachable first
  induction hreachable with
  | refl =>
      intro second h
      rw [canonicalAddress_root] at h
      exact ((canonicalAddress_eq_nil_iff molecule base second).1 h.symm).symm
  | @tail parent node _ hedge ih =>
      intro second h
      have hsecond : second ≠ graph.root := by
        rintro rfl
        rw [canonicalAddress_root, canonicalAddress_child molecule base hedge] at h
        simp at h
      have hsecondEdge := parentOf_child base hsecond
      rw [canonicalAddress_child molecule base hedge,
        canonicalAddress_child molecule base hsecondEdge] at h
      obtain ⟨hprefix, hlast⟩ := List.append_inj' h rfl
      have hparent : parent = parentOf base second := ih hprefix
      rw [← hparent] at hlast
      have hidx : (rankedChildren molecule parent).idxOf node =
          (rankedChildren molecule parent).idxOf second := by
        simpa using hlast
      exact (List.idxOf_inj ((mem_rankedChildren molecule).2 hedge)).1 hidx

/-- The canonical addressing constructed from any parent-preserving addressing. -/
def canonicalAddressingOf : graph.Addressing where
  address := canonicalAddress molecule base
  address_injective := canonicalAddress_injective molecule base
  root_address := canonicalAddress_root molecule base
  child_iff := by
    intro parent node
    constructor
    · intro h
      exact ⟨_, canonicalAddress_child molecule base h⟩
    · rintro ⟨slot, hslot⟩
      have hne : node ≠ graph.root := by
        rintro rfl
        rw [canonicalAddress_root] at hslot
        simp at hslot
      have hedge := parentOf_child base hne
      rw [canonicalAddress_child molecule base hedge] at hslot
      obtain ⟨hprefix, _⟩ := List.append_inj' hslot rfl
      rw [← canonicalAddress_injective molecule base hprefix]
      exact hedge

theorem canonicalAddressingOf_slot {parent child : graph.Node} {slot : ℕ}
    (h : (canonicalAddressingOf molecule base).address child =
      (canonicalAddressingOf molecule base).address parent ++ [slot]) :
    graph.child parent child ∧ slot = (rankedChildren molecule parent).idxOf child := by
  have hedge := ((canonicalAddressingOf molecule base).child_iff parent child).2 ⟨slot, h⟩
  refine ⟨hedge, ?_⟩
  change canonicalAddress molecule base child = canonicalAddress molecule base parent ++ [slot] at h
  rw [canonicalAddress_child molecule base hedge] at h
  simpa using (List.append_inj' h rfl).2.symm

/-- **Existence.**  The constructed addressing is canonical. -/
theorem canonicalAddressingOf_canonical :
    CanonicalAddressing molecule (canonicalAddressingOf molecule base) := by
  constructor
  · intro parent
    refine ⟨(rankedChildren molecule parent).length, fun slot => ?_⟩
    constructor
    · rintro ⟨child, hchild⟩
      obtain ⟨hedge, rfl⟩ := canonicalAddressingOf_slot molecule base hchild
      exact List.idxOf_lt_length_of_mem ((mem_rankedChildren molecule).2 hedge)
    · intro hslot
      refine ⟨(rankedChildren molecule parent)[slot], ?_⟩
      have hmem := List.getElem_mem hslot
      have hedge := (mem_rankedChildren molecule).1 hmem
      change canonicalAddress molecule base _ = canonicalAddress molecule base parent ++ [slot]
      rw [canonicalAddress_child molecule base hedge,
        (rankedChildren_nodup molecule parent).idxOf_getElem slot hslot]
  · intro parent first second firstSlot secondSlot hfirst hsecond hlt
    obtain ⟨hfirstEdge, rfl⟩ := canonicalAddressingOf_slot molecule base hfirst
    obtain ⟨hsecondEdge, rfl⟩ := canonicalAddressingOf_slot molecule base hsecond
    have hpair : (rankedChildren molecule parent).Pairwise
        (KeyDesc (ruleKey molecule graph graph.width graph.height)) :=
      List.pairwise_insertionSort _ _
    have hfl := List.idxOf_lt_length_of_mem ((mem_rankedChildren molecule).2 hfirstEdge)
    have hsl := List.idxOf_lt_length_of_mem ((mem_rankedChildren molecule).2 hsecondEdge)
    have h := List.pairwise_iff_getElem.1 hpair _ _ hfl hsl hlt
    rw [List.getElem_idxOf hfl, List.getElem_idxOf hsl] at h
    exact h

/-- Every rooted digraph possessing a parent-preserving addressing possesses a canonical one. -/
theorem exists_canonicalAddressing (base : graph.Addressing) :
    ∃ addressing : graph.Addressing, CanonicalAddressing molecule addressing :=
  ⟨canonicalAddressingOf molecule base, canonicalAddressingOf_canonical molecule base⟩

end Existence

/-! ## Representation invariance -/

section Transport

variable [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  {left right : RootedDigraph Atom} (iso : RootedDigraph.Iso left right)

local instance (graph : RootedDigraph Atom) : Fintype graph.Node := graph.nodeFintype

omit [Fintype Atom] [DecidableEq Atom] in
include iso in
theorem width_eq_of_iso : left.width = right.width :=
  Fintype.card_congr iso.toEquiv

omit [Fintype Atom] [DecidableEq Atom] in
include iso in
theorem height_eq_of_iso : left.height = right.height := by
  apply le_antisymm
  · apply Finset.sup_le
    intro node _
    rw [iso.map_depth node]
    exact right.depth_le_height _
  · apply Finset.sup_le
    intro node _
    have h := iso.map_depth (iso.toEquiv.symm node)
    simp only [Equiv.apply_symm_apply] at h
    rw [← h]
    exact left.depth_le_height _

omit [Fintype Atom] [DecidableEq Atom] in
theorem childList_iso_perm (node : left.Node) :
    (right.childList (iso.toEquiv node)).Perm ((left.childList node).map iso.toEquiv) := by
  apply (List.perm_ext_iff_of_nodup (right.childList_nodup _)
    ((left.childList_nodup node).map iso.toEquiv.injective)).2
  intro child
  rw [right.mem_childList, List.mem_map]
  constructor
  · intro h
    refine ⟨iso.toEquiv.symm child, ?_, by simp⟩
    rw [left.mem_childList, iso.map_child]
    simpa using h
  · rintro ⟨original, horiginal, rfl⟩
    exact (iso.map_child node original).1 ((left.mem_childList).1 horiginal)

theorem nodeObservation_iso (rule : ConstitutionalRule) (node : left.Node) :
    nodeObservation molecule right rule (iso.toEquiv node) =
      nodeObservation molecule left rule node := by
  simp only [nodeObservation, ← iso.map_label node, ← iso.map_depth node]

/-- Vector keys are representation-invariant. -/
theorem ruleKey_iso (W D : ℕ) :
    ∀ node : left.Node,
      ruleKey molecule right W D (iso.toEquiv node) = ruleKey molecule left W D node := by
  refine node_induction left ?_
  intro node ih
  rw [ruleKey_eq, ruleKey_eq]
  have hchildren :
      sortDesc ((right.childList (iso.toEquiv node)).map (ruleKey molecule right W D)) =
        sortDesc ((left.childList node).map (ruleKey molecule left W D)) := by
    rw [Certificate.CanonicalSphereKey.sortDesc_eq_of_perm
      ((childList_iso_perm iso node).map (ruleKey molecule right W D)), List.map_map]
    congr 1
    exact List.map_congr_left fun child hchild => ih child ((left.mem_childList).1 hchild)
  simp only [ruleComponent, nodeObservation_iso molecule iso, hchildren]

/-- Canonical addressings transport along representation isomorphisms. -/
theorem canonicalAddressing_transport {addressing : left.Addressing}
    (h : CanonicalAddressing molecule addressing) :
    CanonicalAddressing molecule (addressing.transport iso) := by
  obtain ⟨hdense, hsorted⟩ := h
  constructor
  · intro parent
    obtain ⟨count, hcount⟩ := hdense (iso.toEquiv.symm parent)
    refine ⟨count, fun slot => ?_⟩
    rw [← hcount slot]
    simp only [RootedDigraph.Addressing.transport_address]
    constructor
    · rintro ⟨child, hchild⟩
      exact ⟨iso.toEquiv.symm child, hchild⟩
    · rintro ⟨child, hchild⟩
      exact ⟨iso.toEquiv child, by simpa using hchild⟩
  · intro parent first second firstSlot secondSlot hfirst hsecond hlt
    simp only [RootedDigraph.Addressing.transport_address] at hfirst hsecond
    have h := hsorted _ _ _ firstSlot secondSlot hfirst hsecond hlt
    rw [← width_eq_of_iso iso, ← height_eq_of_iso iso]
    rw [← ruleKey_iso molecule iso, ← ruleKey_iso molecule iso] at h
    simpa using h

/-- The canonical family satisfies the naturality field of `ConstitutionalProblemData`. -/
theorem canonicalAddressing_transport_iff (addressing : left.Addressing) :
    CanonicalAddressing molecule addressing ↔
      CanonicalAddressing molecule (addressing.transport iso) := by
  constructor
  · exact canonicalAddressing_transport molecule iso
  · intro h
    have := canonicalAddressing_transport molecule iso.symm h
    rwa [RootedDigraph.Addressing.transport_symm_transport] at this

end Transport

/-! ## Installing the family in constitutional problem data -/

namespace ConstitutionalProblemData

variable {Unit : Type u} [Fintype Atom] [DecidableEq Atom]

/-- Replace the admissible addressing family of constitutional problem data by the canonical one.
Every other field, including the admissible expansions and later-rule judgments, is retained. -/
def withCanonicalAddressing (data : ConstitutionalProblemData Atom Unit) :
    ConstitutionalProblemData Atom Unit :=
  { data with
    admissibleAddressing := fun _ _ _ addressing => CanonicalAddressing data.molecule addressing
    addressing_invariant := fun _ _ _ _ iso addressing =>
      canonicalAddressing_transport_iff data.molecule iso addressing }

/-- **Addressing independence**, the obligation named by the canonical-addressing boundary, holds
for every descriptor map, unit, constitutional rule, and pair of rooted digraphs. -/
theorem withCanonicalAddressing_addressingIndependent (data : ConstitutionalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (rule : ConstitutionalRule)
    (left right : RootedDigraph Atom) :
    data.withCanonicalAddressing.AddressingIndependent descriptorMap unit rule left right := by
  intro firstLeft firstRight secondLeft secondRight firstOutcome secondOutcome
    hfirstLeft hfirstRight hsecondLeft hsecondRight hfirst hsecond
  have hmoved := (hierarchyOutcome_canonical_iff data.molecule hsecondLeft hfirstLeft
    hsecondRight hfirstRight rule secondOutcome).1 hsecond
  exact constitutionalHierarchyOutcome_functional data.molecule rule left firstLeft right
    firstRight hfirst hmoved

/-- Every pair of addressed rooted digraphs has exactly one canonical constitutional outcome for
each of Rules 1a, 1b, and 2. -/
theorem withCanonicalAddressing_canonicalOutcome_existsUnique
    (data : ConstitutionalProblemData Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (rule : ConstitutionalRule) {left right : RootedDigraph Atom}
    (leftAddressing : left.Addressing) (rightAddressing : right.Addressing) :
    ∃! outcome,
      data.withCanonicalAddressing.CanonicalOutcome descriptorMap unit rule left right outcome := by
  obtain ⟨outcome, houtcome⟩ :=
    data.withCanonicalAddressing.canonicalOutcome_exists_of_addressingIndependent
      descriptorMap unit rule left right
      (exists_canonicalAddressing data.molecule leftAddressing)
      (exists_canonicalAddressing data.molecule rightAddressing)
      (data.withCanonicalAddressing_addressingIndependent descriptorMap unit rule left right)
  exact ⟨outcome, houtcome, fun other hother =>
    data.withCanonicalAddressing.canonicalOutcome_functional descriptorMap unit rule left right
      hother houtcome⟩

/-- In particular, the constitutional judgment of the constructed `Problem` is total and
functional on every pair of admissible ligand expansions. -/
theorem withCanonicalAddressing_ruleJudgment_existsUnique
    (data : ConstitutionalProblemData Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (rule : ConstitutionalRule) {leftLigand rightLigand : Fin 4}
    {left right : RootedDigraph Atom}
    (hleft : data.withCanonicalAddressing.toProblem.admissibleExpansion unit leftLigand left)
    (hright : data.withCanonicalAddressing.toProblem.admissibleExpansion unit rightLigand right) :
    ∃! outcome,
      data.withCanonicalAddressing.toProblem.OutcomeOnGraphs descriptorMap rule.toSequenceRule
        unit left right outcome := by
  obtain ⟨_, leftAddressing, _⟩ := data.expansion_sound unit leftLigand left hleft
  obtain ⟨_, rightAddressing, _⟩ := data.expansion_sound unit rightLigand right hright
  have h := data.withCanonicalAddressing_canonicalOutcome_existsUnique descriptorMap unit rule
    leftAddressing rightAddressing
  cases rule <;> exact h

end ConstitutionalProblemData

end
end DeclarativeCIP
end OneCenter
end TetraStereo
