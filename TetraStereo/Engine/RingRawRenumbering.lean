import TetraStereo.Engine.RingGeometryTransport
import TetraStereo.Engine.RingGroupedReport

set_option autoImplicit false

namespace TetraStereo.Engine.RingRawRenumbering

open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingActiveDistanceSchedule (Visible distance)

/-- The input witness refers only to physical atom records, raw bonds and coordinates. -/
structure Renumbering (i j : Input) where
  atoms : i.certified.Atom ≃ j.certified.Atom
  records : ∀ a, j.molecule.atoms[(atoms a).val]? = i.molecule.atoms[a.val]?
  bonds : ∀ a b, j.molecule.bondOrder (atoms a).val (atoms b).val = i.molecule.bondOrder a.val b.val
  positions : ∀ a, j.spatial.positions[(atoms a).val]? = i.spatial.positions[a.val]?

variable {i j : Input}

def Renumbering.symm (r : Renumbering i j) : Renumbering j i where
  atoms := r.atoms.symm
  records := fun b => by simpa using (r.records (r.atoms.symm b)).symm
  bonds := fun a b => by simpa using (r.bonds (r.atoms.symm a) (r.atoms.symm b)).symm
  positions := fun b => by simpa using (r.positions (r.atoms.symm b)).symm

private theorem raw_adj (i : Input) (a b : i.certified.Atom) :
    i.certified.moleculeGraph.Adj a b ↔ 0 < i.molecule.bondOrder a.val b.val :=
  LocalizedChemicalRingPhysicalSense.adj_iff i.molecule i.certified i.agreement
    i.admissible.1.1 i.admissible.1.2 i.supported a b

theorem Renumbering.adj (r : Renumbering i j) (a b : i.certified.Atom) :
    i.certified.moleculeGraph.Adj a b ↔ j.certified.moleculeGraph.Adj (r.atoms a) (r.atoms b) := by
  rw [raw_adj, raw_adj, r.bonds]

private theorem count_eq {n m : Nat} (e : Fin n ≃ Fin m) : n = m := by
  simpa using Fintype.card_congr e

/-- Check a proposed numbering directly against the raw inputs. -/
def check? (i j : Input) (e : i.certified.Atom ≃ j.certified.Atom) : Option (Renumbering i j) :=
  if h : (∀ a, j.molecule.atoms[(e a).val]? = i.molecule.atoms[a.val]?) ∧
      (∀ a b, j.molecule.bondOrder (e a).val (e b).val = i.molecule.bondOrder a.val b.val) ∧
      (∀ a, j.spatial.positions[(e a).val]? = i.spatial.positions[a.val]?) then
    some ⟨e, h.1, h.2.1, h.2.2⟩
  else none

/-- Assign each remaining source atom one unused image. Exact coordinates and atom records
prune the search before the complete raw bond check at a leaf. -/
private def search (i j : Input) : List i.certified.Atom →
    (i.certified.Atom ≃ j.certified.Atom) → Option (Renumbering i j)
  | [], e => check? i j e
  | a :: rest, e => (a :: rest).findSome? fun b =>
    if j.spatial.positions[(e b).val]? = i.spatial.positions[a.val]? ∧
        j.molecule.atoms[(e b).val]? = i.molecule.atoms[a.val]? ∧
        (∀ x ∉ a :: rest, j.molecule.bondOrder (e b).val (e x).val = i.molecule.bondOrder a.val x.val) then
      search i j rest ((Equiv.swap a b).trans e)
    else none

/-- Recover a renumbering from two independently admitted inputs, including when some
atoms have coincident coordinates. A known permutation can be verified with `check?`. -/
def find? (i j : Input) : Option (Renumbering i j) :=
  if h : i.certified.certified.input.molecule.atomCount = j.certified.certified.input.molecule.atomCount then
    search i j (List.finRange _) (finCongr h)
  else none

private theorem search_complete (r : Renumbering i j) (todo : List i.certified.Atom)
    (e : i.certified.Atom ≃ j.certified.Atom) (fixed : ∀ a ∉ todo, e a = r.atoms a) :
    (search i j todo e).isSome = true := by
  induction todo generalizing e with
  | nil =>
    have eq : e = r.atoms := Equiv.ext (fun a => fixed a (by simp))
    simp [search, check?, eq, r.records, r.bonds, r.positions]
  | cons a rest ih =>
    let b := e.symm (r.atoms a)
    have hit : e b = r.atoms a := e.apply_symm_apply _
    have mem : b ∈ a :: rest := by
      by_contra missing
      have eq := r.atoms.injective (hit.symm.trans (fixed b missing))
      exact missing (eq ▸ List.mem_cons_self)
    apply Option.isSome_iff_ne_none.mpr
    intro no
    have noneAt := List.findSome?_eq_none_iff.mp no b mem
    have bonds : ∀ x ∉ a :: rest, j.molecule.bondOrder (e b).val (e x).val = i.molecule.bondOrder a.val x.val :=
      fun x hx => by rw [hit,fixed x hx,r.bonds]
    rw [hit] at bonds
    simp only [hit, r.positions, r.records, true_and] at noneAt
    rw [if_pos bonds] at noneAt
    have next := ih ((Equiv.swap a b).trans e) (by
      intro x hx
      by_cases same : x = a
      · subst x; simpa using hit
      · have away : x ≠ b := by
          intro eq
          subst x
          rcases List.mem_cons.mp mem with ha | hr
          · exact same ha
          · exact hx hr
        simpa [Equiv.swap_apply_of_ne_of_ne same away] using fixed x (by simp [same, hx]))
    rw [noneAt] at next
    contradiction

/-- Failure is equivalent to the absence of a physical raw renumbering. -/
theorem find_complete : (find? i j).isSome = true ↔ Nonempty (Renumbering i j) := by
  constructor
  · intro h
    exact ⟨(find? i j).get h⟩
  · rintro ⟨r⟩
    unfold find?
    rw [dif_pos (count_eq r.atoms)]
    exact search_complete r _ _ (by simp)

noncomputable section

/-- Renaming a molecular history carries the current atom and retains duplicate provenance. -/
def nodeMap {n m : Nat} (e : Fin n ≃ Fin m) (v : OfficialCIPNode (Fin n)) :
    OfficialCIPNode (Fin m) := ⟨v.current?.map e, v.history.map e, v.provenance⟩

private theorem node_extend {n m : Nat} (e : Fin n ≃ Fin m) (v : OfficialCIPNode (Fin n)) (a : Fin n) :
    nodeMap e (v.extend a 0) = (nodeMap e v).extend (e a) 0 := by
  obtain rfl := count_eq e
  exact mapOfficialNode_extend e v a 0

private theorem node_parent {n m : Nat} (e : Fin n ≃ Fin m) (v : OfficialCIPNode (Fin n)) {a : Fin n}
    (h : v.parent? ≠ some a) : (nodeMap e v).parent? ≠ some (e a) := by
  obtain rfl := count_eq e
  exact mapOfficialNode_parent?_ne e h


/-- Input fields used by the full-path publisher once the graph is materialized. -/
structure MolecularRecord where
  element : Element
  mass : Option Nat
  charge : Int
  aromatic : Bool
  deriving DecidableEq

def molecularRecord (atom : AtomSpec) : MolecularRecord :=
  ⟨atom.element, CIPRule2MassData.rule2MassPico? atom.element.atomicNumber atom.isotope?, atom.charge, atom.aromatic⟩

/-- A molecular correspondence after hydrogen materialization. The graph keeps the isotope
mass used by Rule 2, the element, formal charge, and aromaticity used by center selection. -/
structure AtomMap (i j : Input) where
  atoms : i.certified.Atom ≃ j.certified.Atom
  records : ∀ a, (j.molecule.atoms[(atoms a).val]?).map molecularRecord =
    (i.molecule.atoms[a.val]?).map molecularRecord
  bonds : ∀ a b, j.molecule.bondOrder (atoms a).val (atoms b).val = i.molecule.bondOrder a.val b.val
  positions : ∀ a, j.spatial.positions[(atoms a).val]? = i.spatial.positions[a.val]?

def Renumbering.toAtomMap (r : Renumbering i j) : AtomMap i j :=
  ⟨r.atoms, fun a => congrArg (Option.map molecularRecord) (r.records a), r.bonds, r.positions⟩

instance : Coe (Renumbering i j) (AtomMap i j) := ⟨Renumbering.toAtomMap⟩

namespace AtomMap
def symm (r : AtomMap i j) : AtomMap j i where
  atoms := r.atoms.symm
  records := fun b => by simpa using (r.records (r.atoms.symm b)).symm
  bonds := fun a b => by simpa using (r.bonds (r.atoms.symm a) (r.atoms.symm b)).symm
  positions := fun b => by simpa using (r.positions (r.atoms.symm b)).symm

theorem adj (r : AtomMap i j) (a b : i.certified.Atom) :
    i.certified.moleculeGraph.Adj a b ↔ j.certified.moleculeGraph.Adj (r.atoms a) (r.atoms b) := by
  rw [raw_adj,raw_adj,r.bonds]

private theorem observation_record (i : Input) (q : Arm i) (terminal : Bool) :
    RingRetainedChemicalTrace.observation? i q terminal = (do
      let node := q.occurrence.val.node
      let a ← node.current?
      let recd ← (i.molecule.atoms[a.val]?).map molecularRecord
      let z := recd.element.atomicNumber
      guard (z > 0)
      match node.provenance with
      | .realAtom =>
        let mass ← recd.mass
        return ⟨z,RingRetainedChemicalTrace.duplicateValue i.molecule.atomCount none,mass⟩
      | .ringDuplicate origin =>
        guard (terminal && origin ≤ i.molecule.atomCount && node.history.head? == some a &&
          node.history.tail.reverse.idxOf a == origin && node.history.tail.contains a)
        let mass ← CIPRule2MassData.rule2MassPico? z none
        return ⟨z,RingRetainedChemicalTrace.duplicateValue i.molecule.atomCount (some origin),mass⟩
      | _ => none) := by
  unfold RingRetainedChemicalTrace.observation?
  simp only [Option.bind_eq_bind]
  congr 1
  funext a
  cases i.molecule.atoms[a.val]? <;> rfl

private theorem simple_image (r : AtomMap i j) {root v addr}
    (path : SimpleOccurrencePath i.certified root v addr) :
    ∃ address, SimpleOccurrencePath j.certified (r.atoms root) (nodeMap r.atoms v) address ∧
      address.length = addr.length := by
  induction path with
  | root => exact ⟨[], .root, rfl⟩
  | @step parent addr a b path current adj np fresh ih =>
    obtain ⟨address, target, len⟩ := ih
    rw [node_extend]
    refine ⟨_, target.step (current := r.atoms a) (by simp [nodeMap, current])
      ((r.adj a b).mp adj) (node_parent _ _ np) (by simpa [nodeMap] using fresh), ?_⟩
    simp [len]

private theorem legitimate_image (r : AtomMap i j) {root v addr}
    (occ : LegitimateOccurrence i.certified root v addr) :
    ∃ address, LegitimateOccurrence j.certified (r.atoms root) (nodeMap r.atoms v) address ∧
      address.length = addr.length := by
  cases occ with
  | simple path =>
    obtain ⟨address, target, len⟩ := simple_image r path
    exact ⟨address, .simple target, len⟩
  | @ring parent addr a b path current adj np seen =>
    obtain ⟨address, target, len⟩ := simple_image r path
    rw [node_extend]
    refine ⟨_, .ring target (current := r.atoms a) (by simp [nodeMap, current])
      ((r.adj a b).mp adj) (node_parent _ _ np) (by simpa [nodeMap] using seen), ?_⟩
    simp [len]
  | @multiple _ _ a b k _ _ adj bound pos =>
    rw [i.single a b adj] at bound
    exact (pos (Nat.lt_one_iff.mp bound)).elim

private def address (r : AtomMap i j) (q : Site i) : List Nat :=
  j.certified.canonicalAddress (r.atoms q.val.root) (nodeMap r.atoms q.val.node)

private theorem site_path (r : AtomMap i j) (q : Site i) :
    LegitimateOccurrence j.certified (r.atoms q.val.root) (nodeMap r.atoms q.val.node) (address r q) ∧
      (address r q).length = q.val.address.length := by
  obtain ⟨a, path, len⟩ := legitimate_image r (i.certified.carrierOccurrence_legitimate i.single q)
  have canon := (j.certified.legitimateOccurrence_transport j.single 1 path).sourceAddress
  change a = address r q at canon
  rw [← canon]
  exact ⟨path, len⟩

/-- The target enumerates its own child slots along the renamed molecular path. -/
def site (r : AtomMap i j) (q : Site i) : Site j :=
  ⟨_, j.certified.legitimateOccurrence_mem_localizedOccurrences_of_length (site_path r q).1 (by
    rw [(site_path r q).2, ← count_eq r.atoms]
    have grade := i.certified.localizedCIPOccurrence_depthGrade q
    omega)⟩

theorem visible (r : AtomMap i j) (q t : Site i) :
    Visible (site r q) (site r t) ↔ Visible q t := by
  have depth (u : Site i) : distance (site r u) = distance u := (site_path r u).2
  unfold Visible
  simp only [depth]
  change (_ = _ ∧ _ ∧ t.val.node.current?.map r.atoms ≠ some (r.atoms q.val.root)) ↔ _
  cases t.val.node.current? <;> simp [site]

private theorem site_ext {q t : Site i} (root : q.val.root = t.val.root)
    (node : q.val.node = t.val.node) : q = t := by
  have canon (v : Site i) := (i.certified.legitimateOccurrence_transport i.single 1
    (i.certified.carrierOccurrence_legitimate i.single v)).sourceAddress
  apply Subtype.ext
  exact i.certified.declarativeLocalizedOccurrence_functional_at_root_address
    ((i.certified.mem_localizedOccurrences_iff _ _).mp q.property)
    ((i.certified.mem_localizedOccurrences_iff _ _).mp t.property) root
    (by rw [canon q, canon t, root, node])

@[simp] theorem site_back (r : AtomMap i j) (q : Site i) : site r.symm (site r q) = q := by
  apply site_ext
  · exact r.atoms.symm_apply_apply _
  · change nodeMap r.atoms.symm (nodeMap r.atoms q.val.node) = _
    generalize q.val.node = v
    cases v with
    | mk current history prov => cases current <;> simp [nodeMap, List.map_map]

def sites (r : AtomMap i j) : Site i ≃ Site j where
  toFun := site r
  invFun := site r.symm
  left_inv := site_back r
  right_inv := site_back r.symm

def arm (r : AtomMap i j) (u : Arm i) : Arm j :=
  ⟨site r u.occurrence, u.previous?.map (site r)⟩

@[simp] theorem arm_back (r : AtomMap i j) (u : Arm i) : arm r.symm (arm r u) = u := by
  cases u with
  | mk occ prev => cases prev <;> simp [arm]

private abbrev outward {i : Input} (p c : Site i) :=
  c.val ∈ i.certified.localizedCarrierOutwardChildFrames
    (fuel := i.certified.certified.input.molecule.atomCount + 1) p.val

/-- One outward edge appends precisely one physical atom to a real parent. -/
private theorem outward_extension {p c : Site i} (edge : outward p c) :
    p.val.node.provenance = .realAtom ∧ ∃ a, c.val.node = p.val.node.extend a 0 := by
  unfold outward localizedCarrierOutwardChildFrames at edge
  rw [List.mem_filter] at edge
  simp only [Bool.and_eq_true, beq_iff_eq] at edge
  obtain ⟨_, ⟨root, len⟩, drop⟩ := edge
  have ne : c.val.address ≠ [] := by intro h; simp [h] at len
  have addr : c.val.address = p.val.address ++ [c.val.address.getLast ne] := by
    simpa [drop] using (List.dropLast_concat_getLast ne).symm
  obtain ⟨node, mem, eq⟩ := i.certified.declarativeLocalizedOccurrence_immediate_child
    ((i.certified.mem_localizedOccurrences_iff _ _).mp p.property)
    ((i.certified.mem_localizedOccurrences_iff _ _).mp c.property) root _ addr
  have actual := congrArg LocalizedCIPOccurrenceFrame.node eq
  cases dup : p.val.node.isDuplicateLeaf with
  | true => simp [executableOfficialCIPChildren, dup] at mem
  | false =>
    have real : p.val.node.provenance = .realAtom := by
      rcases i.certified.carrierOccurrence_provenance_simple_or_ring i.single p with h | ⟨d, h⟩
      · exact h
      · rw [i.certified.isDuplicateLeaf_eq_true_of_ring_provenance _ h] at dup
        contradiction
    refine ⟨real, ?_⟩
    simp only [executableOfficialCIPChildren, dup, Bool.false_eq_true, if_false,
      List.mk_mem_zipIdx_iff_getElem?, List.getElem?_map] at mem
    cases h : (i.certified.executableOfficialChildCopies p.val.node)[c.val.address.getLast ne]? with
    | none => simp [h] at mem
    | some copy =>
      have zero := i.certified.executableOfficialChildCopy_index_zero i.single _ _ _ (List.mem_of_getElem? h)
      exact ⟨copy.1, actual.trans (by simpa [h, zero] using mem.symm)⟩

private theorem outward_map (r : AtomMap i j) {p c : Site i} (edge : outward p c) :
    outward (site r p) (site r c) := by
  obtain ⟨real, a, ext⟩ := outward_extension edge
  unfold outward localizedCarrierOutwardChildFrames at edge ⊢
  rw [List.mem_filter] at edge ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at edge ⊢
  obtain ⟨_, ⟨root, len⟩, _⟩ := edge
  refine ⟨(site r c).property, ⟨congrArg r.atoms root, ?_⟩, ?_⟩
  · exact ((site_path r c).2.trans len).trans (congrArg (· + 1) (site_path r p).2.symm)
  · have path := j.certified.simpleOccurrencePath_of_carrier_real j.single (site r p) real
    have drop := j.certified.transportedAddress_extend_dropLast 1 path (r.atoms a)
    change (j.certified.canonicalAddress _ (nodeMap r.atoms c.val.node)).dropLast =
      j.certified.canonicalAddress _ (nodeMap r.atoms p.val.node)
    rw [root, ext, node_extend]
    simpa [transportedAddress, canonicalAddress, site] using drop


private abbrev near {i : Input} (p c : Site i) := c.val ∈ i.certified.localizedRerootNeighborFrames
  (fuel := i.certified.certified.input.molecule.atomCount + 1) p.val

private theorem near_map (r : AtomMap i j) {p c : Site i} (h : near p c) :
    near (site r p) (site r c) := by
  unfold near localizedRerootNeighborFrames at h ⊢
  rw [List.mem_append, i.certified.mem_localizedCarrierParentFrames_iff_outward] at h
  rw [List.mem_append, j.certified.mem_localizedCarrierParentFrames_iff_outward]
  exact h.imp (outward_map r) (outward_map r)

private theorem equal_address {p q : Site i} (root : p.val.root = q.val.root) :
    p.val.address = q.val.address ↔ p = q := by
  refine ⟨fun h => Subtype.ext (i.certified.declarativeLocalizedOccurrence_functional_at_root_address
    ((i.certified.mem_localizedOccurrences_iff _ _).mp p.property)
    ((i.certified.mem_localizedOccurrences_iff _ _).mp q.property) root h), ?_⟩
  rintro rfl
  rfl

private theorem aligned (r : AtomMap i j) {u : Arm i} (h : i.certified.cursorPreviousRootAligned u) :
    j.certified.cursorPreviousRootAligned (arm r u) := by
  intro x hx
  change u.previous?.map _ = some x at hx
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hx
  exact congrArg r.atoms (h v hv)

private theorem child_map (r : AtomMap i j) {u v : Arm i} (h : i.certified.cursorPreviousRootAligned u)
    (mem : v ∈ i.certified.executableLocalizedRerootChildren u) :
    arm r v ∈ j.certified.executableLocalizedRerootChildren (arm r u) := by
  rw [i.certified.executableLocalizedRerootChildren_mem_iff, i.certified.mem_intendedLocalizedRerootChildFrames_iff] at mem
  rw [j.certified.executableLocalizedRerootChildren_mem_iff, j.certified.mem_intendedLocalizedRerootChildFrames_iff]
  obtain ⟨prev, leaf, nb, cut⟩ := mem
  refine ⟨by simp [arm, prev], leaf, near_map r nb, ?_⟩
  intro x hx eq
  change u.previous?.map _ = some x at hx
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hx
  have root := (i.certified.localizedRerootNeighborFrames_root_eq _ _ nb).trans (h t ht).symm
  have eqSite := (equal_address (congrArg r.atoms root : (site r v.occurrence).val.root =
    (site r t).val.root)).mp eq
  exact cut t ht ((equal_address root).mpr ((sites r).injective eqSite))

private theorem children (r : AtomMap i j) {u : Arm i} (h : i.certified.cursorPreviousRootAligned u) :
    ((i.certified.executableLocalizedRerootChildren u).map (arm r)).Perm
      (j.certified.executableLocalizedRerootChildren (arm r u)) := by
  have inj : Function.Injective (arm r) := Function.LeftInverse.injective (arm_back r)
  apply (List.perm_ext_iff_of_nodup (List.Nodup.map inj (i.certified.executableLocalizedRerootChildren_nodup _))
    (j.certified.executableLocalizedRerootChildren_nodup _)).mpr
  intro v
  constructor
  · rintro hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
    exact child_map r h ht
  · intro hv
    have back := child_map r.symm (aligned r h) hv
    exact List.mem_map.mpr ⟨arm r.symm v, by simpa using back, arm_back r.symm v⟩

open RingGeometryExchange (Carrier Marked)
open RingRetainedChemicalTrace (observation?)

private theorem idx_map {α β : Type} [DecidableEq α] [DecidableEq β] (s : α ≃ β) (a : α) (xs : List α) :
    (xs.map s).idxOf (s a) = xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons x xs ih => by_cases h : x = a <;> simp [h,ih]

private theorem current_eq {α β : Type} [DecidableEq α] [DecidableEq β] (s : α ≃ β) (t : Option α) (a : α) :
    (t.map s == some (s a)) = (t == some a) := by
  cases t with
  | none => rfl
  | some b => by_cases h : b = a <;> simp [h]

private theorem observation (r : AtomMap i j) (q : Arm i) (terminal : Bool) :
    observation? j (arm r q) terminal = observation? i q terminal := by
  let s := r.atoms
  let xs := q.occurrence.val.node.history
  have hist (a : i.certified.Atom) : ((xs.map s).tail.contains (s a)) = xs.tail.contains a := by
    apply Bool.eq_iff_iff.mpr
    simp [← List.map_tail]
  have index (a : i.certified.Atom) : ((xs.map s).tail.reverse.idxOf (s a)) = xs.tail.reverse.idxOf a := by
    rw [← List.map_tail,← List.map_reverse,idx_map]
  have head (a : i.certified.Atom) : ((xs.map s).head? == some (s a)) = (xs.head? == some a) := by
    rw [List.head?_map,current_eq]
  rw [observation_record,observation_record]
  simp only [arm,site,nodeMap]
  cases h : q.occurrence.val.node.current? with
  | none => rfl
  | some a =>
    simp only [Option.map_some,Option.bind_eq_bind,Option.bind_some]
    rw [r.records a]
    cases prov : q.occurrence.val.node.provenance <;> first | rfl | skip
    dsimp only [xs,s] at head hist index
    have card : j.molecule.atomCount = i.molecule.atomCount :=
      (j.molecule.toSemanticMolecule?_atomCount _ j.agreement.1).symm.trans
        ((count_eq r.atoms).symm.trans (i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1))
    simp only [head,hist,index,card]

/-- A raw renumbering supplies the whole child correspondence and
all constitutional observations, for every rooted, directed molecular cursor. -/
def carrier (r : AtomMap i j) : Carrier i j where
  image := arm r
  domain := i.certified.cursorPreviousRootAligned
  below := fun q _ t ht => i.certified.executableLocalizedRerootChildren_cursorAligned q t ht
  children := fun _ h => children r h
  observation := by
    intro q aligned
    have edges := children r aligned
    have empty : (j.certified.executableLocalizedRerootChildren (arm r q)).isEmpty =
        (i.certified.executableLocalizedRerootChildren q).isEmpty := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.isEmpty_iff]
      have h := edges.length_eq
      simp only [List.length_map] at h
      simp [← List.length_eq_zero_iff,h]
    rw [empty,observation r]

theorem mark (r : AtomMap i j) (a : i.certified.Atom) :
    Marked (carrier r) a.val (r.atoms a).val := by
  intro q _
  unfold RingGroupedMark.bit
  change _ = (((q.occurrence.val.node.current?.map r.atoms).map Fin.val == some (r.atoms a).val).toNat)
  cases h : q.occurrence.val.node.current? with
  | none => rfl
  | some b =>
    by_cases same : b = a
    · subst b; simp
    · have v : b.val ≠ a.val := fun h => same (Fin.ext h)
      have v' : (r.atoms b).val ≠ (r.atoms a).val := fun h => same (r.atoms.injective (Fin.ext h))
      simp only [Option.map_some,Option.some_beq_some,beq_eq_false_iff_ne.mpr v,beq_eq_false_iff_ne.mpr v']

open RingNestedActivePair (Frame)
open RingActivePairReport (Slot)
open RingGroupedCentre (cursor)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedGenericMarkedRecalculation (readback?)

private def neighbors (r : AtomMap i j) (a : i.certified.Atom) :
    i.certified.moleculeGraph.Neighbor a ≃ j.certified.moleculeGraph.Neighbor (r.atoms a) where
  toFun b := ⟨r.atoms b.val, (r.adj a b.val).mp b.property⟩
  invFun b := ⟨r.atoms.symm b.val, (r.adj a _).mpr (by simpa using b.property)⟩
  left_inv _ := Subtype.ext (r.atoms.symm_apply_apply _)
  right_inv _ := Subtype.ext (r.atoms.apply_symm_apply _)

private def center (r : AtomMap i j) (c : i.certified.TetrahedralCenter) : j.certified.TetrahedralCenter :=
  ⟨r.atoms c.val, (j.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr
    ((Fintype.card_congr (neighbors r c.val)).symm.trans
      ((i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mp c.property))⟩

private theorem recognized (r : AtomMap i j) {q : Site i} {c}
    (h : i.certified.localizedOccurrenceDescriptorCenter? q = some c) :
    j.certified.localizedOccurrenceDescriptorCenter? (site r q) = some (center r c) := by
  obtain ⟨real, atCenter⟩ := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp h
  exact (j.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mpr
    ⟨real, by change q.val.node.current?.map r.atoms = some (r.atoms c.val); simp [atCenter]⟩

private theorem frame_cursor {q : Site i} (x : Frame i q) (k : Slot) : cursor x k = x.arm k := by
  have hp := i.certified.executableLocalizedRerootChildren_previous (⟨q,none⟩ : Arm i) (x.arm k)
    (show x.arm k ∈ RingRetainedAuxiliary.frame i.certified q from List.get_mem ..)
  change (⟨(x.arm k).occurrence,some q⟩ : Arm i) = x.arm k
  cases eq : x.arm k with
  | mk occ prev => rw [eq] at hp; cases hp; rfl

private theorem slot_inj {q : Site i} (x : Frame i q) : Function.Injective x.arm := by
  intro a b h
  have nd := i.certified.executableLocalizedRerootChildren_nodup (⟨q,none⟩ : Arm i)
  exact Fin.ext (congrArg (fun k : Fin (RingRetainedAuxiliary.frame i.certified q).length => k.val) (nd.get_inj_iff.mp h))

private theorem incident_slots (r : AtomMap i j) {q : Site i} (x : Frame i q) (y : Frame j (site r q)) :
    ∃ slots : Equiv.Perm Slot, ∀ k, arm r (x.arm k) = y.arm (slots k) := by
  classical
  have perm := children r (u := (⟨q,none⟩ : Arm i)) (i.certified.cursorPreviousRootAligned_of_none _ rfl)
  have hits (k : Slot) : ∃ t : Slot, arm r (x.arm k) = y.arm t := by
    have mem : x.arm k ∈ RingRetainedAuxiliary.frame i.certified q := List.get_mem ..
    have moved : arm r (x.arm k) ∈ RingRetainedAuxiliary.frame j.certified (site r q) :=
      perm.mem_iff.mp (List.mem_map.mpr ⟨_,mem,rfl⟩)
    obtain ⟨t, ht⟩ := List.mem_iff_get.mp moved
    exact ⟨Fin.cast y.four t, by simpa [RingNestedActivePair.Frame.arm] using ht.symm⟩
  choose slots matchArm using hits
  have inj : Function.Injective slots := by
    intro a b h
    apply slot_inj x
    apply Function.LeftInverse.injective (arm_back r)
    rw [matchArm,matchArm,h]
  exact ⟨Equiv.ofBijective slots ⟨inj,Finite.surjective_of_injective inj⟩,matchArm⟩

private theorem position (r : AtomMap i j) (a : i.certified.Atom) :
    inputGeometry i.certified a.val = inputGeometry j.certified (r.atoms a).val := by
  simp [LocalizedChemicalRingPhysicalSense.inputGeometry_val, spatialPointAt?, i.spatial_eq,
    j.spatial_eq, r.positions]

open LocalizedChemicalRingPhysicalAdmission
open LocalizedActualPhysicalBranchDecision (actualCanonicalMolecule coordinateVolume?)

/-- The four ligand coordinates at each centre can be reordered. Nonzero volume
survives that permutation, so one geometry admission suffices for both inputs. -/
theorem coordinates (r : AtomMap i j) (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    LocalizedChemicalRing.coordinatesAdmitted j = true := by
  apply (allCentersAdmitted_iff j.certified).mpr
  intro d
  let c := center r.symm d
  let ligI := i.certified.canonicalLigandEquiv c
  let ligJ := j.certified.canonicalLigandEquiv d
  let slots := (ligJ.trans (neighbors r.symm d.val)).trans ligI.symm
  obtain ⟨points, seen, nonzero, _⟩ := canonical_all_calibrated i.certified ok c
  have pos (k : Slot) : j.certified.spatialPointAt? ((actualCanonicalMolecule j.certified).ligandAtomAt d k) =
      some (points (slots k)) := by
    let a := j.certified.canonicalLigandAtom d k
    have eq : i.certified.canonicalLigandAtom c (slots k) = r.symm.atoms a :=
      congrArg Subtype.val (ligI.apply_symm_apply ((neighbors r.symm d.val) (ligJ k)))
    have p := position r.symm a
    simp only [LocalizedChemicalRingPhysicalSense.inputGeometry_val] at p
    change j.certified.spatialPointAt? a = _
    rw [p, ← eq]
    exact seen _
  refine ⟨_,?_,cartesianOrientedVolume_perm_ne_zero points slots nonzero⟩
  simp [coordinateVolume?,pos]

private theorem frameMap (r : AtomMap i j) {q : Site i} (x : Frame i q) (y : Frame j (site r q)) :
    ∃ p : RingGeometryTransport.FrameMap x y, p.carrier = carrier r := by
  obtain ⟨slots, edge⟩ := incident_slots r x y
  have ids (k : Slot) : ∃ a : i.certified.Atom,
      RingGroupedTrials.atom x k = a.val ∧ RingGroupedTrials.atom y (slots k) = (r.atoms a).val := by
    have left := x.point_at k
    have right := y.point_at (slots k)
    rw [← edge k] at right
    change (((x.arm k).occurrence.val.node.current?.map r.atoms).map Fin.val) = some _ at right
    cases h : (x.arm k).occurrence.val.node.current? with
    | none => simp [h] at left
    | some a => exact ⟨a, by simpa [h,RingGroupedTrials.atom] using left.symm,
        by simpa [h,RingGroupedTrials.atom] using right.symm⟩
  refine ⟨⟨slots,carrier r,?_,?_,?_,?_⟩,rfl⟩
  · intro k prev hp
    change some q = some prev at hp
    obtain rfl := Option.some.inj hp
    exact (x.direction k).property.1.symm
  · intro k
    simpa only [frame_cursor] using edge k
  · intro k
    obtain ⟨a,h,h'⟩ := ids k
    rw [h,h']
    exact mark r a
  · have read (ks : List Slot) :
        ((ks.map (RingGroupedTrials.atom x)).mapM (inputGeometry i.certified)) =
        (((ks.map slots).map (RingGroupedTrials.atom y)).mapM (inputGeometry j.certified)) := by
      induction ks with
      | nil => rfl
      | cons k ks ih =>
        obtain ⟨a,h,h'⟩ := ids k
        simp only [List.map_cons,List.mapM_cons,h,h',position r a,ih]
    change readback? _ ((List.finRange 4).map (RingGroupedTrials.atom x)) =
      readback? _ (((List.finRange 4).map slots).map (RingGroupedTrials.atom y))
    unfold readback?
    rw [read]

/-- The atom bijection alone constructs all occurrence, branch and physical frame matches. -/
def presentation (r : AtomMap i j) : RingGeometryTransport.Presentation i j where
  site := site r
  root := fun _ _ => r.atoms.injective.eq_iff
  visible := visible r
  localFrame := by
    intro q
    cases rec : i.certified.localizedOccurrenceDescriptorCenter? q with
    | none =>
      refine ⟨.absent rec ?_⟩
      cases img : j.certified.localizedOccurrenceDescriptorCenter? (site r q) with
      | none => rfl
      | some c =>
        have back := recognized r.symm img
        rw [site_back,rec] at back
        contradiction
    | some c =>
      obtain ⟨x,hx⟩ := RingGroupedGeometry.frame_exists rec
      obtain ⟨y,hy⟩ := RingGroupedGeometry.frame_exists (recognized r rec)
      obtain ⟨p, hp⟩ := frameMap r x y
      exact ⟨.centre hx hy p (fun u _ => by rw [hp]; rfl)⟩



/-- Change report identifiers using the core molecular correspondence. -/
def renameRow (r : AtomMap i j) (row : Nat × Option RingNestedActivePair.Labels) :=
  (if h : row.1 < i.certified.certified.input.molecule.atomCount then
    (r.atoms ⟨row.1,h⟩).val else row.1, row.2)

end AtomMap

open RingGeometryExchange (Marked)
open RingActiveDistanceSchedule (Visible)

/-- Exact raw record renumberings specialize the molecular correspondence. -/
abbrev site (r : Renumbering i j) := AtomMap.site r.toAtomMap
theorem visible (r : Renumbering i j) (q t : Site i) :
    Visible (site r q) (site r t) ↔ Visible q t :=
  AtomMap.visible r.toAtomMap q t
@[simp] theorem site_back (r : Renumbering i j) (q : Site i) : site r.symm (site r q) = q :=
  AtomMap.site_back r.toAtomMap q
abbrev sites (r : Renumbering i j) := AtomMap.sites r.toAtomMap
abbrev arm (r : Renumbering i j) := AtomMap.arm r.toAtomMap
@[simp] theorem arm_back (r : Renumbering i j) (q : Arm i) : arm r.symm (arm r q) = q :=
  AtomMap.arm_back r.toAtomMap q
abbrev carrier (r : Renumbering i j) := AtomMap.carrier r.toAtomMap
theorem mark (r : Renumbering i j) (a : i.certified.Atom) :
    Marked (carrier r) a.val (r.atoms a).val :=
  AtomMap.mark r.toAtomMap a
theorem coordinates (r : Renumbering i j) (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    LocalizedChemicalRing.coordinatesAdmitted j = true :=
  AtomMap.coordinates r.toAtomMap ok
abbrev presentation (r : Renumbering i j) := AtomMap.presentation r.toAtomMap
/-- Separately admitted numberings publish identical frozen outcomes at corresponding sites. -/
theorem publications (r : Renumbering i j) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) :
    RingGroupedPublication.state i q = RingGroupedPublication.state j (site r q) :=
  (presentation r).publications coords (coordinates r coords) q

theorem root_publications (r : Renumbering i j) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) :
    RingGroupedPublication.state i (RingGroupedReport.origin i a) =
      RingGroupedPublication.state j (RingGroupedReport.origin j (r.atoms a)) := by
  have origin : site r (RingGroupedReport.origin i a) = RingGroupedReport.origin j (r.atoms a) :=
    RingGroupedReport.origin_unique _ rfl
  exact origin ▸ publications r coords (RingGroupedReport.origin i a)

/-- Change the identifier of a report row. Every emitted identifier is in range. -/
def renameRow (r : Renumbering i j) (row : Nat × Option RingNestedActivePair.Labels) :=
  (if h : row.1 < i.certified.certified.input.molecule.atomCount then (r.atoms ⟨row.1,h⟩).val else row.1, row.2)

@[simp] theorem renameRow_toAtomMap (r : Renumbering i j)
    (row : Nat × Option RingNestedActivePair.Labels) :
    AtomMap.renameRow (r : AtomMap i j) row = renameRow r row := rfl

/-- The complete selected report retains its query order and all assigned/refused values.
The returned atom identifiers use the target numbering. -/
theorem report (r : Renumbering i j) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) :
    RingGroupedReport.forAtoms? j (atoms.map r.atoms) =
      (RingGroupedReport.forAtoms? i atoms).map (List.map (renameRow r)) := by
  induction atoms with
  | nil => rfl
  | cons a rest ih =>
    simp only [RingGroupedReport.forAtoms?,List.map_cons,List.mapM_cons]
    change (do let v ← (RingGroupedPublication.state j (RingGroupedReport.origin j (r.atoms a))).map
                    (fun l => ((r.atoms a).val,l))
               let vs ← RingGroupedReport.forAtoms? j (rest.map r.atoms)
               pure (v :: vs)) = Option.map _ (do
                 let v ← (RingGroupedPublication.state i (RingGroupedReport.origin i a)).map (fun l => (a.val,l))
                 let vs ← RingGroupedReport.forAtoms? i rest
                 pure (v :: vs))
    rw [← root_publications r coords,ih]
    cases RingGroupedPublication.state i (RingGroupedReport.origin i a) <;>
      cases RingGroupedReport.forAtoms? i rest <;> simp [renameRow,a.isLt]


theorem centres_perm (r : Renumbering i j) :
    ((RingGroupedReport.centres i).map r.atoms).Perm (RingGroupedReport.centres j) := by
  have sorted (m : Input) : RingGroupedReport.centres m = m.certified.tetrahedralCenterSet.sort (· ≤ ·) := by
    simp [RingGroupedReport.centres, canonicalTetrahedralCenters, List.map_map,Function.comp_def]
  rw [sorted,sorted]
  apply (List.perm_ext_iff_of_nodup ((Finset.sort_nodup _ _).map r.atoms.injective)
    (Finset.sort_nodup _ _)).mpr
  intro b
  simp only [List.mem_map,Finset.mem_sort]
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (AtomMap.center r.toAtomMap ⟨a,ha⟩).property
  · intro hb
    exact ⟨r.atoms.symm b,(AtomMap.center r.symm.toAtomMap ⟨b,hb⟩).property,r.atoms.apply_symm_apply _⟩

private def rendered (i : Input) (a : i.certified.Atom) :=
  (a.val, (RingGroupedPublication.state i (RingGroupedReport.origin i a)).getD none)

private theorem rendered_report (i : Input) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (xs : List i.certified.Atom) : RingGroupedReport.forAtoms? i xs = some (xs.map (rendered i)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp
      (RingGroupedPublication.complete (RingGroupedGeometry.physical coords) (RingGroupedReport.origin i a))
    simp only [RingGroupedReport.forAtoms?,List.mapM_cons,List.map_cons]
    change (do let v ← (RingGroupedPublication.state i (RingGroupedReport.origin i a)).map (fun l => (a.val,l))
               let vs ← RingGroupedReport.forAtoms? i xs
               pure (v :: vs)) = _
    simp [hv,ih,rendered]

/-- Both full centre inventories are computed separately in atom-number order. Relabeling
the source report gives exactly the target rows, with their multiplicities. -/
theorem full_report (r : Renumbering i j) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    ∃ left right, RingGroupedReport.report? i = some left ∧ RingGroupedReport.report? j = some right ∧
      (left.map (renameRow r)).Perm right := by
  refine ⟨_,_,rendered_report i coords _,rendered_report j (coordinates r coords) _,?_⟩
  have entry (a : i.certified.Atom) : renameRow r (rendered i a) = rendered j (r.atoms a) := by
    simp [rendered,renameRow,root_publications r coords a]
  simpa only [List.map_map,Function.comp_def,entry] using (centres_perm r).map (rendered j)


end
end TetraStereo.Engine.RingRawRenumbering
assert_kernel_only TetraStereo.Engine.RingRawRenumbering.visible
assert_kernel_only TetraStereo.Engine.RingRawRenumbering.publications
assert_kernel_only TetraStereo.Engine.RingRawRenumbering.report
assert_kernel_only TetraStereo.Engine.RingRawRenumbering.find_complete
assert_kernel_only TetraStereo.Engine.RingRawRenumbering.full_report
