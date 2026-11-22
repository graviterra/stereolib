import TetraStereo.Engine.RingTerminalReferenceRoles
import TetraStereo.Engine.RingRetainedSilentPair
import TetraStereo.OneCenter.LocalizedActualMonocycleFallbackExclusion

set_option autoImplicit false

namespace TetraStereo.Engine.RingPendantReferenceRoles

open OneCenter
open LocalizedChemicalRing (Input)
open RingRetainedTerminalClass (Atom)
open RingTerminalReferenceRoles (Choice historyRoles)
open RingActivePairs (Site Arm)

/-- A side of a molecular cut with exactly one crossing bond. Internal bonds
and the depth of the side are unrestricted. -/
structure Side (i : Input) (gate : Atom i) where
  atoms : Finset (Atom i)
  first : Atom i
  outside : gate ∉ atoms
  inside : first ∈ atoms
  bond : i.molecule.toMoleculeGraph.Adj gate first
  crossing : ∀ x ∉ atoms, ∀ y ∈ atoms, i.molecule.toMoleculeGraph.Adj x y → x = gate ∧ y = first

/-- An exterior focus can enter this side precisely by selecting the first
atom at the attachment. This includes choices made after visiting a focus again. -/
theorem Side.choice_iff {i gate} (s : Side i gate) (c : Choice i)
    (outside : c.1 ∉ s.atoms) (incident : i.molecule.toMoleculeGraph.Adj c.1 c.2) :
    c.2 ∈ s.atoms ↔ c.1 = gate ∧ c.2 = s.first :=
  ⟨fun h => s.crossing _ outside _ h incident,fun h => h.2 ▸ s.inside⟩

def rawAtom {i : Input} (x : i.certified.Atom) : Atom i :=
  ⟨x.val,(LocalizedChemicalRingPhysicalSense.count i.molecule i.certified i.agreement) ▸ x.isLt⟩

private theorem raw_adj {i : Input} {x y : i.certified.Atom} (h : i.certified.moleculeGraph.Adj x y) :
    i.molecule.toMoleculeGraph.Adj (rawAtom x) (rawAtom y) :=
  (LocalizedChemicalRingPhysicalSense.adj_iff i.molecule i.certified i.agreement i.admissible.1.1
    i.admissible.1.2 i.supported x y).mp h

private theorem Side.stays {i gate} (s : Side i gate) {a b : Atom i}
    (ha : a ≠ gate) (hb : b ≠ gate) (h : i.molecule.toMoleculeGraph.Adj a b) :
    a ∈ s.atoms ↔ b ∈ s.atoms := by
  constructor
  · intro ma
    by_contra mb
    exact hb (s.crossing _ mb _ ma (i.molecule.toMoleculeGraph.adj_symm.mp h)).1
  · intro mb
    by_contra ma
    exact ha (s.crossing _ ma _ mb h).1

/-- On a real original-digraph path ending at the attachment, all proper
ancestors are on the root's side of the cut. A path that had entered the
pendant side first would need a second visit to the attachment. -/
theorem Side.ancestor_outside {i gate} (s : Side i gate) (q : Site i)
    (real : q.val.node.provenance = .realAtom) (atGate : q.val.node.current?.map Fin.val = some gate.val)
    (rootOutside : rawAtom q.val.root ∉ s.atoms) {old : Atom i}
    (earlier : old.val ∈ q.val.node.history.tail.map Fin.val) : old ∉ s.atoms := by
  have chain := i.certified.declarativeLocalizedOccurrence_node_history_chain
    ((i.certified.mem_localizedOccurrences_iff _ q.val).mp q.property)
  have last := i.certified.carrierOccurrence_history_getLast_eq_root i.single q
  have noGate (x : i.certified.Atom) (mem : x ∈ q.val.node.history.tail) : rawAtom x ≠ gate :=
    RingTerminalReferenceRoles.ancestor_ne q real atGate (List.mem_map.mpr ⟨x,mem,rfl⟩)
  have same := chain.tail.imp_of_mem_imp (fun x y hx hy h => s.stays (noGate x hx) (noGate y hy) (raw_adj h))
  obtain ⟨v,member,id⟩ := List.mem_map.mp earlier
  have read : rawAtom v = old := Fin.ext id
  rw [← read]
  cases shape : q.val.node.history with
  | nil => simp [shape] at member
  | cons g rest =>
    cases rest with
    | nil => simp [shape] at member
    | cons a rest =>
      simp only [shape,List.tail_cons] at member same
      rw [shape,List.getLast?_cons_cons] at last
      have rootMem : q.val.root ∈ a :: rest := List.mem_of_mem_getLast? (by simpa using last)
      let P := fun (x : i.certified.Atom) => rawAtom x ∈ s.atoms
      have all (z : i.certified.Atom) (hz : z ∈ a :: rest) : P a ↔ P z := by
        rcases List.mem_cons.mp hz with rfl | h
        · rfl
        · exact same.cons_induction (fun x => P a ↔ P x) _ (fun {_ _} edge base => base.trans edge) Iff.rfl z h
      exact fun h => rootOutside ((all _ rootMem).mp ((all _ member).mpr h))

/-- An ordered molecular history is invariant exactly when the permutation
fixes every selected atom and the current selection. Repeat selections, root
revisits and incompatible roles are tested separately. -/
theorem history_iff_fixed {i : Input} (e : Equiv.Perm (Atom i)) (h : List (Choice i))
    (current : Option (Atom i)) :
    (∀ x, historyRoles h current (e x) = historyRoles h current x) ↔
      (∀ c ∈ h, e c.2 = c.2) ∧ (∀ x, current = some x → e x = x) := by
  constructor
  · intro same
    constructor
    · intro c member
      have all := congrArg Prod.fst (same c.2)
      have here := List.map_inj_left.mp all c member
      exact (of_decide_eq_true (here.trans (decide_eq_true rfl))).symm
    · intro x cur
      have found := congrArg Prod.snd (same x)
      change decide (current = some (e x)) = decide (current = some x) at found
      exact Option.some.inj ((of_decide_eq_true (found.trans (decide_eq_true cur))).symm.trans cur)
  · rintro ⟨old,now⟩ x
    apply Prod.ext
    · apply List.map_congr_left
      intro c member
      apply decide_eq_decide.mpr
      exact ⟨fun eqn => e.injective ((old c member).trans eqn),
        fun eqn => (old c member).symm.trans (congrArg e eqn)⟩
    · cases cur : current with
      | none => rfl
      | some y =>
        have fixed := now y cur
        change decide (some y = some (e x)) = decide (some y = some x)
        apply decide_eq_decide.mpr
        exact ⟨fun eqn => congrArg some (e.injective (fixed.trans (Option.some.inj eqn))),
          fun eqn => congrArg some (fixed.symm.trans (congrArg e (Option.some.inj eqn)))⟩

/-- A whole-molecule automorphism which exchanges two disjoint pendant arms
and fixes every atom outside them. Atom records include isotope and charge. -/
structure Exchange {i : Input} {gate : Atom i} (l r : Side i gate) where
  perm : Equiv.Perm (Atom i)
  symmetry : perm ∈ i.molecule.toMoleculeGraph.Aut
  species : ∀ x, i.molecule.atoms.get (perm x) = i.molecule.atoms.get x
  apart : Disjoint l.atoms r.atoms
  sends : ∀ x, x ∈ l.atoms ↔ perm x ∈ r.atoms
  returns : ∀ x, x ∈ r.atoms ↔ perm x ∈ l.atoms
  fixed : ∀ x, x ∉ l.atoms → x ∉ r.atoms → perm x = x

theorem Exchange.moves_first {i gate} {l r : Side i gate} (e : Exchange l r) :
    e.perm l.first = r.first := by
  have g := e.fixed gate l.outside r.outside
  have adj : i.molecule.toMoleculeGraph.Adj (e.perm gate) (e.perm l.first) := by
    change 0 < i.molecule.toMoleculeGraph.bond _ _
    rw [e.symmetry.2.2.2]
    exact l.bond
  rw [g] at adj
  exact (r.crossing gate r.outside _ ((e.sends _).mp l.inside) adj).2

theorem Exchange.fixed_iff {i gate} {l r : Side i gate} (e : Exchange l r) (x : Atom i) :
    e.perm x = x ↔ x ∉ l.atoms ∧ x ∉ r.atoms := by
  constructor
  · intro hx
    have both := Finset.disjoint_left.mp e.apart
    exact ⟨fun hl => both hl (hx ▸ (e.sends _).mp hl),fun hr => both (hx ▸ (e.returns _).mp hr) hr⟩
  · exact fun h => e.fixed x h.1 h.2

/-- All earlier selections are fixed automatically for an outside-rooted
original path. The only possible failure of transport is the current selection
lying inside one of these two arms. -/
theorem Exchange.ancestor_history {i gate} {l r : Side i gate} (e : Exchange l r) (q : Site i)
    (real : q.val.node.provenance = .realAtom) (atGate : q.val.node.current?.map Fin.val = some gate.val)
    (outsideL : rawAtom q.val.root ∉ l.atoms) (outsideR : rawAtom q.val.root ∉ r.atoms)
    (h : List (Choice i)) (current : Option (Atom i)) (source : ∀ c ∈ h,
      c.1.val ∈ q.val.node.history.tail.map Fin.val ∧ i.molecule.toMoleculeGraph.Adj c.1 c.2) :
    (∀ x, historyRoles h current (e.perm x) = historyRoles h current x) ↔
      ∀ x, current = some x → x ∉ l.atoms ∧ x ∉ r.atoms := by
  rw [history_iff_fixed]
  have old (c : Choice i) (here : c ∈ h) := source c here
  have avoid (s : Side i gate) (outside : rawAtom q.val.root ∉ s.atoms)
      (c : Choice i) (here : c ∈ h) : c.2 ∉ s.atoms := by
    obtain ⟨prior,adj⟩ := old c here
    have away := RingTerminalReferenceRoles.ancestor_ne q real atGate prior
    exact fun hi => away ((s.choice_iff c (s.ancestor_outside q real atGate outside prior) adj).mp hi).1
  exact ⟨fun p x hx => (e.fixed_iff x).mp (p.2 x hx),
    fun cur => ⟨fun c mem => e.fixed _ (avoid l outsideL c mem) (avoid r outsideR c mem),
      fun x hx => (e.fixed_iff x).mpr (cur x hx)⟩⟩



def atomObservation {i : Input} (history : List (Choice i)) (current : Option (Atom i)) (x : Atom i) :=
  (i.molecule.atoms.get x,historyRoles history current x)

def endpoint {i : Input} (x : Arm i) := (x.occurrence.val.node.current?.map Fin.val).getD i.molecule.atomCount

def observation {i : Input} {α : Type} (h : List (Choice i)) (current : Option (Atom i))
    (read : Site i → α) (x : Arm i) :=
  (if hx : endpoint x < i.molecule.atomCount then some (atomObservation h current ⟨_,hx⟩) else none,
    read x.occurrence)

/-- A sphere truncation retains the parent/child grouping and multiplicity.
Only permutations of siblings are identified. -/
def Signature (α : Type) : Nat → Type
  | 0 => α
  | n+1 => α × Multiset (Signature α n)

def signature {i : Input} {α : Type} (read : Arm i → α) : (n : Nat) → Arm i → Signature α n
  | 0,a => read a
  | n+1,a => (read a,((i.certified.executableLocalizedRerootChildren a).map (signature read n) : Multiset _))

private theorem map_same {α β : Type} {p : α → α → Prop} {f : α → β} {xs ys : List α}
    (t : List.Forall₂ p xs ys) (h : ∀ a b, p a b → f a = f b) : xs.map f = ys.map f := by
  induction t with
  | nil => rfl
  | cons edge _ ih => exact congrArg₂ List.cons (h _ _ edge) ih

/-- The source's independently matched retained trees give identical branch
signatures at every comparison depth, even deeper than the finite branches. -/
theorem signature_eq_of_matched {i f} (e : RingRetainedSilentPair.Exchange i f) {α : Type}
    (read : Arm i → α) (invariant : ∀ a b, RingRetainedSilentPair.SameSite e a b → read a = read b)
    {n a b} (matched : RingRetainedSilentPair.Matched e n a b) (depth : Nat) :
    signature read depth a = signature read depth b := by
  induction n generalizing a b depth with
  | zero => contradiction
  | succ n ih =>
    obtain ⟨head,ys,perm,below⟩ := matched
    cases depth with
    | zero => exact invariant a b head
    | succ d =>
      apply Prod.ext (invariant a b head)
      apply Multiset.coe_eq_coe.mpr
      rw [map_same below (fun x y rel => ih rel d)]
      exact perm.map _

private theorem observation_eq {i f} (e : RingRetainedSilentPair.Exchange i f) {α : Type}
    (h : List (Choice i)) (current : Option (Atom i)) (read : Site i → α)
    (roles : ∀ x, historyRoles h current (e.swap x) = historyRoles h current x)
    {a b : Arm i} (related : RingRetainedSilentPair.SameSite e a b)
    (labels : read a.occurrence = read b.occurrence) :
    observation h current read a = observation h current read b := by
  obtain ⟨_,_,ha,hb,step,_,_⟩ := related
  change endpoint a < i.molecule.atomCount at ha
  change endpoint b < i.molecule.atomCount at hb
  let x : Atom i := ⟨endpoint a,ha⟩
  let y : Atom i := ⟨endpoint b,hb⟩
  have step' : e.swap x = y := by
    apply Fin.ext
    change (if ht : endpoint a < i.molecule.atomCount then (e.swap ⟨endpoint a,ht⟩).val
      else i.molecule.atomCount) = endpoint b at step
    simpa only [dif_pos ha] using step
  apply Prod.ext _ labels
  simp only [observation,dif_pos ha,dif_pos hb,Option.some.injEq]
  change atomObservation h current x = atomObservation h current y
  rw [← step']
  exact Prod.ext (e.graph.1 x).symm (roles x).symm

/-- A checked pair of actual retained arms stays tied under every irreflexive
reading of the marked branch signatures. Arbitrarily many retained ancestor
choices are permitted. The auxiliary reader is explicitly required to agree
at matched occurrences; each geometry can use its own published observations. -/
theorem no_marked_ranking {i gate} {l r : Side i gate} (e : Exchange l r) (q : Site i)
    (real : q.val.node.provenance = .realAtom) (atGate : q.val.node.current?.map Fin.val = some gate.val)
    (outsideL : rawAtom q.val.root ∉ l.atoms) (outsideR : rawAtom q.val.root ∉ r.atoms)
    (h : List (Choice i)) (current : Option (Atom i)) (source : ∀ c ∈ h,
      c.1.val ∈ q.val.node.history.tail.map Fin.val ∧ i.molecule.toMoleculeGraph.Adj c.1 c.2)
    (away : ∀ x, current = some x → x ∉ l.atoms ∧ x ∉ r.atoms)
    (c : RingRetainedSilentPair.Certificate i q) (aligned : c.exchange.swap = e.perm)
    {α : Type} (read : Bool → Site i → α)
    (published : ∀ rev a b, RingRetainedSilentPair.SameSite c.exchange a b →
      read rev a.occurrence = read rev b.occurrence)
    (rev : Bool) (d : Nat) (strict : Signature (Option (AtomSpec × (List Bool × Bool)) × α) d →
      Signature (Option (AtomSpec × (List Bool × Bool)) × α) d → Prop)
    (irrefl : ∀ v, ¬strict v v) (order : List (Arm i)) (left : c.left ∈ order) (right : c.right ∈ order) :
    ¬order.Pairwise (fun x y => strict (signature (observation h current (read rev)) d x)
      (signature (observation h current (read rev)) d y)) := by
  have roles := (e.ancestor_history q real atGate outsideL outsideR h current source).mpr away
  rw [← aligned] at roles
  let s := signature (observation h current (read rev)) d
  have eqn : s c.left = s c.right := signature_eq_of_matched c.exchange _
    (fun a b rel => observation_eq c.exchange h current _ roles rel (published rev a b rel)) c.full d
  have distinct : c.left ≠ c.right := by
    intro same
    exact c.exchange.distinct
      (c.leftAt.2.symm.trans ((congrArg (fun x : Arm i => endpoint x) same).trans c.rightAt.2))
  intro ranked
  have anyPair : order.Pairwise (fun x y => strict (s x) (s y) ∨ strict (s y) (s x)) :=
    ranked.imp fun h => Or.inl h
  obtain hit | hit := anyPair.forall (fun _ _ z => z.symm) left right distinct
  · exact irrefl _ (eqn ▸ hit)
  · exact irrefl _ (eqn ▸ hit)

end TetraStereo.Engine.RingPendantReferenceRoles

assert_kernel_only TetraStereo.Engine.RingPendantReferenceRoles.Side.ancestor_outside
assert_kernel_only TetraStereo.Engine.RingPendantReferenceRoles.history_iff_fixed
assert_kernel_only TetraStereo.Engine.RingPendantReferenceRoles.Exchange.moves_first
assert_kernel_only TetraStereo.Engine.RingPendantReferenceRoles.Exchange.ancestor_history

assert_kernel_only TetraStereo.Engine.RingPendantReferenceRoles.no_marked_ranking
