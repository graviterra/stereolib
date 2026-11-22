import TetraStereo.Engine.RingRetainedTerminalClass
import TetraStereo.OneCenter.LocalizedCarrierRealCenterActiveSimple
import TetraStereo.OneCenter.LocalizedParentFrameHistory
import TetraStereo.OneCenter.LocalizedRootBranchAuxiliaryLocality

set_option autoImplicit false

namespace TetraStereo.Engine.RingTerminalReferenceRoles
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingRetainedTerminalClass (Atom Pair)

/-- A class of real, equivalent terminal substituents at one retained carbon.
Its witnesses bind the individual members to their actual original occurrences. -/
structure Group (i : Input) (q : Site i) (f : Atom i) (n : Nat) where
  atom : Fin n → Atom i
  injective : Function.Injective atom
  related : ∀ j k, j < k → Nonempty (Pair i q f (atom j) (atom k))

/-- The existing molecular detector constructs a group with three members. -/
def triple {i q} (c : RingRetainedTerminalClass.Certificate i q) : Group i q c.focus 3 where
  atom := ![c.a,c.b,c.c]
  injective := by
    intro j k eqn
    fin_cases j <;> fin_cases k <;>
      simp_all [c.ab.distinct,c.ac.distinct,c.bc.distinct,Ne.symm c.ab.distinct,Ne.symm c.ac.distinct,Ne.symm c.bc.distinct]
  related := by
    intro j k lt
    fin_cases j <;> fin_cases k <;> first | exact ⟨c.ab⟩ | exact ⟨c.ac⟩ | exact ⟨c.bc⟩ | contradiction

def Collision {i q f n} (g : Group i q f n) {α : Type} (color : Atom i → α) :=
  ∃ j k : Fin n, j ≠ k ∧ color (g.atom j) = color (g.atom k)

/-- A whole-molecule atom-and-bond symmetry permutes this terminal class,
fixes every other atom, preserves all reference roles, and moves a class member. -/
def Stabilizer {i q f n} (g : Group i q f n) {α : Type} (color : Atom i → α) : Prop :=
  ∃ e : Equiv.Perm (Atom i), e ∈ i.molecule.toMoleculeGraph.Aut ∧
    (∀ x, i.molecule.atoms.get (e x) = i.molecule.atoms.get x) ∧
    (∀ x, (∀ j, g.atom j ≠ x) → e x = x) ∧ (∀ j, ∃ k, e (g.atom j) = g.atom k) ∧
    (∀ x, color (e x) = color x) ∧ ∃ j, e (g.atom j) ≠ g.atom j

private theorem oriented {i q f n} {g : Group i q f n} {α : Type} {color : Atom i → α}
    (hit : Collision g color) : ∃ j k, j < k ∧ color (g.atom j) = color (g.atom k) := by
  obtain ⟨j,k,ne,e⟩ := hit
  rcases lt_or_gt_of_ne ne with lt | gt
  · exact ⟨j,k,lt,e⟩
  · exact ⟨k,j,gt,e.symm⟩

theorem stabilizer_iff {i q f n} (g : Group i q f n) {α : Type} (color : Atom i → α) :
    Stabilizer g color ↔ Collision g color := by
  constructor
  · rintro ⟨e,_,_,_,closed,paint,j,moved⟩
    obtain ⟨k,inClass⟩ := closed j
    exact ⟨j,k,fun eqn => moved (eqn ▸ inClass),(paint _).symm.trans (congrArg color inClass)⟩
  · intro hit
    obtain ⟨j,k,lt,same⟩ := oriented hit
    obtain ⟨p⟩ := g.related j k lt
    obtain ⟨specs,aut,paint⟩ := p.exchange color same
    refine ⟨Equiv.swap (g.atom j) (g.atom k),aut,specs,?_,?_,paint,j,?_⟩
    · intro x outside
      exact Equiv.swap_apply_of_ne_of_ne (outside j).symm (outside k).symm
    · intro s
      by_cases h : s = j
      · subst s; exact ⟨k,Equiv.swap_apply_left ..⟩
      by_cases h' : s = k
      · subst s; exact ⟨j,Equiv.swap_apply_right ..⟩
      exact ⟨s,Equiv.swap_apply_of_ne_of_ne (fun eqn => h (g.injective eqn)) (fun eqn => h' (g.injective eqn))⟩
    · simpa only [Equiv.swap_apply_left] using p.distinct.symm

/-- Older and current references retain distinct roles, even when one is absent
or both name the same atom. -/
def roles {β : Type} [DecidableEq β] (older current : Option β) (x : β) :=
  (decide (older = some x),decide (current = some x))

private noncomputable def slot {i q f n} (g : Group i q f n) (reference : Option (Atom i)) : Option (Fin n) :=
  if h : ∃ j, reference = some (g.atom j) then some h.choose else none

private theorem slot_iff {i q f n} (g : Group i q f n) (ref : Option (Atom i)) (j : Fin n) :
    slot g ref = some j ↔ ref = some (g.atom j) := by
  unfold slot
  split
  · rename_i h
    simp only [Option.some.injEq]
    constructor
    · rintro rfl; exact h.choose_spec
    · intro same
      exact g.injective (Option.some.inj (h.choose_spec.symm.trans same))
  · rename_i no
    simp only [reduceCtorEq,false_iff]
    exact fun eqn => no ⟨j,eqn⟩

private theorem relative_roles {i q f n} (g : Group i q f n) (old cur : Option (Atom i)) (j : Fin n) :
    roles (slot g old) (slot g cur) j = roles old cur (g.atom j) := by
  simp only [roles,slot_iff]

private theorem four_colors (old cur : Option (Fin 4)) :
    ∃ j k : Fin 4, j ≠ k ∧ roles old cur j = roles old cur k := by
  revert old cur
  decide +kernel

private theorem three_colors (old cur : Option (Fin 3)) :
    (∃ j k : Fin 3, j ≠ k ∧ roles old cur j = roles old cur k) ↔
      ¬∃ j k : Fin 3, j ≠ k ∧ old = some j ∧ cur = some k := by
  revert old cur
  decide +kernel

/-- Retaining any one older atom alongside the current reference cannot destroy
every terminal exchange in a four-member class. -/
theorem four_stabilizer {i q f} (g : Group i q f 4) (old cur : Option (Atom i)) :
    Stabilizer g (roles old cur) := by
  apply (stabilizer_iff ..).mpr
  obtain ⟨j,k,ne,same⟩ := four_colors (slot g old) (slot g cur)
  exact ⟨j,k,ne,by simpa only [relative_roles] using same⟩

/-- For three exchangeable termini, the class loses every surviving exchange
exactly when the older and current roles name two different members. -/
theorem three_stabilizer {i q f} (g : Group i q f 3) (old cur : Option (Atom i)) :
    Stabilizer g (roles old cur) ↔
      ¬∃ j k : Fin 3, j ≠ k ∧ old = some (g.atom j) ∧ cur = some (g.atom k) := by
  rw [stabilizer_iff]
  simpa only [Collision,relative_roles,slot_iff] using three_colors (slot g old) (slot g cur)

/-- The richer comparison on other ligands is arbitrary. For two chemical
termini, the order may read every atom and isotope observation and every
reference role through any irreflexive comparison. -/
def Higher {i : Input} {α : Type} (f : Atom i) (paint : Atom i → α)
    (interpret : (Nat × Nat × α) → (Nat × Nat × α) → Prop) (other : Atom i → Atom i → Prop)
    (a b : Atom i) :=
  let word (x : Atom i) := ((i.molecule.atoms.get x).element.atomicNumber,(i.molecule.atomMassAt? x).getD 0,paint x)
  if RingTerminalPair.Leaf i.molecule f a ∧ RingTerminalPair.Leaf i.molecule f b then
    interpret (word a) (word b) else other a b

private theorem either_before {α : Type} {p : α → α → Prop} {xs : List α}
    (order : xs.Pairwise p) {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) (ne : a ≠ b) : p a b ∨ p b a := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    obtain ⟨first,tail⟩ := List.pairwise_cons.mp order
    rcases List.mem_cons.mp ha with rfl | ma
    · rcases List.mem_cons.mp hb with rfl | mb
      · exact (ne rfl).elim
      · exact Or.inl (first _ mb)
    rcases List.mem_cons.mp hb with rfl | mb
    · exact Or.inr (first _ ma)
    · exact ih tail ma mb

/-- Whenever a colored terminal exchange survives, neither geometry admits a
strict ligand ranking, for every completion on the remaining comparisons. -/
theorem no_ranking {i q f n} (g : Group i q f n) {α : Type} (paint : Atom i → α)
    (survives : Stabilizer g paint)
    (interpret : (Nat × Nat × α) → (Nat × Nat × α) → Prop) (irrefl : ∀ o, ¬interpret o o)
    (other : Atom i → Atom i → Prop) (order : List (Atom i)) (all : ∀ j, g.atom j ∈ order) :
    ¬ order.Pairwise (Higher f paint interpret other) := by
  obtain ⟨j,k,lt,same⟩ := oriented ((stabilizer_iff ..).mp survives)
  obtain ⟨p⟩ := g.related j k lt
  have e := p.raw.equivalent
  rw [p.leftId,p.rightId] at e
  intro ranked
  rcases either_before ranked (all j) (all k) p.distinct with left | right
  · simp only [Higher,if_pos (And.intro e.2.1 e.2.2.1),e.2.2.2.1,e.2.2.2.2.2,same] at left
    exact irrefl _ left
  · simp only [Higher,if_pos (And.intro e.2.2.1 e.2.1),e.2.2.2.1,e.2.2.2.2.2,same] at right
    exact irrefl _ right

/-- Retaining each older focus and its chosen incident atom allows membership
in the active scope to be checked from the bond graph. -/
abbrev Choice (i : Input) := Atom i × Atom i

def historyRoles {i : Input} (history : List (Choice i)) (current : Option (Atom i)) (x : Atom i) :=
  (history.map (fun choice => decide (choice.2 = x)),decide (current = some x))

theorem Group.terminal {i q f n} (g : Group i q f n) (j k : Fin n) (ne : j ≠ k) :
    RingTerminalPair.Leaf i.molecule f (g.atom j) := by
  rcases lt_or_gt_of_ne ne with h | h
  · obtain ⟨p⟩ := g.related j k h
    have e := p.raw.equivalent
    rw [p.leftId,p.rightId] at e
    exact e.2.1
  · obtain ⟨p⟩ := g.related k j h
    have e := p.raw.equivalent
    rw [p.leftId,p.rightId] at e
    exact e.2.2.1

/-- A mark selected among the neighbors of any other center cannot name a
member of this terminal class. The terminal atom has just one molecular bond. -/
theorem external_choice_misses {i q f n} (g : Group i q f n) {j k : Fin n} (ne : j ≠ k)
    (previous : Choice i) (different : previous.1 ≠ f)
    (incident : i.molecule.toMoleculeGraph.Adj previous.1 previous.2) : previous.2 ≠ g.atom j := by
  intro enters
  have zero := (g.terminal j k ne).2.2 previous.1
  rw [if_neg different] at zero
  have back := i.molecule.toMoleculeGraph.adj_symm.mp incident
  change 0 < i.molecule.toMoleculeGraph.bond previous.2 previous.1 at back
  rw [enters,zero] at back
  exact lt_irrefl _ back

/-- Any number of older marks chosen at other centers leave all three termini
indistinguishable up to the one current role. Their order and multiplicity are
retained explicitly in the observation word. -/
theorem external_history {i q f} (g : Group i q f 3) (history : List (Choice i))
    (current : Option (Atom i)) (source : ∀ e ∈ history,
      e.1 ≠ f ∧ i.molecule.toMoleculeGraph.Adj e.1 e.2) :
    Stabilizer g (historyRoles history current) := by
  have old (j : Fin 3) : history.map (fun e => decide (e.2 = g.atom j)) =
      history.map (fun _ => false) := by
    apply List.map_congr_left
    intro e here
    have another : ∀ j : Fin 3, ∃ k : Fin 3, j ≠ k := by decide
    obtain ⟨k,ne⟩ := another j
    simp [external_choice_misses g ne e (source e here).1 (source e here).2]
  have one : Stabilizer g (roles none current) := (three_stabilizer g none current).mpr (by simp)
  obtain ⟨j,k,ne,same⟩ := (stabilizer_iff ..).mp one
  have curr := congrArg Prod.snd same
  apply (stabilizer_iff ..).mpr
  refine ⟨j,k,ne,?_⟩
  simp only [historyRoles,old]
  exact congrArg (Prod.mk (history.map (fun _ => false))) curr

/-- Proper ancestors of the original real occurrence name different atoms.
The original carrier supplies both the current head and the simple path. -/
theorem ancestor_ne {i : Input} (q : Site i) {f old : Atom i}
    (real : q.val.node.provenance = .realAtom)
    (atFocus : q.val.node.current?.map Fin.val = some f.val)
    (earlier : old.val ∈ q.val.node.history.tail.map Fin.val) : old ≠ f := by
  have simple := (i.certified.localizedCIPOccurrence_activeSimple_of_provenance_real q real).2
  obtain ⟨center,read,ident⟩ := Option.map_eq_some_iff.mp atFocus
  have head := (i.certified.declarativeLocalizedOccurrence_node_history_head_eq_current
    ((i.certified.mem_localizedOccurrences_iff _ q.val).mp q.property)).trans read
  obtain ⟨past,shape⟩ := List.head?_eq_some_iff.mp head
  rw [shape] at simple earlier
  obtain ⟨x,hx,atom⟩ := List.mem_map.mp earlier
  intro same
  have equal : x = center := Fin.ext (atom.trans ((congrArg Fin.val same).trans ident.symm))
  exact (List.nodup_cons.mp simple).1 (equal ▸ hx)

/-- A strict original address prefix puts the earlier focus atom in the
proper tail of the later occurrence's history, even on a cyclic bond graph. -/
theorem atom_in_history_of_prefix {i : Input} (before after : Site i) {atom : Atom i}
    (read : before.val.node.current?.map Fin.val = some atom.val)
    (root : before.val.root = after.val.root) (below : before.val.address <+: after.val.address)
    (proper : before.val.address.length < after.val.address.length) :
    atom.val ∈ after.val.node.history.tail.map Fin.val := by
  obtain ⟨x,hx,id⟩ := Option.map_eq_some_iff.mp read
  have head := (i.certified.declarativeLocalizedOccurrence_node_history_head_eq_current
    ((i.certified.mem_localizedOccurrences_iff _ before.val).mp before.property)).trans hx
  obtain ⟨past,shape⟩ := List.head?_eq_some_iff.mp head
  obtain ⟨steps,route⟩ := i.certified.history_suffix_of_rootBranch before after root below
  have lb := i.certified.carrierOccurrence_history_length_eq_address_succ before
  have la := i.certified.carrierOccurrence_history_length_eq_address_succ after
  cases steps with
  | nil =>
    simp only [List.nil_append] at route
    rw [route] at lb
    omega
  | cons z zs =>
    rw [← route,shape]
    exact List.mem_map.mpr ⟨x,List.mem_append_right _ List.mem_cons_self,id⟩

/-- Direct comparison consequence for any prefix of actual original path ancestors.
Every retained earlier choice was incident at its own focus. Even under two different
coordinate presentations, any completion respecting identical terminal observations
has no strict ranking. -/
theorem ancestor_no_ranking {i q f} (g : Group i q f 3) (history : List (Choice i))
    (current : Option (Atom i)) (real : q.val.node.provenance = .realAtom)
    (atFocus : q.val.node.current?.map Fin.val = some f.val)
    (source : ∀ e ∈ history, e.1.val ∈ q.val.node.history.tail.map Fin.val ∧
      i.molecule.toMoleculeGraph.Adj e.1 e.2)
    (interpret : Bool → (Nat × Nat × (List Bool × Bool)) → (Nat × Nat × (List Bool × Bool)) → Prop)
    (irrefl : ∀ rev o, ¬interpret rev o o) (other : Bool → Atom i → Atom i → Prop) :
    ∀ (rev : Bool) (order : List (Atom i)), (∀ j, g.atom j ∈ order) →
      ¬order.Pairwise (Higher f (historyRoles history current) (interpret rev) (other rev)) := by
  have symmetry := external_history g history current fun e h =>
    ⟨ancestor_ne q real atFocus (source e h).1,(source e h).2⟩
  intro rev order all
  exact no_ranking g _ symmetry (interpret rev) (irrefl rev) (other rev) order all

end TetraStereo.Engine.RingTerminalReferenceRoles

assert_kernel_only TetraStereo.Engine.RingTerminalReferenceRoles.triple
assert_kernel_only TetraStereo.Engine.RingTerminalReferenceRoles.stabilizer_iff
assert_kernel_only TetraStereo.Engine.RingTerminalReferenceRoles.four_stabilizer
assert_kernel_only TetraStereo.Engine.RingTerminalReferenceRoles.three_stabilizer
assert_kernel_only TetraStereo.Engine.RingTerminalReferenceRoles.no_ranking
assert_kernel_only TetraStereo.Engine.RingTerminalReferenceRoles.external_choice_misses
assert_kernel_only TetraStereo.Engine.RingTerminalReferenceRoles.external_history
assert_kernel_only TetraStereo.Engine.RingTerminalReferenceRoles.atom_in_history_of_prefix
assert_kernel_only TetraStereo.Engine.RingTerminalReferenceRoles.ancestor_ne
assert_kernel_only TetraStereo.Engine.RingTerminalReferenceRoles.ancestor_no_ranking
