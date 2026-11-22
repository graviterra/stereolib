import TetraStereo.Engine.RingTerminalReferenceRoles
import TetraStereo.Engine.RingRetainedChemicalTrace

set_option autoImplicit false

namespace TetraStereo.Engine.RingRetainedProtiumClass
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingRetainedTerminalClass (Atom)
open RingActivePairs (Site Arm)
open RingTerminalReferenceRoles (Choice historyRoles)

/-- Chemical atom observations after interpreting the written isotope notation. -/
def species (s : AtomSpec) := (s.element,s.charge,s.aromatic,s.explicitHydrogens,s.tetrahedral?,
    CIPRule2MassData.rule2MassPico? s.element.atomicNumber s.isotope?)

def Protium (s : AtomSpec) := s.element = .H ∧ s.charge = 0 ∧ s.aromatic = false ∧
  s.explicitHydrogens = 0 ∧ s.tetrahedral? = none ∧ (s.isotope? = none ∨ s.isotope? = some 1)

instance {s} : Decidable (Protium s) := by unfold Protium; infer_instance

theorem protium_same {x y : AtomSpec} (l : Protium x) (r : Protium y) : species x = species y := by
  obtain ⟨lx,lc,la,lh,lt,li⟩ := l
  obtain ⟨rx,rc,ra,rh,rt,ri⟩ := r
  rcases li with li | li <;> rcases ri with ri | ri <;>
    simp only [species,lx,lc,la,lh,lt,li,rx,rc,ra,rh,rt,ri] <;>
    rfl

private def arms (i : Input) (q : Site i) := RingRetainedAuxiliary.frame i.certified q
private def id? {i : Input} (c : Arm i) := c.occurrence.val.node.current?.map Fin.val

structure Leaf (i : Input) (q : Site i) (f : Atom i) where
  atom : Atom i
  raw : RingTerminalPair.Leaf i.molecule f atom
  isotope : Protium (i.molecule.atoms.get atom)
  cursor : Arm i
  incident : cursor ∈ arms i q
  number : id? cursor = some atom.val
  real : cursor.occurrence.val.node.provenance = .realAtom
  terminal : i.certified.executableLocalizedRerootChildren cursor = []

/-- Project the pair onto the actual chemical key used by the retained comparison
engine, including its original provenance, the observed atom record and the Rule 2 mass. -/
theorem Leaf.molecular_key {i q f} (p : Leaf i q f) :
    RingRetainedChemicalTrace.observation? i p.cursor true =
      (CIPRule2MassData.rule2MassPico? 1 (some 1)).map (fun mass => ⟨1,0,mass⟩) := by
  obtain ⟨x,source,atom⟩ := Option.map_eq_some_iff.mp p.number
  have record : i.molecule.atoms[x.val]? = some (i.molecule.atoms.get p.atom) := by
    rw [atom]
    exact List.getElem?_eq_getElem p.atom.isLt
  obtain ⟨element,_,_,_,_,ordinary | labelled⟩ := p.isotope
  all_goals simp only [RingRetainedChemicalTrace.observation?,source,record,p.real,Option.bind_eq_bind,Option.bind_some,
    element,show Element.H.atomicNumber = 1 from rfl,
    RingRetainedChemicalTrace.duplicateValue,Option.elim_none]
  · rw [ordinary,CIPRule2MassData.ordinary_hydrogen_eq_protium]
    rfl
  · rw [labelled]
    rfl

private def leaf? {i : Input} {q : Site i} (f : Atom i) (c : {a // a ∈ arms i q}) : Option (Leaf i q f) := do
  let ⟨x,hx⟩ ← (id? c.val).attach
  if h : x < i.molecule.atomCount then
    let a : Atom i := ⟨x,h⟩
    if ok : Protium (i.molecule.atoms.get a) ∧ RingTerminalPair.Leaf i.molecule f a ∧
        c.val.occurrence.val.node.provenance = .realAtom ∧ i.certified.executableLocalizedRerootChildren c.val = [] then
      return ⟨a,ok.2.1,ok.1,c.val,c.property,hx,ok.2.2.1,ok.2.2.2⟩
  none

structure Certificate (i : Input) (q : Site i) where
  focus : Atom i
  real : q.val.node.provenance = .realAtom
  atFocus : q.val.node.current?.map Fin.val = some focus.val
  ids : List Nat
  frame : (arms i q).mapM id? = some ids
  allAtoms : ids.Perm (i.molecule.ligandsWithLonePair focus.val)
  carbon : RingTerminalPair.Focus i.molecule focus.val
  a : Leaf i q focus
  b : Leaf i q focus
  c : Leaf i q focus
  distinct : a.atom ≠ b.atom ∧ a.atom ≠ c.atom ∧ b.atom ≠ c.atom

/-- Test terminal protium equivalence at the actual occurrence, accepting ordinary
H and explicitly written ¹H in the same class on their normalized Rule 2 mass. -/
def find? (i : Input) (q : Site i) : Option (Certificate i q) := do
  let ⟨x,hx⟩ ← (q.val.node.current?.map Fin.val).attach
  if h : x < i.molecule.atomCount then
    let f : Atom i := ⟨x,h⟩
    let ⟨ns,frame⟩ ← ((arms i q).mapM id?).attach
    if actual : q.val.node.provenance = .realAtom ∧ RingTerminalPair.Focus i.molecule f.val ∧
        ns.Perm (i.molecule.ligandsWithLonePair f.val) then
      match (arms i q).attach.filterMap (leaf? f) with
      | a :: b :: c :: _ =>
        if ne : a.atom ≠ b.atom ∧ a.atom ≠ c.atom ∧ b.atom ≠ c.atom then
          return ⟨f,actual.1,hx,ns,frame,actual.2.2,actual.2.1,a,b,c,ne⟩
        none
      | _ => none
  none

private theorem swap_preserves {α β : Type} [DecidableEq α] {a b : α} (f : α → β) (h : f a = f b) (x : α) :
    f (Equiv.swap a b x) = f x := by
  by_cases ha : x = a
  · subst x; simpa using h.symm
  by_cases hb : x = b
  · subst x; simpa using h
  rw [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- The exchange preserves every normalized atom record and every bond
of the molecular graph, including the ring outside the pendant hydrogens. -/
theorem exchange {i q f} (a b : Leaf i q f) :
    let e := Equiv.swap a.atom b.atom
    (∀ x, species (i.molecule.atoms.get (e x)) = species (i.molecule.atoms.get x)) ∧
    ∀ x y, i.molecule.toMoleculeGraph.bond (e x) (e y) = i.molecule.toMoleculeGraph.bond x y := by
  let G := i.molecule.toMoleculeGraph
  let e := Equiv.swap a.atom b.atom
  have rows (v : Atom i) : G.bond a.atom v = G.bond b.atom v := (a.raw.2.2 v).trans (b.raw.2.2 v).symm
  refine ⟨swap_preserves (fun z => species (i.molecule.atoms.get z)) (protium_same a.isotope b.isotope),?_⟩
  intro x y
  have cols := (G.bond_symm x a.atom).trans ((rows x).trans (G.bond_symm b.atom x))
  exact (swap_preserves (fun t => G.bond t (e y)) (rows (e y)) x).trans (swap_preserves (G.bond x) cols y)

private theorem avoided {i q} (c : Certificate i q) (mark : Option (Atom i)) :
    ∃ a b : Leaf i q c.focus, a.atom ≠ b.atom ∧ mark ≠ some a.atom ∧ mark ≠ some b.atom := by
  by_cases atA : mark = some c.a.atom
  · exact ⟨c.b,c.c,c.distinct.2.2,fun h => c.distinct.1 (Option.some.inj (atA.symm.trans h)),
      fun h => c.distinct.2.1 (Option.some.inj (atA.symm.trans h))⟩
  by_cases atB : mark = some c.b.atom
  · exact ⟨c.a,c.c,c.distinct.2.1,atA,fun h => c.distinct.2.2 (Option.some.inj (atB.symm.trans h))⟩
  exact ⟨c.a,c.b,c.distinct.1,atA,atB⟩

private theorem remote {i q f} (a : Leaf i q f) (choice : Choice i)
    (outside : choice.1 ≠ f) (bond : i.molecule.toMoleculeGraph.Adj choice.1 choice.2) : choice.2 ≠ a.atom := by
  intro same
  have edge := i.molecule.toMoleculeGraph.adj_symm.mp bond
  change 0 < i.molecule.toMoleculeGraph.bond choice.2 choice.1 at edge
  rw [same,a.raw.2.2,if_neg outside] at edge
  exact lt_irrefl _ edge

/-- All older incident marks at different foci and a current mark anywhere still
leave a pair of molecular termini with the exact same normalized data and roles. -/
theorem Certificate.surviving {i q} (c : Certificate i q) (history : List (Choice i)) (mark : Option (Atom i))
    (placed : ∀ e ∈ history, e.1 ≠ c.focus ∧ i.molecule.toMoleculeGraph.Adj e.1 e.2) :
    ∃ a b : Leaf i q c.focus, a.atom ≠ b.atom ∧ historyRoles history mark a.atom = historyRoles history mark b.atom ∧
      (∀ e ∈ history, Equiv.swap a.atom b.atom e.2 = e.2) ∧
      mark.map (Equiv.swap a.atom b.atom) = mark := by
  obtain ⟨a,b,ne,am,bm⟩ := avoided c mark
  have ma (e) (h : e ∈ history) := remote a e (placed e h).1 (placed e h).2
  have mb (e) (h : e ∈ history) := remote b e (placed e h).1 (placed e h).2
  refine ⟨a,b,ne,?_,fun e h => Equiv.swap_apply_of_ne_of_ne (ma e h) (mb e h),?_⟩
  · simp only [historyRoles,decide_eq_false am,decide_eq_false bm,Prod.mk.injEq,and_true]
    apply List.map_congr_left
    intro e h
    simp [ma e h,mb e h]
  · cases mark with
    | none => rfl
    | some m =>
      exact congrArg some (Equiv.swap_apply_of_ne_of_ne (fun h => am (congrArg some h)) (fun h => bm (congrArg some h)))

/-- The remaining ligand priorities on either geometry may be completed arbitrarily.
A comparison of the identical terminal words is never strict. -/
theorem Certificate.no_ranking {i q} (c : Certificate i q) (history : List (Choice i)) (mark : Option (Atom i))
    (placed : ∀ e ∈ history, e.1 ≠ c.focus ∧ i.molecule.toMoleculeGraph.Adj e.1 e.2)
    (rev : Bool) (priority : Bool → Atom i → Atom i → Prop)
    (terminal : ∀ a b : Leaf i q c.focus,
      species (i.molecule.atoms.get a.atom) = species (i.molecule.atoms.get b.atom) →
      historyRoles history mark a.atom = historyRoles history mark b.atom → ¬priority rev a.atom b.atom)
    (order : List (Atom i)) (all : (order.map Fin.val).Perm c.ids) : ¬order.Pairwise (priority rev) := by
  obtain ⟨a,b,ne,roles,_,_⟩ := c.surviving history mark placed
  have member (x : Leaf i q c.focus) : x.atom ∈ order := by
    obtain ⟨v,hv,h⟩ := List.mem_map.mp ((all.trans c.allAtoms).mem_iff.mpr x.raw.1)
    exact Fin.ext h ▸ hv
  intro ranked
  have anyPair : order.Pairwise (fun x y => priority rev x y ∨ priority rev y x) := ranked.imp fun h => Or.inl h
  have pair := anyPair.forall (fun _ _ h => h.symm) (member a) (member b) ne
  exact pair.elim (terminal a b (protium_same a.isotope b.isotope) roles)
    (terminal b a (protium_same b.isotope a.isotope) roles.symm)

/-- At two terminal protium atoms the only remaining observation is their
reference history. The interpretation of distinct histories and all other
branches on each geometry can be chosen independently. -/
def Higher {i : Input} (focus : Atom i) (history : List (Choice i)) (mark : Option (Atom i))
    (prefer : (List Bool × Bool) → (List Bool × Bool) → Prop) (other : Atom i → Atom i → Prop) (a b : Atom i) :=
  if RingTerminalPair.Leaf i.molecule focus a ∧ RingTerminalPair.Leaf i.molecule focus b ∧
      Protium (i.molecule.atoms.get a) ∧ Protium (i.molecule.atoms.get b) then
    prefer (historyRoles history mark a) (historyRoles history mark b) else other a b

theorem Certificate.no_completed_order {i q} (c : Certificate i q) (history : List (Choice i)) (mark : Option (Atom i))
    (placed : ∀ e ∈ history, e.1 ≠ c.focus ∧ i.molecule.toMoleculeGraph.Adj e.1 e.2)
    (prefer : Bool → (List Bool × Bool) → (List Bool × Bool) → Prop) (irrefl : ∀ rev x, ¬prefer rev x x)
    (other : Bool → Atom i → Atom i → Prop) (rev : Bool) (order : List (Atom i)) (all : (order.map Fin.val).Perm c.ids) :
    ¬order.Pairwise (Higher c.focus history mark (prefer rev) (other rev)) := by
  apply c.no_ranking history mark placed rev (fun b => Higher c.focus history mark (prefer b) (other b)) _ order all
  intro a b _ roles
  simp only [Higher,if_pos (And.intro a.raw (And.intro b.raw (And.intro a.isotope b.isotope))),roles]
  exact irrefl _ _

end TetraStereo.Engine.RingRetainedProtiumClass
assert_kernel_only TetraStereo.Engine.RingRetainedProtiumClass.protium_same
assert_kernel_only TetraStereo.Engine.RingRetainedProtiumClass.Leaf.molecular_key
assert_kernel_only TetraStereo.Engine.RingRetainedProtiumClass.find?
assert_kernel_only TetraStereo.Engine.RingRetainedProtiumClass.exchange
assert_kernel_only TetraStereo.Engine.RingRetainedProtiumClass.Certificate.surviving
assert_kernel_only TetraStereo.Engine.RingRetainedProtiumClass.Certificate.no_ranking
assert_kernel_only TetraStereo.Engine.RingRetainedProtiumClass.Certificate.no_completed_order
