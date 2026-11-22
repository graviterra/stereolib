import TetraStereo.Engine.RingCursorTie

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.CursorMass
open OneCenter CertifiedLocalizedCIPInput IsotopePriority

/-- Earlier rules see molecular constitution and the original ring-duplicate
origin. Real nodes retain no spurious priority from their history lengths. -/
def prior? (m : RawMolecule) (p : List Nat) (c : CanonicalRerootCursor) :
    Option (PriorObservation × AtomSpec) := do
  let obs ← observation? m p c
  let a ← m.atoms[c.node.atom]?
  return (DuplicatePriority.originalView obs,massIndependentAtom a)

def mass? (m : RawMolecule) (c : CanonicalRerootCursor) : Option Nat := do
  let a ← m.atoms[c.node.atom]?
  CIPRule2MassData.rule2MassPico? a.element.atomicNumber a.isotope?

theorem mass?_source {m c mass} (measured : mass? m c = some mass) :
    ∃ a, m.atoms[c.node.atom]? = some a ∧
      CIPRule2MassData.rule2MassPico? a.element.atomicNumber a.isotope? = some mass := by
  cases h : m.atoms[c.node.atom]? with
  | none => simp [mass?,h] at measured
  | some a => exact ⟨a,rfl,by simpa [mass?,h] using measured⟩

/-- One proximal mass difference on earlier-rule-equivalent real branches.
One of the two has the original predecessor as its first occurrence. -/
structure Split (m : RawMolecule) (p : List Nat) where
  focus : RawMolecule.CanonicalBranchNode
  reached : occurrence? m p = some focus
  heavy : CanonicalRerootCursor
  light : CanonicalRerootCursor
  heavyAt : heavy ∈ occurrenceLigandCursors m focus
  lightAt : light ∈ occurrenceLigandCursors m focus
  different : heavy.node.atom ≠ light.node.atom
  incoming : canonicalOriginalParent? focus = some heavy.node ∨ canonicalOriginalParent? focus = some light.node
  heavyReal : heavy.node.provenance = .realAtom
  lightReal : light.node.provenance = .realAtom
  matched : TreesMatch m (prior? m p) (budget m+1) heavy light
  heavyMass : Nat
  lightMass : Nat
  heavyRead : mass? m heavy = some heavyMass
  lightRead : mass? m light = some lightMass
  higher : lightMass < heavyMass

theorem Split.source_masses {m p} (s : Split m p) :
    ∃ a b, m.atoms[s.heavy.node.atom]? = some a ∧ m.atoms[s.light.node.atom]? = some b ∧
      CIPRule2MassData.rule2MassPico? a.element.atomicNumber a.isotope? = some s.heavyMass ∧
      CIPRule2MassData.rule2MassPico? b.element.atomicNumber b.isotope? = some s.lightMass ∧
      s.lightMass < s.heavyMass := by
  obtain ⟨a,ha,ma⟩ := mass?_source s.heavyRead
  obtain ⟨b,hb,mb⟩ := mass?_source s.lightRead
  exact ⟨a,b,ha,hb,ma,mb,s.higher⟩

private def before {m p} (s : Split m p) (depth i j : Nat) : Bool :=
  if i = s.heavy.node.atom ∧ j = s.light.node.atom then true
  else if j = s.heavy.node.atom ∧ i = s.light.node.atom then false
  else match ligandRows? m p i depth, ligandRows? m p j depth with
    | some x,some y => decide (y < x)
    | _,_ => false

/-- Every incident ligand occurs exactly once. Each of the six comparisons
comes either from strict Rule 1a keys or the one witnessed proximal mass split. -/
structure Ranking (m : RawMolecule) (p : List Nat) (depth : Nat) where
  domain : saturatedWithHalogens m = true
  split : Split m p
  carbon : (m.atoms[split.focus.atom]?).any (fun a => a.element == .C) = true
  order : List Nat
  complete : order.Perm ((occurrenceLigandCursors m split.focus).map (·.node.atom))
  four : order.length = 4
  unique : order.Nodup
  strict : order.Pairwise fun i j => before split depth i j = true

theorem Ranking.priority {m p depth} (r : Ranking m p depth) :
    r.order.Pairwise fun i j => (i = r.split.heavy.node.atom ∧ j = r.split.light.node.atom) ∨
      (∃ x y, ligandRows? m p i depth = some x ∧ ligandRows? m p j depth = some y ∧ y < x) := by
  apply r.strict.imp
  intro i j h
  by_cases yes : i = r.split.heavy.node.atom ∧ j = r.split.light.node.atom
  · exact Or.inl yes
  · right
    by_cases neg : j = r.split.heavy.node.atom ∧ i = r.split.light.node.atom
    · simp only [before,if_neg yes,if_pos neg,Bool.false_eq_true] at h
    · cases hx : ligandRows? m p i depth <;> cases hy : ligandRows? m p j depth <;>
        simp_all [before]

private def make? {m p} (s : Split m p) (depth : Nat) : Option (Ranking m p depth) := do
  let ids := (occurrenceLigandCursors m s.focus).map (·.node.atom)
  if domain : saturatedWithHalogens m = true then
    if carbon : (m.atoms[s.focus.atom]?).any (fun a => a.element == .C) = true then
      return ← ids.permutations'.findSome? fun order => do
        if h : order.Perm ids ∧ order.length = 4 ∧ order.Nodup ∧ order.Pairwise (fun i j => before s depth i j = true) then
          return ⟨domain,s,carbon,order,h.1,h.2.1,h.2.2.1,h.2.2.2⟩
        none
  none

def rank? (m : RawMolecule) (p : List Nat) (depth : Nat) : Option (Ranking m p depth) := do
  let ⟨focus,reached⟩ ← (occurrence? m p).attach
  let cs := occurrenceLigandCursors m focus
  let parent ← canonicalOriginalParent? focus
  guard (cs.length == 4)
  cs.attach.findSome? fun heavy => cs.attach.findSome? fun light => do
    guard (parent == heavy.val.node || parent == light.val.node)
    if guardPair : heavy.val.node.atom ≠ light.val.node.atom ∧ heavy.val.node.provenance = .realAtom ∧ light.val.node.provenance = .realAtom then
      let ⟨hm,hheavy⟩ ← (mass? m heavy.val).attach
      let ⟨lm,hlight⟩ ← (mass? m light.val).attach
      if senior : lm < hm then
        if inc : canonicalOriginalParent? focus = some heavy.val.node ∨ canonicalOriginalParent? focus = some light.val.node then
          if matchPrior : treesMatch m (prior? m p) (budget m+1) heavy.val light.val = true then
            return ← make? ⟨focus,reached,heavy.val,light.val,heavy.property,light.property,guardPair.1,inc,
              guardPair.2.1,guardPair.2.2,treesMatch_sound matchPrior,hm,lm,hheavy,hlight,senior⟩ depth
    none

end TetraStereo.Engine.RingChemicalPriority.CursorMass

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.CursorMass.Split.source_masses
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.CursorMass.Ranking.priority
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.CursorMass.rank?
