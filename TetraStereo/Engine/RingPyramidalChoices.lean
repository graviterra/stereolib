import TetraStereo.Engine.RingHydrogenFrame

set_option autoImplicit false

/-! Coordinate variants of a hydrogen-completed graph for P/As/Sb centers whose single omitted
hydrogen leaves the pyramidal hand unwritten.

`RingHydrogenCompletion.single` places the one missing hydrogen of a two-neighbour centre in the
plane of the two retained bonds, so the completed frame is degenerate and carries no hand. Each
such P/As/Sb center has two hand completions. `variants` returns every independent combination; the
completed graph `out` is unchanged and only the appended hydrogen positions move.

Nothing here decides a descriptor. A consumer has to read every member of the family and report
a hand only when the members agree. -/
namespace TetraStereo.Engine.RingPyramidalChoices

open OneCenter
open RingHydrogenCompletion

/-! ## Sites -/

/-- One phosphorus with an unwritten hand, its appended hydrogen and its retained frame. -/
structure Site where
  parent : Nat
  hydrogen : Nat
  first : Nat
  second : Nat
  center : Point
  firstPoint : Point
  secondPoint : Point
  deriving DecidableEq, Repr

namespace Site

def normal (s : Site) : Point :=
  vcross (vsub s.firstPoint s.center) (vsub s.secondPoint s.center)

def plus (s : Site) : Point := pairPlus s.center s.firstPoint s.secondPoint

def minus (s : Site) : Point := pairMinus s.center s.firstPoint s.secondPoint

end Site

/-- Position of the first occurrence of a parent among the added-hydrogen parents. -/
def offset? : List Nat → Nat → Option Nat
  | [], _ => none
  | q :: rest, p => if q = p then some 0 else (offset? rest p).map (· + 1)

def eligibleAtom (a : AtomSpec) : Bool :=
  decide ((a.element = Element.P ∨ a.element = Element.As ∨ a.element = Element.Sb) ∧ a.charge = 0 ∧ a.aromatic = false)

/-- Read a site from the source graph and coordinates, before any admission check. -/
def draft? (m : RawMolecule) (g : SpatialConfiguration) (p : Nat) : Option Site :=
  match m.writtenNeighbors p, offset? (addedParents m) p, g.positions[p]? with
  | [i, j], some t, some c =>
    match g.positions[i]?, g.positions[j]? with
    | some q1, some q2 => some ⟨p, m.atomCount + t, i, j, c, q1, q2⟩
    | _, _ => none
  | _, _, _ => none

/-- Everything a site guarantees, as one decidable statement. -/
def Valid (m : RawMolecule) (g : SpatialConfiguration) (out : RawMolecule)
    (pos : SpatialConfiguration) (p : Nat) (s : Site) : Prop :=
  s.parent = p ∧
  (m.atoms[p]?).map eligibleAtom = some true ∧
  missing m p = 1 ∧
  m.writtenNeighbors p = [s.first, s.second] ∧
  s.first ≠ s.second ∧
  g.positions[p]? = some s.center ∧
  g.positions[s.first]? = some s.firstPoint ∧
  g.positions[s.second]? = some s.secondPoint ∧
  m.atomCount ≤ s.hydrogen ∧
  (addedParents m)[s.hydrogen - m.atomCount]? = some p ∧
  out.writtenNeighbors s.hydrogen = [p] ∧
  s.hydrogen < pos.positions.length ∧
  s.normal ≠ zeroVector ∧
  p < m.atomCount ∧
  s.first < m.atomCount ∧
  s.second < m.atomCount

instance (m : RawMolecule) (g : SpatialConfiguration) (out : RawMolecule)
    (pos : SpatialConfiguration) (p : Nat) (s : Site) : Decidable (Valid m g out pos p s) := by
  unfold Valid
  infer_instance

def admit (m : RawMolecule) (g : SpatialConfiguration) (out : RawMolecule)
    (pos : SpatialConfiguration) (p : Nat) (s : Site) : Option Site :=
  if Valid m g out pos p s then some s else none

def site? (m : RawMolecule) (g : SpatialConfiguration) (out : RawMolecule)
    (pos : SpatialConfiguration) (p : Nat) : Option Site :=
  if (m.atoms[p]?).map eligibleAtom = some true then
    (draft? m g p).bind (admit m g out pos p)
  else none

/-- Eligible neutral P/As atoms in ascending original index. -/
def sites (m : RawMolecule) (g : SpatialConfiguration) (out : RawMolecule)
    (pos : SpatialConfiguration) : List Site :=
  (List.range m.atomCount).filterMap (site? m g out pos)

theorem admit_eq_some {m out : RawMolecule} {g pos : SpatialConfiguration} {p : Nat}
    {s s' : Site} (h : admit m g out pos p s = some s') : s' = s ∧ Valid m g out pos p s := by
  unfold admit at h
  by_cases c : Valid m g out pos p s
  · rw [if_pos c] at h
    exact ⟨(Option.some.inj h).symm, c⟩
  · rw [if_neg c] at h
    cases h

theorem site?_valid {m out : RawMolecule} {g pos : SpatialConfiguration} {p : Nat} {s : Site}
    (h : site? m g out pos p = some s) : Valid m g out pos p s := by
  unfold site? at h
  split at h <;> try contradiction
  obtain ⟨s0, _, passed⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨same, valid⟩ := admit_eq_some passed
  rw [same]
  exact valid

theorem sites_valid {m out : RawMolecule} {g pos : SpatialConfiguration} {s : Site}
    (h : s ∈ sites m g out pos) : ∃ p, site? m g out pos p = some s ∧ Valid m g out pos p s := by
  obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp h
  exact ⟨p, hp, site?_valid hp⟩

namespace Valid

variable {m out : RawMolecule} {g pos : SpatialConfiguration} {p : Nat} {s : Site}

theorem hydrogen_ge (v : Valid m g out pos p s) : m.atomCount ≤ s.hydrogen := by
  obtain ⟨_, _, _, _, _, _, _, _, h, _⟩ := v
  exact h

theorem hydrogen_parent (v : Valid m g out pos p s) :
    (addedParents m)[s.hydrogen - m.atomCount]? = some p := by
  obtain ⟨_, _, _, _, _, _, _, _, _, h, _⟩ := v
  exact h

theorem hydrogen_lt (v : Valid m g out pos p s) : s.hydrogen < pos.positions.length := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h, _⟩ := v
  exact h

theorem normal_ne (v : Valid m g out pos p s) : s.normal ≠ zeroVector := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := v
  exact h

/-- The upper completion is a positive frame of the two retained neighbours and the hydrogen
against the phosphorus. -/
theorem plus_volume_pos (v : Valid m g out pos p s) :
    0 < CartesianPoint3.orientedVolume s.firstPoint s.secondPoint s.plus s.center := by
  show 0 < CartesianPoint3.orientedVolume s.firstPoint s.secondPoint
    (pairPlus s.center s.firstPoint s.secondPoint) s.center
  rw [orientedVolume_pairPlus]
  exact normSq_pos v.normal_ne

/-- The lower completion is the opposite frame. -/
theorem minus_volume_neg (v : Valid m g out pos p s) :
    CartesianPoint3.orientedVolume s.firstPoint s.secondPoint s.minus s.center < 0 := by
  show CartesianPoint3.orientedVolume s.firstPoint s.secondPoint
    (pairMinus s.center s.firstPoint s.secondPoint) s.center < 0
  rw [orientedVolume_pairMinus]
  exact neg_lt_zero.mpr (normSq_pos v.normal_ne)

end Valid

/-- Two sites never share an appended hydrogen. -/
theorem sites_pairwise (m : RawMolecule) (g : SpatialConfiguration) (out : RawMolecule)
    (pos : SpatialConfiguration) :
    (sites m g out pos).Pairwise fun a b => a.hydrogen ≠ b.hydrogen := by
  unfold sites
  refine List.Pairwise.filterMap _ ?_ (List.nodup_range (n := m.atomCount))
  intro p q apart s hs t ht same
  have hs' : site? m g out pos p = some s := hs
  have ht' : site? m g out pos q = some t := ht
  have rowS := (site?_valid hs').hydrogen_parent
  have rowT := (site?_valid ht').hydrogen_parent
  rw [same, rowT] at rowS
  exact apart (Option.some.inj rowS).symm

/-! ## Independent combinations -/

/-- Both completions at every site, the remaining positions untouched. -/
def choices : List Site → List Point → List (List Point)
  | [], base => [base]
  | s :: rest, base =>
      choices rest (base.set s.hydrogen s.plus) ++ choices rest (base.set s.hydrogen s.minus)

theorem choices_length (sites : List Site) (base : List Point) :
    (choices sites base).length = 2 ^ sites.length := by
  induction sites generalizing base with
  | nil => rfl
  | cons s rest ih =>
    show (choices rest (base.set s.hydrogen s.plus) ++
      choices rest (base.set s.hydrogen s.minus)).length = 2 ^ (rest.length + 1)
    rw [List.length_append, ih, ih, Nat.pow_succ, Nat.mul_two]

theorem choices_exists (sites : List Site) (base : List Point) :
    ∃ ps, ps ∈ choices sites base := by
  induction sites generalizing base with
  | nil => exact ⟨base, List.mem_singleton.mpr rfl⟩
  | cons s rest ih =>
    obtain ⟨ps, h⟩ := ih (base.set s.hydrogen s.plus)
    refine ⟨ps, ?_⟩
    show ps ∈ choices rest (base.set s.hydrogen s.plus) ++
      choices rest (base.set s.hydrogen s.minus)
    exact List.mem_append.mpr (Or.inl h)

theorem choices_ne_nil (sites : List Site) (base : List Point) : choices sites base ≠ [] := by
  obtain ⟨ps, h⟩ := choices_exists sites base
  exact List.ne_nil_of_mem h

theorem choices_member_length {sites : List Site} {base ps : List Point}
    (h : ps ∈ choices sites base) : ps.length = base.length := by
  induction sites generalizing base with
  | nil =>
    have h' : ps ∈ [base] := h
    rw [List.mem_singleton.mp h']
  | cons s rest ih =>
    have h' : ps ∈ choices rest (base.set s.hydrogen s.plus) ++
      choices rest (base.set s.hydrogen s.minus) := h
    rcases List.mem_append.mp h' with l | r
    · rw [ih l, List.length_set]
    · rw [ih r, List.length_set]

/-- An index that is no site's hydrogen keeps its position. -/
theorem choices_getElem?_of_not_site {sites : List Site} {base ps : List Point}
    (h : ps ∈ choices sites base) {k : Nat} (hk : ∀ s ∈ sites, s.hydrogen ≠ k) :
    ps[k]? = base[k]? := by
  induction sites generalizing base with
  | nil =>
    have h' : ps ∈ [base] := h
    rw [List.mem_singleton.mp h']
  | cons s rest ih =>
    have h' : ps ∈ choices rest (base.set s.hydrogen s.plus) ++
      choices rest (base.set s.hydrogen s.minus) := h
    have here : s.hydrogen ≠ k := hk s (List.mem_cons.mpr (Or.inl rfl))
    have later : ∀ u ∈ rest, u.hydrogen ≠ k := fun u hu => hk u (List.mem_cons.mpr (Or.inr hu))
    rcases List.mem_append.mp h' with l | r
    · rw [ih l later, List.getElem?_set_ne here]
    · rw [ih r later, List.getElem?_set_ne here]

/-- Every site's hydrogen sits at one of its two completions. -/
theorem choices_getElem?_site {sites : List Site} {base ps : List Point}
    (h : ps ∈ choices sites base)
    (distinct : sites.Pairwise fun a b => a.hydrogen ≠ b.hydrogen)
    {s : Site} (hs : s ∈ sites) (bound : s.hydrogen < base.length) :
    ps[s.hydrogen]? = some s.plus ∨ ps[s.hydrogen]? = some s.minus := by
  induction sites generalizing base with
  | nil => cases hs
  | cons t rest ih =>
    obtain ⟨apart, later⟩ := List.pairwise_cons.mp distinct
    have h' : ps ∈ choices rest (base.set t.hydrogen t.plus) ++
      choices rest (base.set t.hydrogen t.minus) := h
    rcases List.mem_cons.mp hs with same | inRest
    · have bound' : t.hydrogen < base.length := by
        rw [← same]
        exact bound
      have clear : ∀ u ∈ rest, u.hydrogen ≠ t.hydrogen := fun u hu => (apart u hu).symm
      rw [same]
      rcases List.mem_append.mp h' with l | r
      · left
        rw [choices_getElem?_of_not_site l (k := t.hydrogen) clear]
        exact List.getElem?_set_self bound'
      · right
        rw [choices_getElem?_of_not_site r (k := t.hydrogen) clear]
        exact List.getElem?_set_self bound'
    · rcases List.mem_append.mp h' with l | r
      · exact ih l later inRest (by rw [List.length_set]; exact bound)
      · exact ih r later inRest (by rw [List.length_set]; exact bound)

/-! ## The family -/

/-- Every hand completion of the unwritten pyramidal phosphorus atoms. With no such atom the
family is exactly the prepared coordinates. -/
def variants (m : RawMolecule) (g : SpatialConfiguration) (out : RawMolecule)
    (pos : SpatialConfiguration) : List SpatialConfiguration :=
  (choices (sites m g out pos) pos.positions).map fun ps => { positions := ps }

theorem variants_ne_nil (m : RawMolecule) (g : SpatialConfiguration) (out : RawMolecule)
    (pos : SpatialConfiguration) : variants m g out pos ≠ [] := by
  obtain ⟨ps, h⟩ := choices_exists (sites m g out pos) pos.positions
  exact List.ne_nil_of_mem (List.mem_map.mpr ⟨ps, h, rfl⟩)

theorem variants_length (m : RawMolecule) (g : SpatialConfiguration) (out : RawMolecule)
    (pos : SpatialConfiguration) :
    (variants m g out pos).length = 2 ^ (sites m g out pos).length := by
  unfold variants
  rw [List.length_map, choices_length]

theorem variants_of_no_site {m out : RawMolecule} {g pos : SpatialConfiguration}
    (none : sites m g out pos = []) : variants m g out pos = [pos] := by
  unfold variants
  rw [none]
  rfl

section Members

variable {m out : RawMolecule} {g pos x : SpatialConfiguration}

theorem variants_positions_length (hx : x ∈ variants m g out pos) :
    x.positions.length = pos.positions.length := by
  obtain ⟨ps, hps, same⟩ := List.mem_map.mp hx
  rw [← same]
  exact choices_member_length hps

/-- Every index outside the selected hydrogens keeps its prepared position. -/
theorem variants_getElem?_of_not_site (hx : x ∈ variants m g out pos) {k : Nat}
    (hk : ∀ s ∈ sites m g out pos, s.hydrogen ≠ k) :
    x.positions[k]? = pos.positions[k]? := by
  obtain ⟨ps, hps, same⟩ := List.mem_map.mp hx
  rw [← same]
  exact choices_getElem?_of_not_site hps hk

/-- Every original atom keeps its prepared position. -/
theorem variants_original (hx : x ∈ variants m g out pos) {k : Nat} (hk : k < m.atomCount) :
    x.positions[k]? = pos.positions[k]? := by
  apply variants_getElem?_of_not_site hx
  intro s hs same
  obtain ⟨p, _, valid⟩ := sites_valid hs
  have ge := valid.hydrogen_ge
  omega

/-- Every selected hydrogen sits at one of its two completions. -/
theorem variants_site (hx : x ∈ variants m g out pos) {s : Site}
    (hs : s ∈ sites m g out pos) :
    x.positions[s.hydrogen]? = some s.plus ∨ x.positions[s.hydrogen]? = some s.minus := by
  obtain ⟨ps, hps, same⟩ := List.mem_map.mp hx
  obtain ⟨p, _, valid⟩ := sites_valid hs
  rw [← same]
  exact choices_getElem?_site hps (sites_pairwise m g out pos) hs valid.hydrogen_lt

/-- On certified completion output, every member reads the selected phosphorus frame with a
definite sign: positive at the upper completion and negative at the lower one. -/
theorem variants_site_frame (cert : Certified m g out pos) (hx : x ∈ variants m g out pos)
    {s : Site} (hs : s ∈ sites m g out pos) :
    x.positions[s.parent]? = some s.center ∧
    x.positions[s.first]? = some s.firstPoint ∧
    x.positions[s.second]? = some s.secondPoint ∧
    ((x.positions[s.hydrogen]? = some s.plus ∧
        0 < CartesianPoint3.orientedVolume s.firstPoint s.secondPoint s.plus s.center) ∨
      (x.positions[s.hydrogen]? = some s.minus ∧
        CartesianPoint3.orientedVolume s.firstPoint s.secondPoint s.minus s.center < 0)) := by
  obtain ⟨p, _, valid⟩ := sites_valid hs
  have spot := variants_site hx hs
  have up := valid.plus_volume_pos
  have down := valid.minus_volume_neg
  obtain ⟨parent, _, _, _, _, center, first, second, _, _, _, _, _, pLt, firstLt, secondLt⟩ :=
    valid
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [parent, variants_original hx pLt, cert.positions_getElem? pLt]
    exact center
  · rw [variants_original hx firstLt, cert.positions_getElem? firstLt]
    exact first
  · rw [variants_original hx secondLt, cert.positions_getElem? secondLt]
    exact second
  · rcases spot with plus | minus
    · exact Or.inl ⟨plus, up⟩
    · exact Or.inr ⟨minus, down⟩

end Members

end TetraStereo.Engine.RingPyramidalChoices

assert_kernel_only TetraStereo.Engine.RingPyramidalChoices.variants_length
assert_kernel_only TetraStereo.Engine.RingPyramidalChoices.variants_site_frame
