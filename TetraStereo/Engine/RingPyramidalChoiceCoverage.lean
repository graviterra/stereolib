import TetraStereo.Engine.RingPyramidalChoices

set_option autoImplicit false

/-! Coverage of `RingPyramidalChoices.sites` and representation of independent choices.

* `site_of_eligible`: on certified completion output, every original eligible phosphorus with one
  missing hydrogen, two distinct written neighbours and noncollinear present coordinates has a
  selected site. Nothing is assumed about `draft?`, `offset?` or the `Valid` gate; the row of the
  appended hydrogen comes from `addedParents` ownership and `Certified.added_rows`.
* `variants_represent`: every Boolean assignment over the selected sites is realised by one member
  of `variants`. -/
namespace TetraStereo.Engine.RingPyramidalChoices

open OneCenter
open RingHydrogenCompletion

/-! ## Ownership of the appended hydrogen -/

/-- A listed parent has a first occurrence, and that row names it. -/
theorem offset?_of_mem {l : List Nat} {p : Nat} (h : p ∈ l) :
    ∃ t, offset? l p = some t ∧ l[t]? = some p := by
  induction l with
  | nil => cases h
  | cons q rest ih =>
    by_cases same : q = p
    · refine ⟨0, ?_, ?_⟩
      · show (if q = p then some 0 else (offset? rest p).map (· + 1)) = some 0
        exact if_pos same
      · rw [List.getElem?_cons_zero, same]
    · have inRest : p ∈ rest := by
        rcases List.mem_cons.mp h with e | r
        · exact absurd e.symm same
        · exact r
      obtain ⟨t, ht, row⟩ := ih inRest
      refine ⟨t + 1, ?_, ?_⟩
      · show (if q = p then some 0 else (offset? rest p).map (· + 1)) = some (t + 1)
        rw [if_neg same, ht, Option.map_some]
      · rw [List.getElem?_cons_succ]
        exact row

/-- An original atom with one missing hydrogen owns a row of `addedParents`. -/
theorem mem_addedParents_of_missing_one {m : RawMolecule} {p : Nat} (hp : p < m.atomCount)
    (hmiss : missing m p = 1) : p ∈ addedParents m := by
  have planned : (p, 1) ∈ plan m := by
    unfold plan
    refine List.mem_filterMap.mpr ⟨p, List.mem_range.mpr hp, ?_⟩
    show (if missing m p = 0 then none else some (p, missing m p)) = some (p, 1)
    rw [hmiss, if_neg Nat.one_ne_zero]
  have own : p ∈ List.replicate 1 p := List.mem_replicate.mpr ⟨Nat.one_ne_zero, rfl⟩
  unfold addedParents
  exact List.mem_flatMap.mpr ⟨(p, 1), planned, own⟩

/-- The certificate fixes the number of appended rows. -/
theorem addedParents_length {m out : RawMolecule} {g pos : SpatialConfiguration}
    (cert : Certified m g out pos) :
    (addedParents m).length = out.atomCount - m.atomCount := by
  have e := congrArg List.length cert.added_rows
  rw [List.length_map, List.length_map, List.length_range] at e
  exact e.symm

/-! ## Coverage -/

section Coverage

variable {m out : RawMolecule} {g pos : SpatialConfiguration} {p i j : Nat} {c q1 q2 : Point}

theorem draft?_eq_some {t : Nat} (hn : m.writtenNeighbors p = [i, j])
    (ht : offset? (addedParents m) p = some t) (hc : g.positions[p]? = some c)
    (h1 : g.positions[i]? = some q1) (h2 : g.positions[j]? = some q2) :
    draft? m g p = some ⟨p, m.atomCount + t, i, j, c, q1, q2⟩ := by
  simp only [draft?, hn, ht, hc, h1, h2]

theorem valid_of_row (cert : Certified m g out pos) (hp : p < m.atomCount)
    (helig : (m.atoms[p]?).map eligibleAtom = some true) (hmiss : missing m p = 1)
    (hn : m.writtenNeighbors p = [i, j]) (hne : i ≠ j)
    (hc : g.positions[p]? = some c) (h1 : g.positions[i]? = some q1)
    (h2 : g.positions[j]? = some q2)
    (hnormal : vcross (vsub q1 c) (vsub q2 c) ≠ zeroVector)
    {t : Nat} (row : (addedParents m)[t]? = some p) :
    Valid m g out pos p ⟨p, m.atomCount + t, i, j, c, q1, q2⟩ := by
  obtain ⟨ilt, _⟩ := List.getElem?_eq_some_iff.mp h1
  obtain ⟨jlt, _⟩ := List.getElem?_eq_some_iff.mp h2
  rw [cert.input_positions] at ilt jlt
  obtain ⟨tlt, _⟩ := List.getElem?_eq_some_iff.mp row
  rw [addedParents_length cert] at tlt
  have le := cert.atomCount_le
  have hlt : m.atomCount + t < out.atomCount := by omega
  have hlen : m.atomCount + t < pos.positions.length := by
    rw [cert.positions_length]
    exact hlt
  have row' : (addedParents m)[m.atomCount + t - m.atomCount]? = some p := by
    rw [Nat.add_sub_cancel_left]
    exact row
  obtain ⟨p', found, rowOut⟩ := cert.fresh_row (Nat.le_add_right m.atomCount t) hlt
  rw [row'] at found
  have same : p = p' := Option.some.inj found
  rw [← same] at rowOut
  unfold Valid
  exact ⟨rfl, helig, hmiss, hn, hne, hc, h1, h2, Nat.le_add_right m.atomCount t, row', rowOut,
    hlen, hnormal, hp, ilt, jlt⟩

theorem site?_of_draft {s : Site} (hd : draft? m g p = some s) (v : Valid m g out pos p s) :
    site? m g out pos p = some s := by
  unfold site?
  rw [if_pos v.2.1,hd]
  show admit m g out pos p s = some s
  unfold admit
  exact if_pos v

/-- Coverage: every original eligible phosphorus with one missing hydrogen, exactly two distinct
written neighbours and present noncollinear coordinates is selected, with its retained frame. -/
theorem site_of_eligible (cert : Certified m g out pos) (hp : p < m.atomCount)
    (helig : (m.atoms[p]?).map eligibleAtom = some true) (hmiss : missing m p = 1)
    (hn : m.writtenNeighbors p = [i, j]) (hne : i ≠ j)
    (hc : g.positions[p]? = some c) (h1 : g.positions[i]? = some q1)
    (h2 : g.positions[j]? = some q2)
    (hnormal : vcross (vsub q1 c) (vsub q2 c) ≠ zeroVector) :
    ∃ s, s ∈ sites m g out pos ∧ s.parent = p ∧ s.first = i ∧ s.second = j ∧
      s.center = c ∧ s.firstPoint = q1 ∧ s.secondPoint = q2 := by
  obtain ⟨t, ht, row⟩ := offset?_of_mem (mem_addedParents_of_missing_one hp hmiss)
  have hd := draft?_eq_some (m := m) (g := g) hn ht hc h1 h2
  have valid := valid_of_row cert hp helig hmiss hn hne hc h1 h2 hnormal row
  have selected := site?_of_draft hd valid
  have member : (⟨p, m.atomCount + t, i, j, c, q1, q2⟩ : Site) ∈ sites m g out pos := by
    unfold sites
    exact List.mem_filterMap.mpr ⟨p, List.mem_range.mpr hp, selected⟩
  exact ⟨_, member, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The same coverage with eligibility stated on the atom record. -/
theorem site_of_phosphorus (cert : Certified m g out pos) (hp : p < m.atomCount)
    {a : AtomSpec} (ha : m.atoms[p]? = some a) (element : a.element = Element.P)
    (charge : a.charge = 0) (aromatic : a.aromatic = false) (hmiss : missing m p = 1)
    (hn : m.writtenNeighbors p = [i, j]) (hne : i ≠ j)
    (hc : g.positions[p]? = some c) (h1 : g.positions[i]? = some q1)
    (h2 : g.positions[j]? = some q2)
    (hnormal : vcross (vsub q1 c) (vsub q2 c) ≠ zeroVector) :
    ∃ s, s ∈ sites m g out pos ∧ s.parent = p ∧ s.first = i ∧ s.second = j ∧
      s.center = c ∧ s.firstPoint = q1 ∧ s.secondPoint = q2 := by
  have e : eligibleAtom a = true := decide_eq_true ⟨Or.inl element, charge, aromatic⟩
  have helig : (m.atoms[p]?).map eligibleAtom = some true := by
    rw [ha, Option.map_some, e]
  exact site_of_eligible cert hp helig hmiss hn hne hc h1 h2 hnormal

/-- Neutral nonaromatic arsenic shares the same omitted-H two-hand coverage. -/
theorem site_of_arsenic_or_antimony (cert : Certified m g out pos) (hp : p < m.atomCount)
    {a : AtomSpec} (ha : m.atoms[p]? = some a) (element : a.element = Element.As ∨ a.element = Element.Sb)
    (charge : a.charge = 0) (aromatic : a.aromatic = false) (hmiss : missing m p = 1)
    (hn : m.writtenNeighbors p = [i, j]) (hne : i ≠ j)
    (hc : g.positions[p]? = some c) (h1 : g.positions[i]? = some q1)
    (h2 : g.positions[j]? = some q2)
    (hnormal : vcross (vsub q1 c) (vsub q2 c) ≠ zeroVector) :
    ∃ s, s ∈ sites m g out pos ∧ s.parent = p ∧ s.first = i ∧ s.second = j ∧
      s.center = c ∧ s.firstPoint = q1 ∧ s.secondPoint = q2 := by
  have e : eligibleAtom a = true := decide_eq_true ⟨Or.inr element, charge, aromatic⟩
  have helig : (m.atoms[p]?).map eligibleAtom = some true := by
    rw [ha, Option.map_some, e]
  exact site_of_eligible cert hp helig hmiss hn hne hc h1 h2 hnormal

theorem site_of_arsenic (cert : Certified m g out pos) (hp : p < m.atomCount)
    {a : AtomSpec} (ha : m.atoms[p]? = some a) (element : a.element = Element.As)
    (charge : a.charge = 0) (aromatic : a.aromatic = false) (hmiss : missing m p = 1)
    (hn : m.writtenNeighbors p = [i, j]) (hne : i ≠ j)
    (hc : g.positions[p]? = some c) (h1 : g.positions[i]? = some q1)
    (h2 : g.positions[j]? = some q2)
    (hnormal : vcross (vsub q1 c) (vsub q2 c) ≠ zeroVector) :
    ∃ s, s ∈ sites m g out pos ∧ s.parent = p ∧ s.first = i ∧ s.second = j ∧
      s.center = c ∧ s.firstPoint = q1 ∧ s.secondPoint = q2 := by
  exact site_of_arsenic_or_antimony cert hp ha (Or.inl element) charge aromatic hmiss hn hne hc h1 h2 hnormal

end Coverage

/-! ## Independent choices -/

/-- The completion a Boolean assignment asks for at a site: upper for `true`. -/
def pick (choice : Site → Bool) (s : Site) : Point :=
  if choice s = true then s.plus else s.minus

theorem pick_pos {choice : Site → Bool} {s : Site} (h : choice s = true) :
    pick choice s = s.plus := by
  unfold pick
  exact if_pos h

theorem pick_neg {choice : Site → Bool} {s : Site} (h : ¬ choice s = true) :
    pick choice s = s.minus := by
  unfold pick
  exact if_neg h

/-- Any assignment over sites with distinct in-range hydrogens is one member of `choices`. -/
theorem choices_represent (ss : List Site) (base : List Point) (choice : Site → Bool)
    (distinct : ss.Pairwise fun a b => a.hydrogen ≠ b.hydrogen)
    (bound : ∀ s ∈ ss, s.hydrogen < base.length) :
    ∃ ps, ps ∈ choices ss base ∧ ∀ s ∈ ss, ps[s.hydrogen]? = some (pick choice s) := by
  induction ss generalizing base with
  | nil =>
    refine ⟨base, List.mem_singleton.mpr rfl, ?_⟩
    intro s hs
    cases hs
  | cons t rest ih =>
    obtain ⟨apart, later⟩ := List.pairwise_cons.mp distinct
    have boundHead : t.hydrogen < base.length := bound t (List.mem_cons.mpr (Or.inl rfl))
    have boundRest : ∀ s ∈ rest, s.hydrogen < (base.set t.hydrogen (pick choice t)).length := by
      intro s hs
      rw [List.length_set]
      exact bound s (List.mem_cons.mpr (Or.inr hs))
    obtain ⟨ps, hps, spec⟩ := ih (base.set t.hydrogen (pick choice t)) later boundRest
    have clear : ∀ u ∈ rest, u.hydrogen ≠ t.hydrogen := fun u hu => (apart u hu).symm
    have head : ps[t.hydrogen]? = some (pick choice t) := by
      rw [choices_getElem?_of_not_site hps (k := t.hydrogen) clear]
      exact List.getElem?_set_self boundHead
    have member : ps ∈ choices (t :: rest) base := by
      show ps ∈ choices rest (base.set t.hydrogen t.plus) ++
        choices rest (base.set t.hydrogen t.minus)
      by_cases up : choice t = true
      · rw [pick_pos up] at hps
        exact List.mem_append.mpr (Or.inl hps)
      · rw [pick_neg up] at hps
        exact List.mem_append.mpr (Or.inr hps)
    refine ⟨ps, member, ?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with same | inRest
    · rw [same]
      exact head
    · exact spec s inRest

section Represent

variable {m out : RawMolecule} {g pos : SpatialConfiguration}

/-- Every Boolean assignment over the selected sites is realised simultaneously by one member of
`variants`: each selected hydrogen sits at the completion its own bit asks for. -/
theorem variants_represent (m : RawMolecule) (g : SpatialConfiguration) (out : RawMolecule)
    (pos : SpatialConfiguration) (choice : Site → Bool) :
    ∃ x, x ∈ variants m g out pos ∧
      ∀ s ∈ sites m g out pos, x.positions[s.hydrogen]? = some (pick choice s) := by
  have bound : ∀ s ∈ sites m g out pos, s.hydrogen < pos.positions.length := by
    intro s hs
    obtain ⟨p, _, valid⟩ := sites_valid hs
    exact valid.hydrogen_lt
  obtain ⟨ps, hps, spec⟩ :=
    choices_represent (sites m g out pos) pos.positions choice (sites_pairwise m g out pos) bound
  have member : ({ positions := ps } : SpatialConfiguration) ∈ variants m g out pos := by
    unfold variants
    exact List.mem_map.mpr ⟨ps, hps, rfl⟩
  exact ⟨{ positions := ps }, member, spec⟩

/-- The representing member with the frame sign each bit selects. -/
theorem variants_represent_signed (m : RawMolecule) (g : SpatialConfiguration)
    (out : RawMolecule) (pos : SpatialConfiguration) (choice : Site → Bool) :
    ∃ x, x ∈ variants m g out pos ∧
      ∀ s ∈ sites m g out pos,
        (choice s = true →
          x.positions[s.hydrogen]? = some s.plus ∧
            0 < CartesianPoint3.orientedVolume s.firstPoint s.secondPoint s.plus s.center) ∧
        (choice s = false →
          x.positions[s.hydrogen]? = some s.minus ∧
            CartesianPoint3.orientedVolume s.firstPoint s.secondPoint s.minus s.center < 0) := by
  obtain ⟨x, hx, spec⟩ := variants_represent m g out pos choice
  refine ⟨x, hx, ?_⟩
  intro s hs
  obtain ⟨p, _, valid⟩ := sites_valid hs
  have spot := spec s hs
  refine ⟨?_, ?_⟩
  · intro up
    rw [pick_pos up] at spot
    exact ⟨spot, valid.plus_volume_pos⟩
  · intro down
    have notUp : ¬ choice s = true := by
      rw [down]
      exact Bool.false_ne_true
    rw [pick_neg notUp] at spot
    exact ⟨spot, valid.minus_volume_neg⟩

open CertifiedLocalizedCIPInput RationalTetrahedralPermutation

/-- One member matches every nondegenerate independently supplied P–H position
at once, in every ligand order at every selected phosphorus. -/
theorem variants_represent_positions (m out : RawMolecule) (g pos : SpatialConfiguration)
    (written : Site → Point)
    (nonzero : ∀ s ∈ sites m g out pos,
      CartesianPoint3.orientedVolume s.firstPoint s.secondPoint (written s) s.center ≠ 0) :
    ∃ x ∈ variants m g out pos, ∀ s ∈ sites m g out pos, ∃ h,
      x.positions[s.hydrogen]? = some h ∧ ∀ π : Equiv.Perm (Fin 4),
        descriptorOfOrientedVolume? (permutedOrientedVolume s.firstPoint s.secondPoint h s.center π) =
        descriptorOfOrientedVolume? (permutedOrientedVolume s.firstPoint s.secondPoint (written s) s.center π) := by
  classical
  let agreesAt (s : Site) (h : Point) := ∀ π : Equiv.Perm (Fin 4),
    descriptorOfOrientedVolume? (permutedOrientedVolume s.firstPoint s.secondPoint h s.center π) =
    descriptorOfOrientedVolume? (permutedOrientedVolume s.firstPoint s.secondPoint (written s) s.center π)
  let hand (s : Site) := decide (agreesAt s s.plus)
  obtain ⟨x,hx,placed⟩ := variants_represent m g out pos hand
  refine ⟨x,hx,?_⟩
  intro s hs
  obtain ⟨_,_,valid⟩ := sites_valid hs
  obtain ⟨h,member,equal⟩ := explicit_pyramidal_represented _ _ _ (written s) valid.normal_ne (nonzero s hs)
  refine ⟨_,placed s hs,?_⟩
  change agreesAt s (pick hand s)
  by_cases up : agreesAt s s.plus
  · simp [pick,hand,up]
  · have down : agreesAt s s.minus := by
      rcases List.mem_cons.mp member with rfl | tail
      · exact (up equal).elim
      · have same := List.mem_singleton.mp tail
        subst h
        exact equal
    simpa [pick,hand,up] using down

end Represent

end TetraStereo.Engine.RingPyramidalChoices

assert_kernel_only TetraStereo.Engine.RingPyramidalChoices.site_of_eligible
assert_kernel_only TetraStereo.Engine.RingPyramidalChoices.site_of_arsenic_or_antimony
assert_kernel_only TetraStereo.Engine.RingPyramidalChoices.site_of_phosphorus
assert_kernel_only TetraStereo.Engine.RingPyramidalChoices.variants_represent
assert_kernel_only TetraStereo.Engine.RingPyramidalChoices.variants_represent_signed
assert_kernel_only TetraStereo.Engine.RingPyramidalChoices.variants_represent_positions
