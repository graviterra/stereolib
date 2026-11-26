import TetraStereo.Engine.RingBranchSymmetry
import TetraStereo.Engine.RingConstitutionalHand

/-! A deuterated 1-bromo-1-fluorocyclopropane ring. All eight spellings retain
deuterium and vary which ordinary hydrogens are written at the two ring carbons. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings
open OneCenter OrdinaryHydrogenSpellings OrdinaryHydrogenSpellings.Production
open CertifiedLocalizedCIPInput RingRawRenumbering LocalizedGenericMarkedRecalculation
open RingPyramidalChoices RingWrittenPHReadings RingSpatialTransport
open RingNumberedHydrogenGeometry RingHydrogenCompletion
open LocalizedChemicalRing (Input)
open RingNestedActivePair (Labels)

def chosen (mask : Fin 8) : List Nat := (List.range 3).filter fun j => mask.val.testBit j

def coreAtoms : List AtomSpec :=
  ([.C,.C,.C,.Br,.F] : List Element).map AtomSpec.aliphatic ++
    [{AtomSpec.aliphatic .H with isotope? := some 2}]

def source (mask : Fin 8) : RawMolecule := {
  atoms := coreAtoms ++ List.replicate (chosen mask).length (.aliphatic .H)
  bonds := ([(0,1),(0,2),(0,3),(0,4),(1,2),(1,5)] : List (Nat × Nat)).map (fun ab => ⟨ab.1,ab.2,.single⟩) ++
    (chosen mask).zipIdx.map (fun jk => ⟨(if jk.1 = 0 then 1 else 2),6+jk.2,.single⟩) }

def coreAtom (p : Fin 6) : AtomSpec := coreAtoms.get p

def coreBond (p q : Fin 6) : Nat := (source 0).bondOrder p.val q.val

def tag (mask : Fin 8) (v : Fin (source mask).atomCount) : Fin 6 ⊕ Fin 6 :=
  if h : v.val < 6 then .inl ⟨v.val,h⟩ else
    .inr ⟨if ((chosen mask)[v.val-6]?.getD 0) = 0 then 1 else 2,by split <;> omega⟩

def completion (mask : Fin 8) : Completion coreAtom coreBond where
  molecule := source mask
  core := {
    toFun := fun p => ⟨p.val,by simp [source,coreAtoms,RawMolecule.atomCount]; omega⟩
    inj' := by intro p q h; exact Fin.ext (congrArg (fun z : Fin (source mask).atomCount => z.val) h) }
  tag := tag mask
  core_tag := by intro p; simp [tag,p.isLt]
  core_only := by
    intro v p h
    unfold tag at h
    split at h
    · exact Fin.ext (congrArg (fun z : Fin 6 => z.val) (Sum.inl.inj h))
    · contradiction
  retained := by decide
  records := by fin_cases mask <;> decide
  bonds := by fin_cases mask <;> decide

theorem totals : ∀ mask : Fin 8, ∀ p : Fin 6,
    (completion mask).hydrogenCount p + (addedParents (source mask)).count p.val =
      (completion 7).hydrogenCount p := by decide

/-- Arbitrary-coordinate successful preparation yields the same nine-atom graph,
up to a core-fixing bijection. Only local input tables are reflected. -/
theorem prepared_equivalent (mask : Fin 8) {xyz pos : SpatialConfiguration} {out : RawMolecule}
    (done : prepare? (source mask) xyz = some (out,pos)) :
    ∃ e : Fin out.atomCount ≃ Fin (source 7).atomCount,
      (∀ p : Fin 6, (e ⟨p.val,lt_of_lt_of_le ((completion mask).core p).isLt
        (prepare?_certified done).atomCount_le⟩).val = p.val) ∧
      (∀ v, heavyCore ((source 7).atoms.get (e v)) = heavyCore (out.atoms.get v)) ∧
      (∀ v w, (source 7).bondOrder (e v).val (e w).val = out.bondOrder v.val w.val) := by
  let ca := producedCompletion (a := completion mask) (prepare?_certified done)
  let cb := completion 7
  have counts : ∀ p, ca.hydrogenCount p = cb.hydrogenCount p := by
    intro p
    rw [produced_hydrogenCount]
    exact totals mask p
  refine ⟨Completion.atomEquiv ca cb counts,?_,Completion.atomEquiv_records ca cb counts,
    Completion.atomEquiv_bonds ca cb counts⟩
  intro p
  exact congrArg Fin.val (Completion.atomEquiv_core ca cb counts p)

noncomputable def preparedGraphMap (mask : Fin 8) (i j : Input) (xyz pos : SpatialConfiguration)
    (done : prepare? (source mask) xyz = some (i.molecule,pos)) (target : j.molecule = source 7) : GraphMap i j :=
  let ca := producedCompletion (a := completion mask) (prepare?_certified done)
  ofHydrogenCounts ca (completion 7) rfl target (fun p => by rw [produced_hydrogenCount]; exact totals mask p)

theorem preparedGraphMap_core (mask : Fin 8) (i j : Input) (xyz pos : SpatialConfiguration)
    (done : prepare? (source mask) xyz = some (i.molecule,pos)) (target : j.molecule = source 7) (p : Fin 6) :
    (preparedGraphMap mask i j xyz pos done target).atoms
      ((rawVertices i rfl).symm ⟨p.val,lt_of_lt_of_le ((completion mask).core p).isLt
        (prepare?_certified done).atomCount_le⟩) =
      (rawVertices j target).symm ((completion 7).core p) :=
  ofHydrogenCounts_core (producedCompletion (a := completion mask) (prepare?_certified done))
    (completion 7) rfl target _ p

def c1HydrogenId (mask : Fin 8) : Nat := if mask.val.testBit 0 then 6 else (source mask).atomCount
private theorem c1_index_lt : ∀ mask : Fin 8, c1HydrogenId mask < 9 := by decide
private theorem no_eligible : ∀ mask : Fin 8, ∀ n : Fin (source mask).atomCount,
    ((source mask).atoms[n.val]?).map eligibleAtom ≠ some true := by decide

theorem no_placements (mask : Fin 8) (xyz pos : SpatialConfiguration) (out : RawMolecule) :
    sites (source mask) xyz out pos = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro n hn
  have bound := List.mem_range.mp hn
  unfold site?
  rw [if_neg (no_eligible mask ⟨n,bound⟩)]

theorem written_eq_prepared (mask : Fin 8) {xyz pos y : SpatialConfiguration} {out : RawMolecule}
    (p : Placement (source mask) xyz out pos y) : y = pos := by
  have eq : y.positions = pos.positions := List.ext_getElem? (fun n => p.fixed n (by rw [no_placements]; simp))
  cases y
  cases pos
  cases eq
  rfl

theorem output_count (mask : Fin 8) {xyz pos : SpatialConfiguration} {out : RawMolecule}
    (done : prepare? (source mask) xyz = some (out,pos)) : out.atomCount = 9 := by
  obtain ⟨e,_⟩ := prepared_equivalent mask done
  have h := Fintype.card_congr e
  simpa [source,coreAtoms,chosen,RawMolecule.atomCount] using h

theorem c1HydrogenId_lt (mask : Fin 8) {xyz pos : SpatialConfiguration} {out : RawMolecule}
    (done : prepare? (source mask) xyz = some (out,pos)) : c1HydrogenId mask < out.atomCount := by
  rw [output_count mask done]
  exact c1_index_lt mask

private theorem old_tag_c1 : ∀ mask : Fin 8, mask.val.testBit 0 = true →
    ∀ h : 6 < (source mask).atomCount, (completion mask).tag ⟨6,h⟩ = .inr 1 := by decide
private theorem fresh_plan_c1 : ∀ mask : Fin 8, mask.val.testBit 0 = false →
    (addedParents (source mask))[0]? = some 1 := by decide

theorem c1Hydrogen_tag (mask : Fin 8) {xyz pos : SpatialConfiguration} {out : RawMolecule}
    (done : prepare? (source mask) xyz = some (out,pos)) :
    (producedCompletion (a := completion mask) (prepare?_certified done)).tag
      ⟨c1HydrogenId mask,c1HydrogenId_lt mask done⟩ = .inr 1 := by
  let cert := prepare?_certified done
  by_cases bit : mask.val.testBit 0 = true
  · have bound : 6 < (source mask).atomCount := by
      have h : ∀ m : Fin 8, m.val.testBit 0 = true → 6 < (source m).atomCount := by decide
      exact h mask bit
    change producedTag cert _ = _
    rw [producedTag_old cert _ (by simpa [c1HydrogenId,bit] using bound)]
    simpa only [c1HydrogenId,bit,if_true] using old_tag_c1 mask bit bound
  · have off : mask.val.testBit 0 = false := Bool.eq_false_iff.mpr bit
    let v : Fin out.atomCount := ⟨c1HydrogenId mask,c1HydrogenId_lt mask done⟩
    have fresh : (source mask).atomCount ≤ v.val := by simp [v,c1HydrogenId,off]
    obtain ⟨c,tag,row⟩ := producedTag_fresh (a := completion mask) cert v fresh
    obtain ⟨parent,planned,row'⟩ := cert.fresh_row fresh v.isLt
    have planned0 : parent = 1 := by
      have h : v.val - (source mask).atomCount = 0 := by simp [v,c1HydrogenId,off]
      rw [h,fresh_plan_c1 mask off] at planned
      exact (Option.some.inj planned).symm
    have cEq : c = (1 : Fin 6) := by
      have h := List.singleton_inj.mp (row.symm.trans row')
      apply Fin.ext
      exact h.trans planned0
    rw [cEq] at tag
    exact tag

theorem preparedGraphMap_c1Hydrogen (mask : Fin 8) (i j : Input) (xyz pos : SpatialConfiguration)
    (done : prepare? (source mask) xyz = some (i.molecule,pos)) (target : j.molecule = source 7) :
    (preparedGraphMap mask i j xyz pos done target).atoms
      ((rawVertices i rfl).symm ⟨c1HydrogenId mask,c1HydrogenId_lt mask done⟩) =
      (rawVertices j target).symm ⟨6,by decide⟩ := by
  let ca := producedCompletion (a := completion mask) (prepare?_certified done)
  let counts : ∀ p, ca.hydrogenCount p = (completion 7).hydrogenCount p :=
    fun p => by rw [produced_hydrogenCount]; exact totals mask p
  apply (rawVertices j target).injective
  change (rawVertices j target)
    ((rawVertices j target).symm
      ((Completion.atomEquiv ca (completion 7) counts)
        ((rawVertices i rfl) ((rawVertices i rfl).symm ⟨c1HydrogenId mask,c1HydrogenId_lt mask done⟩)))) = _
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  have unique : ∀ v : Fin (source 7).atomCount, (completion 7).tag v = .inr 1 → v = ⟨6,by decide⟩ := by decide
  apply unique
  exact (Completion.atomEquiv_tag ca (completion 7) counts _).trans (c1Hydrogen_tag mask done)

/-- Degree follows directly from the raw bond table of an admitted graph. -/
private theorem neighborCount (i : Input) (mol : i.molecule = source 7) (a : i.certified.Atom) :
    Fintype.card (i.certified.moleculeGraph.Neighbor a) =
      Fintype.card {k : Fin 9 // 0 < (source 7).bondOrder a.val k.val} := by
  let e : i.certified.Atom ≃ Fin 9 := rawVertices i mol
  have adj (b : i.certified.Atom) : i.certified.moleculeGraph.Adj a b ↔
      0 < (source 7).bondOrder a.val (e b).val := by
    rw [LocalizedChemicalRingPhysicalSense.adj_iff i.molecule i.certified i.agreement
      i.admissible.1.1 i.admissible.1.2 i.supported,rawVertex_bond i mol]
    rfl
  exact Fintype.card_congr {
    toFun := fun b => ⟨e b.val,(adj b.val).mp b.property⟩
    invFun := fun k => ⟨e.symm k.val,(adj _).mpr (by simpa only [Equiv.apply_symm_apply] using k.property)⟩
    left_inv := fun b => Subtype.ext (e.symm_apply_apply b.val)
    right_inv := fun k => Subtype.ext (e.apply_symm_apply k.val) }

private theorem degreeTable : ∀ a : Fin 9,
    Fintype.card {k : Fin 9 // 0 < (source 7).bondOrder a.val k.val} =
      if a.val < 3 then 4 else 1 := by decide

/-- C2 retains its two identical terminal hydrogens. The other atoms beyond C1
are all terminal, including D itself. -/
theorem other_roots (i : Input) (mol : i.molecule = source 7)
    (valid : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) (offZero : a.val ≠ 0) (offOne : a.val ≠ 1) :
    RingChemicalGraphProof.root i a = some none := by
  let e : i.certified.Atom ≃ Fin 9 := rawVertices i mol
  have size : a.val < 9 := (e a).isLt
  have degree := (neighborCount i mol a).trans (degreeTable (e a))
  change Fintype.card (i.certified.moleculeGraph.Neighbor a) = (if a.val < 3 then 4 else 1) at degree
  by_cases two : a.val = 2
  · have four : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by simpa [two] using degree
    let c : i.certified.TetrahedralCenter := ⟨a,(i.certified.moleculeGraph.mem_tetrahedralCenterSet a).mpr four⟩
    let u : i.certified.Atom := e.symm 7
    let v : i.certified.Atom := e.symm 8
    have row (k : Fin 9) (hk : k = 7 ∨ k = 8) (b : i.certified.Atom) :
        i.molecule.bondOrder (e.symm k).val b.val = if b = a then 1 else 0 := by
      have table : ∀ n : Fin 9, ∀ x : Fin 9, x = 7 ∨ x = 8 →
          (source 7).bondOrder x.val n.val = if n.val = 2 then 1 else 0 := by decide
      rw [mol]
      change (source 7).bondOrder k.val (e b).val = _
      rw [table (e b) k hk]
      simp only [←two,Fin.ext_iff]
      rfl
    let p : TwinPair i := {
      c := c, u := u, v := v
      distinct := e.symm.injective.ne (by decide)
      records := by rw [mol]; rfl
      lu := row 7 (Or.inl rfl)
      lv := row 8 (Or.inr rfl) }
    exact p.root_refusal valid
  · have one : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 1 := by
      rw [degree,if_neg (by omega)]
    exact LeafAllRequests.root_ineligible i a (LeafAllRequests.terminal_ineligible i a one)


def chiralReading (xyz : SpatialConfiguration) (ids : List Nat) : Option Labels :=
  (readback? (geometry xyz) ids).map fun h => (.chiral h,.chiral h.swap)

/-- C0 uses four original heavy atoms. At C1 the lowest-priority ordinary H
can be either written or generated by the public preparation step. -/
def predicted (mask : Fin 8) (xyz : SpatialConfiguration) (id : Nat) : Option Labels :=
  if id = 0 then chiralReading xyz [3,4,1,2]
  else if id = 1 then do
    let (_,pos) ← prepare? (source mask) xyz
    chiralReading pos [0,2,5,c1HydrogenId mask]
  else none

/-- The two physical priority rows pull back through the prepared graph map.
This includes the actual generated C1 hydrogen and the unchanged original C0 row. -/
private theorem prepared_readbacks (base : Input) (target : base.molecule = source 7)
    (mask : Fin 8) (xyz pos : SpatialConfiguration) (i : Input)
    (done : prepare? (source mask) xyz = some (i.molecule,pos)) (atPos : i.spatial = pos) :
    let x := reindexed i base (preparedGraphMap mask i base xyz pos done target).atoms
    chiralReading x [3,4,1,2] = predicted mask xyz 0 ∧
      chiralReading x [0,2,5,6] = predicted mask xyz 1 := by
  let g := preparedGraphMap mask i base xyz pos done target
  let x := reindexed i base g.atoms
  let left (k : Fin 6) : i.certified.Atom :=
    (rawVertices i rfl).symm ⟨k.val,((completion mask).core k).isLt.trans_le (prepare?_certified done).atomCount_le⟩
  let right (k : Fin 6) : base.certified.Atom := (rawVertices base target).symm ((completion 7).core k)
  have fixed (k : Fin 6) : g.atoms (left k) = right k := preparedGraphMap_core mask i base xyz pos done target k
  have posCore (k : Fin 6) : k.val < (source mask).atomCount := ((completion mask).core k).isLt
  have point (k : Fin 6) : geometry x k.val = geometry pos k.val := by
    change x.positions[(right k).val]? = pos.positions[(left k).val]?
    rw [←fixed k]
    exact (reindexed_lookup_image g.atoms (left k)).trans (congrArg (fun z : SpatialConfiguration => z.positions[(left k).val]?) atPos)
  let low : i.certified.Atom := (rawVertices i rfl).symm ⟨c1HydrogenId mask,c1HydrogenId_lt mask done⟩
  let h6 : base.certified.Atom := (rawVertices base target).symm ⟨6,by decide⟩
  have pH : geometry x 6 = geometry pos (c1HydrogenId mask) := by
    change x.positions[h6.val]? = pos.positions[low.val]?
    rw [show h6 = g.atoms low from (preparedGraphMap_c1Hydrogen mask i base xyz pos done target).symm]
    exact (reindexed_lookup_image g.atoms low).trans (congrArg (fun z : SpatialConfiguration => z.positions[low.val]?) atPos)
  constructor
  · change chiralReading x [3,4,1,2] = chiralReading xyz [3,4,1,2]
    have original (k : Fin 6) : geometry x k.val = geometry xyz k.val :=
      (point k).trans ((prepare?_certified done).positions_getElem? (posCore k))
    have p3 : geometry x 3 = geometry xyz 3 := original 3
    have p4 : geometry x 4 = geometry xyz 4 := original 4
    have p1 : geometry x 1 = geometry xyz 1 := original 1
    have p2 : geometry x 2 = geometry xyz 2 := original 2
    simp only [chiralReading,readback?,List.mapM_cons,List.mapM_nil,p3,p4,p1,p2]
  · have p0 : geometry x 0 = geometry pos 0 := point 0
    have p2 : geometry x 2 = geometry pos 2 := point 2
    have p5 : geometry x 5 = geometry pos 5 := point 5
    change chiralReading x [0,2,5,6] =
      ((prepare? (source mask) xyz).bind fun pair => chiralReading pair.2 [0,2,5,c1HydrogenId mask])
    rw [done]
    change chiralReading x [0,2,5,6] = chiralReading pos [0,2,5,c1HydrogenId mask]
    simp only [chiralReading,readback?,List.mapM_cons,List.mapM_nil,p0,p2,p5,pH]


private theorem transport_prediction (base : Input) (target : base.molecule = source 7)
    (native : ∀ y (hy : y.positions.length = size base), let j := atGeometry base y hy
      LocalizedChemicalRing.coordinatesAdmitted j = true → ∀ b : j.certified.Atom, b.val < 2 →
        RingChemicalGraphProof.root j b = some (chiralReading y
          (if b.val = 0 then [3,4,1,2] else [0,2,5,6])))
    (mask : Fin 8) (xyz pos : SpatialConfiguration) (i : Input)
    (done : prepare? (source mask) xyz = some (i.molecule,pos)) (atPos : i.spatial = pos)
    (valid : LocalizedChemicalRing.coordinatesAdmitted i = true) (a : i.certified.Atom) :
    RingChemicalGraphProof.root i a = some (predicted mask xyz a.val) := by
  let g := preparedGraphMap mask i base xyz pos done target
  let x := reindexed i base g.atoms
  let j := withSourceGeometry i base g.atoms
  have validJ := RingRawRenumbering.AtomMap.coordinates g.atSourceGeometry valid
  have re := RingReportRenumber.chemical_root g.atSourceGeometry valid a
  let left (k : Fin 6) : i.certified.Atom :=
    (rawVertices i rfl).symm ⟨k.val,((completion mask).core k).isLt.trans_le (prepare?_certified done).atomCount_le⟩
  let right (k : Fin 6) : base.certified.Atom := (rawVertices base target).symm ((completion 7).core k)
  have fixed (k : Fin 6) : g.atoms (left k) = right k := preparedGraphMap_core mask i base xyz pos done target k
  have readings := prepared_readbacks base target mask xyz pos i done atPos
  have mappedId (k : Fin 6) : (g.atoms a).val = k.val ↔ a.val = k.val := calc
    _ ↔ g.atoms a = right k := Fin.ext_iff.symm
    _ ↔ a = left k := by rw [←fixed, g.atoms.injective.eq_iff]
    _ ↔ _ := Fin.ext_iff
  have zero := mappedId 0
  have one := mappedId 1
  change (g.atoms a).val = 0 ↔ a.val = 0 at zero
  change (g.atoms a).val = 1 ↔ a.val = 1 at one
  by_cases atZero : a.val = 0
  · have b0 := zero.mpr atZero
    have root := native x (reindexed_full _) validJ (g.atoms a) (by omega)
    rw [if_pos b0] at root
    refine (re.trans root).trans ?_
    simpa only [atZero] using congrArg some readings.1
  · by_cases atOne : a.val = 1
    · have b1 := one.mpr atOne
      have root := native x (reindexed_full _) validJ (g.atoms a) (by omega)
      rw [if_neg (by omega : (g.atoms a).val ≠ 0)] at root
      refine (re.trans root).trans ?_
      simpa only [atOne] using congrArg some readings.2
    · refine (re.trans (other_roots j target validJ (g.atoms a) (mt zero.mp atZero) (mt one.mp atOne))).trans ?_
      simp [predicted,atZero,atOne]

private theorem raw_of_priority_orders (base : Input) (target : base.molecule = source 7)
    (native : ∀ y (hy : y.positions.length = size base), let j := atGeometry base y hy
      LocalizedChemicalRing.coordinatesAdmitted j = true → ∀ b : j.certified.Atom, b.val < 2 →
        RingChemicalGraphProof.root j b = some (chiralReading y
          (if b.val = 0 then [3,4,1,2] else [0,2,5,6])))
    (mask : Fin 8) (xyz : SpatialConfiguration) (ids : List Nat) (rows : RingGroupedReport.Report) :
    RingHydrogenReport.fromRaw? (source mask) xyz ids = some rows ↔
      PlacementAdmission (source mask) xyz ids ∧ rows = ids.map (fun n => (n,predicted mask xyz n)) := by
  apply raw_labels_iff_admission
  intro out pos done y placement j hj valid a _
  obtain ⟨hm,hg⟩ := RingChemicalReport.admission_fields hj
  rw [←hm] at done
  exact transport_prediction base target native mask xyz pos j done (hg.trans (written_eq_prepared mask placement)) valid a

/-- It suffices to establish two coordinate-free ordering certificates on a single
fully explicit graph. All raw requested atoms, ordinary-H spellings, prepared
positions, reflections, refusals and admission gates then follow. -/
theorem public_of_constitution (base : Input) (target : base.molecule = source 7)
    (frames : ∀ a : base.certified.Atom, a.val < 2 →
      ∃ fr : RingNestedActivePair.Frame base (RingGroupedReport.origin base a),
        Nonempty (RingConstitutionalHand.OrientationFrame fr
          (if a.val = 0 then [3,4,1,2] else [0,2,5,6])))
    (mask : Fin 8) (xyz : SpatialConfiguration) (ids : List Nat) (rows : RingGroupedReport.Report) :
    RingHydrogenReport.fromRaw? (source mask) xyz ids = some rows ↔
      PlacementAdmission (source mask) xyz ids ∧ rows = ids.map (fun n => (n,predicted mask xyz n)) := by
  apply raw_of_priority_orders base target
  intro y hy
  dsimp only
  intro valid a small
  obtain ⟨fr,⟨cert⟩⟩ := frames a small
  have nonP : RingPyramidalPublication.phosphorus base a = false := by
    have carbon : (base.molecule.atoms[a.val]?).any (fun atom =>
        atom.element == .P && atom.charge == 0 && !atom.aromatic) = false := by
      rw [target]
      rcases (by omega : a.val = 0 ∨ a.val = 1) with h | h <;> rw [h] <;> decide
    simp [RingPyramidalPublication.phosphorus,carbon]
  have tetra : RingPyramidalPublication.focusP base (RingGroupedReport.origin base a) = none := by
    change (some a).filter (RingPyramidalPublication.phosphorus base) = none
    simp [Option.filter,nonP]
  have hand := RingConstitutionalHand.root_atGeometry base y hy valid a tetra cert
  rw [inputGeometry_eq] at hand
  exact hand

/-- Admission makes both isotope-sensitive predictions assigned. The same two
constitutional frames used by `public_of_constitution` provide nonzero physical readings,
even when neither atom occurs in the requested list. -/
theorem predicted_isSome_of_constitution (base : Input) (target : base.molecule = source 7)
    (frames : ∀ a : base.certified.Atom, a.val < 2 →
      ∃ fr : RingNestedActivePair.Frame base (RingGroupedReport.origin base a),
        Nonempty (RingConstitutionalHand.OrientationFrame fr
          (if a.val = 0 then [3,4,1,2] else [0,2,5,6])))
    (mask : Fin 8) (xyz : SpatialConfiguration) (ids : List Nat)
    (admission : PlacementAdmission (source mask) xyz ids) :
    (predicted mask xyz 0).isSome = true ∧ (predicted mask xyz 1).isSome = true := by
  obtain ⟨s,out,pos,_,_,_,done,all⟩ := admission
  have placement : Placement (source mask) xyz out pos pos := by
    refine ⟨rfl,fun _ _ => rfl,?_⟩
    intro t ht
    rw [no_placements] at ht
    contradiction
  obtain ⟨i,hi,valid⟩ := all pos placement
  obtain ⟨hm,hg⟩ := RingChemicalReport.admission_fields hi
  rw [←hm] at done
  let g := preparedGraphMap mask i base xyz pos done target
  let x := reindexed i base g.atoms
  have validJ := AtomMap.coordinates g.atSourceGeometry valid
  let right (k : Fin 6) : base.certified.Atom := (rawVertices base target).symm ((completion 7).core k)
  have admittedHand (k : Fin 6) (small : k.val < 2) :
      (chiralReading x (if k.val = 0 then [3,4,1,2] else [0,2,5,6])).isSome = true := by
    obtain ⟨fr,⟨cert⟩⟩ := frames (right k) small
    have h := RingConstitutionalHand.root_atGeometry_isSome base x (reindexed_full _) validJ (right k) cert
    rw [inputGeometry_eq] at h
    exact (Option.isSome_map ..).trans h
  have readings := prepared_readbacks base target mask xyz pos i done hg
  have zero := admittedHand 0 (by decide)
  have one := admittedHand 1 (by decide)
  change (chiralReading x [3,4,1,2]).isSome = true at zero
  change (chiralReading x [0,2,5,6]).isSome = true at one
  rw [readings.1] at zero
  rw [readings.2] at one
  exact ⟨zero,one⟩

end TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings.public_of_constitution

assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings.predicted_isSome_of_constitution
