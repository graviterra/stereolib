import TetraStereo.Engine.RingTwinCoordinateTransport
import TetraStereo.Examples.DecalinRelativeConfiguration
import TetraStereo.OneCenter.LocalizedMarkedMolecularConfiguration

/-! Geometric transport for the two junctions of fully hydrogenated decalin.
The eight methylene carbons have distinct terminal H twins outside either
fusion root. Only the two explicit fusion-frame readings are needed. -/
set_option autoImplicit false
namespace TetraStereo.Examples.DecalinFrames
open TetraStereo.Engine OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingAtomicNeighborOrder (neighbors degree_eq enumeration enumeration_ids)
open RingWrittenPHReadings (geometry tetraEnumeration)
open private bound toAtom from TetraStereo.Engine.RingAtomicNeighborOrder
open private four_eta from TetraStereo.Engine.RingGroupedGeometry

def molecule : RawMolecule := {
  atoms := (List.replicate 10 Element.C ++ List.replicate 18 Element.H).map AtomSpec.aliphatic
  bonds := [(0,2),(0,6),(0,1),(0,10),(1,3),(1,8),(1,11),(2,4),(3,5),(4,5),
    (6,7),(7,9),(8,9),(2,12),(2,13),(3,14),(3,15),(4,16),(4,17),(5,18),
    (5,19),(6,20),(6,21),(7,22),(7,23),(8,24),(8,25),(9,26),(9,27)].map
      fun (a,b) => ⟨a,b,.single⟩ }

def junctionRow (a : Nat) : List Nat := if a = 0 then [1,2,6,10] else [0,3,8,11]

/-- Two signed readings in consistently ordered local frames, allowing flat
frames and missing points. -/
def JunctionAgreement (w x : SpatialConfiguration) : Prop :=
  ∀ a : Fin 2, readback? (geometry w) (junctionRow a) = readback? (geometry x) (junctionRow a)

/-- Read the same determinant used by the independent relative-configuration specification. -/
theorem readback_frame (g : Geometry) (ids : DecalinRelativeConfiguration.Frame Nat)
    (p : Nat → CartesianPoint3)
    (present : ∀ n ∈ [ids.other,ids.routeA,ids.routeB,ids.hydrogen], g n = some (p n)) :
    readback? g [ids.other,ids.routeA,ids.routeB,ids.hydrogen] =
      descriptorOfOrientedVolume? ((ids.map p).volume) := by
  have a := present ids.other (by simp)
  have b := present ids.routeA (by simp)
  have c := present ids.routeB (by simp)
  have d := present ids.hydrogen (by simp)
  simp [readback?,List.mapM_cons,a,b,c,d,descriptorOfPriorityOrderedPoints?,
    DecalinRelativeConfiguration.Frame.volume,DecalinRelativeConfiguration.Frame.map]

private def incident (a : Nat) := (List.range molecule.atomCount).filter fun n => 0 < molecule.bondOrder a n

private theorem neighbor_perm (a : Nat) : (neighbors molecule a).Perm (incident a) :=
  (RingStereoSiblingPass.legal_order _ _).perm

private theorem graph_rows : ∀ a : Fin 2, (neighbors molecule a.val).Perm (junctionRow a) := by
  have rows : ∀ a : Fin 2, (incident a).Perm (junctionRow a) := by decide +kernel
  exact fun a => (neighbor_perm a).trans (rows a)

private theorem four_only : ∀ a : Fin 28, (neighbors molecule a.val).length = 4 → a.val < 10 := by
  have bound : ∀ a : Fin 28, (incident a).length = 4 → a.val < 10 := by decide +kernel
  exact fun a h => bound a ((neighbor_perm a).length_eq.symm.trans h)

private theorem no_pyramids : ∀ a : Fin 28, RingAtomicNeighborOrder.neutralPyramidal molecule a.val = false := by
  decide +kernel

theorem closed : RingHydrogenCompletion.plan molecule = [] := by decide +kernel

private def leaf (a : Nat) := 12 + 2 * (a - 2)

private theorem hydrogens : ∀ k : Fin 8,
    let a := k.val + 2
    (molecule.atoms[leaf a]?).map RingRawRenumbering.molecularRecord =
      (molecule.atoms[leaf a + 1]?).map RingRawRenumbering.molecularRecord ∧
    ∀ b : Fin 28,
      molecule.bondOrder (leaf a) b.val = (if b.val = a then 1 else 0) ∧
      molecule.bondOrder (leaf a + 1) b.val = (if b.val = a then 1 else 0) := by
  decide +kernel

private theorem atom_bound {i : Input} (raw : i.molecule = molecule) (a : i.certified.Atom) : a.val < 28 := by
  simpa only [raw] using bound i a

private theorem methylene_pair {i : Input} (raw : i.molecule = molecule)
    (c : i.certified.TetrahedralCenter) (lo : 2 ≤ c.val.val) (hi : c.val.val < 10)
    (root : i.certified.Atom) (junction : root.val < 2) :
    ∃ p : RingHydrogenSpelling.TwinPair i, p.c = c ∧ root ≠ p.u ∧ root ≠ p.v := by
  let a := c.val.val
  have ha : (a - 2) + 2 = a := by dsimp [a]; omega
  have spec := hydrogens ⟨a-2,by dsimp [a]; omega⟩
  simp only [ha] at spec
  have hu : leaf a < i.molecule.atomCount := by rw [raw]; change leaf a < 28; unfold leaf; dsimp [a]; omega
  have hv : leaf a + 1 < i.molecule.atomCount := by rw [raw]; change leaf a + 1 < 28; unfold leaf; dsimp [a]; omega
  let u := toAtom i (leaf a) hu
  let v := toAtom i (leaf a + 1) hv
  have eu : u.val = leaf a := rfl
  have ev : v.val = leaf a + 1 := rfl
  let p : RingHydrogenSpelling.TwinPair i := {
    c := c, u := u, v := v
    distinct := fun eq => by have h := congrArg Fin.val eq; rw [eu,ev] at h; omega
    records := by rw [eu,ev,raw]; exact spec.1
    lu := fun b => by rw [eu,raw]; simpa only [Fin.ext_iff] using (spec.2 ⟨b.val,atom_bound raw b⟩).1
    lv := fun b => by rw [ev,raw]; simpa only [Fin.ext_iff] using (spec.2 ⟨b.val,atom_bound raw b⟩).2 }
  refine ⟨p,rfl,?_,?_⟩
  · change root ≠ u
    intro h
    have eq := congrArg Fin.val h
    rw [eu] at eq
    unfold leaf at eq
    omega
  · change root ≠ v
    intro h
    have eq := congrArg Fin.val h
    rw [ev] at eq
    unfold leaf at eq
    omega

private theorem canonical_perm (i : Input) (c : i.certified.TetrahedralCenter) :
    (RingRetainedAuxiliary.canonical i.certified c).Perm (neighbors i.molecule c.val.val) := by
  have four := (i.certified.moleculeGraph.mem_tetrahedralCenterSet c.val).mp c.property
  have size := (degree_eq i c.val).symm.trans four
  let enum := enumeration i c.val size
  let e := (tetraEnumeration i c).trans enum.symm
  have perm := (Equiv.Perm.map_finRange_perm e).map (fun s => (enum s).val.val)
  have slots (s : Fin 4) : (enum (e s)).val.val = (i.certified.canonicalLigandAtom c s).val := by
    simp [e]
    rfl
  rw [List.map_map] at perm
  simp only [Function.comp_def,slots] at perm
  exact perm.trans ((enumeration_ids i c.val size) ▸ List.Perm.refl _)

private theorem frame_perm {i : Input} {q : RingActivePairs.Site i} (fr : RingNestedActivePair.Frame i q) :
    (fr.atoms (List.finRange 4)).Perm (neighbors i.molecule fr.center.val.val) := by
  have eq : fr.atoms (List.finRange 4) = fr.ids := four_eta _ (by simpa [RingRetainedAuxiliary.canonical] using fr.physical.length_eq)
  exact eq ▸ fr.physical.trans (canonical_perm i fr.center)

private theorem site_of_junction_frames {i : Input} (raw : i.molecule = molecule) (x : SpatialConfiguration)
    (root : i.certified.Atom) (junction : root.val < 2) (q : RingActivePairs.Site i)
    (on : q.val.root = root) (missed : RingRootTwinDecision.direct i q ≠ some (some none))
    (same : ∀ fr : RingNestedActivePair.Frame i q, fr.center.val.val < 2 →
      readback? (geometry i.spatial) (junctionRow fr.center.val.val) =
        readback? (geometry x) (junctionRow fr.center.val.val)) :
    RingFrameTransport.SiteAgree i (geometry i.spatial) (geometry x) q := by
  constructor
  · intro fr
    let a := fr.center.val.val
    have degree := (i.certified.moleculeGraph.mem_tetrahedralCenterSet fr.center.val).mp fr.center.property
    change Fintype.card (i.certified.moleculeGraph.Neighbor fr.center.val) = 4 at degree
    rw [degree_eq,raw] at degree
    have hi : a < 10 := four_only ⟨a,atom_bound raw _⟩ degree
    by_cases j : a < 2
    · have perm := frame_perm fr
      rw [raw] at perm
      apply LocalizedMarkedMolecularConfiguration.readback_perm_congr (junctionRow a) _
        (by unfold junctionRow; split <;> decide) (by unfold junctionRow; split <;> rfl)
        (perm.trans (graph_rows ⟨a,j⟩)) (same fr j)
    · exfalso
      have p := (RingRootTwinDecision.detected_iff i root fr.center).mpr
        (methylene_pair raw fr.center (by omega) hi root junction)
      obtain ⟨t,ht⟩ := Option.isSome_iff_exists.mp p
      exact missed (by simp [RingRootTwinDecision.direct,fr.recognized,on,ht])
  · intro a hp
    have gate := RingPhysicalFrameBridge.focusP_phosphorus hp
    have ng : RingAtomicNeighborOrder.neutralPyramidal i.molecule a.val = true :=
      (Bool.and_eq_true_iff.mp gate).1
    rw [raw] at ng
    exact False.elim (by have f := no_pyramids ⟨a.val,atom_bound raw a⟩; simp [ng] at f)

theorem residual {i : Input} (raw : i.molecule = molecule) (x : SpatialConfiguration)
    (same : JunctionAgreement i.spatial x) (root : i.certified.Atom) (junction : root.val < 2) :
    RingTwinCoordinateTransport.ResidualAgreement i x root :=
  fun q on missed => site_of_junction_frames raw x root junction q on missed
    (fun fr h => same ⟨fr.center.val.val,h⟩)

/-- All root priorities use only the signed reading at the opposite fusion atom.
The root's own local tetrahedron may invert or become flat. -/
theorem auxiliary {i : Input} (raw : i.molecule = molecule) (x : SpatialConfiguration)
    (root : i.certified.Atom) (junction : root.val < 2)
    (same : readback? (geometry i.spatial) (junctionRow (1-root.val)) =
      readback? (geometry x) (junctionRow (1-root.val))) :
    RingTwinCoordinateTransport.AuxiliaryAgreement i x root := by
  intro q on away missed
  apply site_of_junction_frames raw x root junction q on missed
  intro fr j
  have recognized := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q fr.center).mp fr.recognized
  have ne : fr.center.val.val ≠ root.val := by
    intro eq
    exact away (recognized.2.trans (congrArg some (Fin.ext eq)))
  have eq : fr.center.val.val = 1 - root.val := by omega
  simpa only [eq] using same

/-- Any list of the two fusion IDs, with arbitrary order and repetitions. -/
theorem raw_report {i : Input} (raw : i.molecule = molecule)
    (x : SpatialConfiguration) (full : x.positions.length = RingSpatialTransport.size i)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (moved : LocalizedChemicalRing.coordinatesAdmitted (RingSpatialTransport.atGeometry i x full) = true)
    (same : JunctionAgreement i.spatial x) (roots : List i.certified.Atom)
    (junctions : ∀ a ∈ roots, a.val < 2) :
    RingHydrogenReport.fromRaw? molecule i.spatial (roots.map Fin.val) =
      RingHydrogenReport.fromRaw? molecule x (roots.map Fin.val) := by
  rw [←raw]
  exact RingTwinCoordinateTransport.raw i x full admitted moved (raw ▸ closed) roots
    (fun a ha => residual raw x same a (junctions a ha))

open private calibrated from TetraStereo.Engine.RingRetainedAuxiliary

private def atom (i : Input) (raw : i.molecule = molecule) (a : Fin 28) : i.certified.Atom :=
  toAtom i a.val (by rw [raw]; exact a.isLt)

/-- Physical admission rules out zero volume and absent points at both junctions. -/
theorem junction_nonflat (i : Input) (raw : i.molecule = molecule)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true) (a : Fin 2) :
    (readback? (geometry i.spatial) (junctionRow a.val)).isSome = true := by
  let v := atom i raw ⟨a.val,by omega⟩
  have four : Fintype.card (i.certified.moleculeGraph.Neighbor v) = 4 := by
    rw [degree_eq,raw]
    exact (graph_rows a).length_eq.trans (by unfold junctionRow; split <;> rfl)
  let c : i.certified.TetrahedralCenter := ⟨v,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr four⟩
  have rows := canonical_perm i c
  rw [raw] at rows
  rw [← RingWrittenPHReadings.inputGeometry_eq]
  exact calibrated i admit c _ ((rows.trans (graph_rows a)).symm)

/-- Source labels for the four pairs of ordered local determinant signs. -/
def fusionLabel (a b : RS) : RingNestedActivePair.Labels :=
  let h := LocalizedTetrahedralRSPseudoDescriptor.pseudoasymmetric (if a = b then .r else .s)
  (h,h)

def expected (a b : RS) (ids : List Nat) : RingGroupedReport.Report :=
  ids.map fun n => (n, if n < 2 then some (fusionLabel a b) else none)

/-- Each representative contributes one observed report of two public rows.
The coordinate calibration and structural admission are separate fields. -/
structure Representative (a b : RS) where
  input : Input
  raw : input.molecule = molecule
  admitted : LocalizedChemicalRing.coordinatesAdmitted input = true
  first : readback? (geometry input.spatial) (junctionRow 0) = some a
  second : readback? (geometry input.spatial) (junctionRow 1) = some b
  checked : RingHydrogenReport.fromRaw? molecule input.spatial [0,1] = some (expected a b [0,1])

/-- A finite certificate at four tables determines both rows for any geometry passing the gate. -/
theorem fusion_rows (reps : ∀ a b : RS, Representative a b) (i : Input)
    (raw : i.molecule = molecule) (admit : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    ∃ a b : RS, readback? (geometry i.spatial) (junctionRow 0) = some a ∧
      readback? (geometry i.spatial) (junctionRow 1) = some b ∧
      RingHydrogenReport.fromRaw? molecule i.spatial [0,1] = some (expected a b [0,1]) := by
  obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp (junction_nonflat i raw admit 0)
  obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp (junction_nonflat i raw admit 1)
  let r := reps a b
  have graph := raw.trans r.raw.symm
  have full := RingSpatialTransport.full_at_other graph
  have moved : LocalizedChemicalRing.coordinatesAdmitted (RingSpatialTransport.atGeometry i r.input.spatial full) = true := by
    rw [RingSpatialTransport.eq_atGeometry graph]; exact r.admitted
  have same : JunctionAgreement i.spatial r.input.spatial := by
    intro v
    fin_cases v
    · exact ha.trans r.first.symm
    · exact hb.trans r.second.symm
  have transport := raw_report raw r.input.spatial full admit moved same [atom i raw 0,atom i raw 1] (by
    intro v hv
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hv
    rcases hv with rfl | rfl
    · exact (by decide : 0 < 2)
    · exact (by decide : 1 < 2))
  exact ⟨a,b,ha,hb,transport.trans r.checked⟩

/-- The other twenty-six atoms are completed refusals for every admitted geometry. -/
theorem nonjunction (i : Input) (raw : i.molecule = molecule)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true) (v : i.certified.Atom) (off : 2 ≤ v.val) :
    RingChemicalGraphProof.root i v = some none := by
  by_cases four : Fintype.card (i.certified.moleculeGraph.Neighbor v) = 4
  · let c : i.certified.TetrahedralCenter := ⟨v,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr four⟩
    have h := four
    rw [degree_eq,raw] at h
    have hi := four_only ⟨v.val,atom_bound raw v⟩ h
    obtain ⟨p,hp,_,_⟩ := methylene_pair raw c off hi (atom i raw 0) (by exact (by decide : 0 < 2))
    have result := p.root_refusal admit
    rw [hp] at result
    exact result
  · have inactive : ¬ RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) (RingGroupedReport.origin i v) := by
      rintro ⟨_,b,current,on⟩
      obtain rfl : v = b := Option.some.inj current
      have ng : RingAtomicNeighborOrder.neutralPyramidal i.molecule v.val = false := raw ▸ no_pyramids ⟨v.val,atom_bound raw v⟩
      have notP : RingPyramidalPublication.phosphorus i v = false := by
        change (RingAtomicNeighborOrder.neutralPyramidal i.molecule v.val && _) = false
        simp [ng]
      simp [RingPyramidalPublication.eligible,four,notP] at on
    exact (RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i) v).trans
      ((RingChemicalGraphProof.state_eq i _).trans (RingChemicalGraphProof.skips i _ _ inactive))

/-- The independent two-determinant specification, in the native report format. -/
def independentReport? (x : SpatialConfiguration) (ids : List Nat) : Option RingGroupedReport.Report := do
  guard (ids.all (· < 28))
  let a ← readback? (geometry x) (junctionRow 0)
  let b ← readback? (geometry x) (junctionRow 1)
  return expected a b ids

open private row? from TetraStereo.Engine.RingChemicalReport

/-- Four fixed two-row checks determine every atom in arbitrary request order. -/
theorem complete_of_representatives (reps : ∀ a b : RS, Representative a b) (i : Input)
    (raw : i.molecule = molecule) (admit : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (roots : List i.certified.Atom) :
    RingHydrogenReport.fromRaw? molecule i.spatial (roots.map Fin.val) =
      independentReport? i.spatial (roots.map Fin.val) := by
  obtain ⟨a,b,ha,hb,checked⟩ := fusion_rows reps i raw admit
  have report_eq (vs : List i.certified.Atom) :
      RingHydrogenReport.fromRaw? molecule i.spatial (vs.map Fin.val) = RingChemicalReport.report? i vs := by
    rw [←raw]; exact RingWrittenPHReadings.fromRaw_closed_report i (raw ▸ closed) admit vs
  have pair := (report_eq [atom i raw 0,atom i raw 1]).symm.trans checked
  have extracted : RingChemicalGraphProof.root i (atom i raw 0) = some (some (fusionLabel a b)) ∧
      RingChemicalGraphProof.root i (atom i raw 1) = some (some (fusionLabel a b)) := by
    cases h : RingChemicalGraphProof.root i (atom i raw 0) <;>
      cases k : RingChemicalGraphProof.root i (atom i raw 1) <;>
      simp_all [RingChemicalReport.report?,row?,List.mapM_cons,expected]
  have each (v : i.certified.Atom) :
      row? v = some (v.val,if v.val < 2 then some (fusionLabel a b) else none) := by
    by_cases h : v.val < 2
    · have cases' : v = atom i raw 0 ∨ v = atom i raw 1 := by
        rcases (by omega : v.val = 0 ∨ v.val = 1) with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases cases' with rfl | rfl <;> simp [row?,extracted,h]
    · simp [row?,h,nonjunction i raw admit v (by omega)]
  have good : ((roots.map Fin.val).all (· < 28)) = true := by
    apply List.all_eq_true.mpr
    intro n hn
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hn
    exact decide_eq_true (atom_bound raw v)
  rw [report_eq]
  simp [independentReport?,ha,hb,good]
  clear good
  unfold RingChemicalReport.report? expected
  induction roots with
  | nil => rfl
  | cons v vs ih =>
    simp [List.mapM_cons,each,ih]

/-- Agreement with the independent relative-configuration formula for every raw request,
including invalid IDs, the empty list and repetitions, assuming four measured reports. -/
theorem raw_complete_of_representatives (reps : ∀ a b : RS, Representative a b) (i : Input)
    (raw : i.molecule = molecule) (admit : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (ids : List Nat) :
    RingHydrogenReport.fromRaw? molecule i.spatial ids = independentReport? i.spatial ids := by
  by_cases good : (ids.all (· < 28)) = true
  · let vs := ids.attach.map fun n => atom i raw ⟨n.val,of_decide_eq_true (List.all_eq_true.mp good _ n.property)⟩
    have vs_eq : vs.map Fin.val = ids := by simp [vs,List.map_map,Function.comp_def,atom,toAtom]
    rw [←vs_eq]
    exact complete_of_representatives reps i raw admit vs
  · have absent : RingMolecularReport.resolve i ids = none := by
      cases h : RingMolecularReport.resolve i ids with
      | none => rfl
      | some vs =>
        exfalso
        apply good
        rw [← (RingMolecularReport.resolve_iff ..).mp h]
        apply List.all_eq_true.mpr
        intro n hn
        obtain ⟨v,_,rfl⟩ := List.mem_map.mp hn
        exact decide_eq_true (atom_bound raw v)
    have input := RingSpatialTransport.readmit i
    rw [raw] at input
    simp [RingHydrogenReport.fromRaw_closed_eq closed,RingChemicalReport.fromRaw?,input,absent,
      independentReport?,good]

/-- Identify the sign-based labels used in the finite reduction with the
independent product-of-determinants definition. -/
theorem fusionLabel_relative (f g : DecalinRelativeConfiguration.Frame CartesianPoint3) (a b : RS)
    (first : descriptorOfOrientedVolume? f.volume = some a)
    (second : descriptorOfOrientedVolume? g.volume = some b) :
    DecalinRelativeConfiguration.relative f g =
      some (if a = b then PseudoRS.r else PseudoRS.s) := by
  cases a <;> cases b <;>
    simp only [descriptorOfOrientedVolume?_eq_some_R_iff,descriptorOfOrientedVolume?_eq_some_S_iff] at first second <;>
    simp (disch := linarith) [DecalinRelativeConfiguration.relative,mul_pos_iff,mul_neg_iff,first,second] <;> grind

end TetraStereo.Examples.DecalinFrames
assert_kernel_only TetraStereo.Examples.DecalinFrames.residual
assert_kernel_only TetraStereo.Examples.DecalinFrames.auxiliary
assert_kernel_only TetraStereo.Examples.DecalinFrames.raw_report
assert_kernel_only TetraStereo.Examples.DecalinFrames.raw_complete_of_representatives
