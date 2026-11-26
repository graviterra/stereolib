import TetraStereo.Engine.RingTerminalTwinRefusal

/-! Whole-branch symmetries of the public ring evaluator. The graph action may
move auxiliary centers. Off-root physical readings and independently proved
refusals determine the contents of the public sphere queue. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter RingRawRenumbering
open LocalizedChemicalRing (Input)

/-- All ordered atom pairs are checked, so both bond directions are included.
Coordinates and inline-H spelling fields are deliberately absent. -/
def graphSymmetryValid (i : Input) (e : Equiv.Perm i.certified.Atom) : Prop :=
  (∀ a, (i.molecule.atoms[(e a).val]?).map molecularRecord =
    (i.molecule.atoms[a.val]?).map molecularRecord) ∧
  (∀ a b, i.molecule.bondOrder (e a).val (e b).val = i.molecule.bondOrder a.val b.val)

instance (i : Input) (e : Equiv.Perm i.certified.Atom) : Decidable (graphSymmetryValid i e) := by
  unfold graphSymmetryValid
  infer_instance

def checkGraphSymmetry? (i : Input) (e : Equiv.Perm i.certified.Atom) : Option (GraphMap i i) :=
  if h : graphSymmetryValid i e then some ⟨e,h.1,h.2⟩ else none

theorem checkGraphSymmetry_atoms (i : Input) (e : Equiv.Perm i.certified.Atom)
    (g : GraphMap i i) (found : checkGraphSymmetry? i e = some g) : g.atoms = e := by
  unfold checkGraphSymmetry? at found
  split at found
  · exact congrArg GraphMap.atoms (Option.some.inj found).symm
  · contradiction

theorem checkGraphSymmetry_iff (i : Input) (e : Equiv.Perm i.certified.Atom) :
    (checkGraphSymmetry? i e).isSome = true ↔ ∃ g : GraphMap i i, g.atoms = e := by
  constructor
  · intro found
    obtain ⟨g,hg⟩ := Option.isSome_iff_exists.mp found
    exact ⟨g,checkGraphSymmetry_atoms i e g hg⟩
  · rintro ⟨g,hg⟩
    have valid : graphSymmetryValid i e := by
      rw [←hg]
      exact ⟨g.records,g.bonds⟩
    simp [checkGraphSymmetry?,valid]

theorem checkGraphSymmetry_valid (i : Input) (e : Equiv.Perm i.certified.Atom) :
    (checkGraphSymmetry? i e).isSome = true ↔ graphSymmetryValid i e := by
  simp [checkGraphSymmetry?]
end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.checkGraphSymmetry_iff
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.checkGraphSymmetry_atoms
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.checkGraphSymmetry_valid

namespace TetraStereo.Engine.RingFrameTransport
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame)
open RingActiveDistanceSchedule (View Visible distance height frozen)
open RingGraphPaths (Path)

private theorem root_mem_path {i : Input} {root current : i.certified.Atom}
    {history : List i.certified.Atom} (path : Path i root history current) : root ∈ history := by
  induction path with
  | origin => simp
  | step _ _ _ ih => exact List.mem_cons_of_mem _ ih

private theorem path_return_is_origin {i : Input} {root current : i.certified.Atom}
    {history : List i.certified.Atom} (path : Path i root history current) (same : current = root) :
    history = [root] := by
  cases path with
  | origin => rfl
  | step prior bond fresh => exact False.elim (fresh (same ▸ root_mem_path prior))

/-- A real positive-distance visit cannot return to its original root. Ring-return
copies are duplicate leaves, so they are outside this real-path lemma. -/
theorem positive_real_not_root {i : Input} (q : Site i)
    (real : q.val.node.provenance = .realAtom) (positive : 0 < distance q) :
    q.val.node.current? ≠ some q.val.root := by
  obtain ⟨b,found,path⟩ := RingGraphPaths.site_path q real
  intro returns
  have same : b = q.val.root := Option.some.inj (found.symm.trans returns)
  have hist := path_return_is_origin path same
  have length := i.certified.carrierOccurrence_history_length_eq_address_succ q
  rw [hist] at length
  change 1 = distance q + 1 at length
  omega

/-- Convert one canonical center hand equality to the actual local occurrence frame.
Only this frame's own center is required; no global geometric gate is involved. -/
theorem frame_agree_of_canonical {i : Input} {q : Site i} (fr : Frame i q) {g g' : Geometry}
    (same : readback? g (RingRetainedAuxiliary.canonical i.certified fr.center) =
      readback? g' (RingRetainedAuxiliary.canonical i.certified fr.center)) :
    readback? g (fr.atoms (List.finRange 4)) = readback? g' (fr.atoms (List.finRange 4)) := by
  have inj : Function.Injective (fun k : Fin 4 => (i.certified.canonicalLigandAtom fr.center k).val) :=
    fun _ _ eq => i.certified.canonicalLigandAtom_injective fr.center (Fin.ext eq)
  obtain ⟨π,hπ⟩ := RingPhysicalFrameBridge.written_frame_order fr.ids
    (by simpa [RingRetainedAuxiliary.canonical] using fr.physical.length_eq.symm)
    (fun k : Fin 4 => (i.certified.canonicalLigandAtom fr.center k).val) inj fr.physical
  rw [show fr.atoms (List.finRange 4) = RingWrittenPHReadings.order
    (fun k : Fin 4 => (i.certified.canonicalLigandAtom fr.center k).val) π from hπ]
  exact RingWrittenPHReadings.order_readback_congr _ same π

/-- Local bridge from canonical tetrahedral hands at just the recognized centers,
and the P orders actually available at this occurrence. -/
theorem siteAgree_of_canonical {i : Input} {q : Site i} {g g' : Geometry}
    (tetra : ∀ fr : Frame i q,
      readback? g (RingRetainedAuxiliary.canonical i.certified fr.center) =
      readback? g' (RingRetainedAuxiliary.canonical i.certified fr.center))
    (phosphorus : ∀ b : i.certified.Atom, RingPyramidalPublication.focusP i q = some b →
      ∀ row : List Nat, row.Perm (ligandIds i q) →
        readback? g (row ++ [b.val]) = readback? g' (row ++ [b.val])) : SiteAgree i g g' q :=
  ⟨fun fr => frame_agree_of_canonical fr (tetra fr),phosphorus⟩

/-- General branch induction: each positive-distance occurrence either has matching
local frames or an independently established equality of its two state cells. -/
theorem stateG_positive_of_local_or_equal {i : Input} {g g' : Geometry} (root : i.certified.Atom)
    (laws : ∀ q : Site i, q.val.root = root → 0 < distance q →
      SiteAgree i g g' q ∨ stateG i g q = stateG i g' q)
    (q : Site i) (on : q.val.root = root) (positive : 0 < distance q) :
    stateG i g q = stateG i g' q := by
  suffices h : ∀ n (u : Site i), u.val.root = root → 0 < distance u → height i-distance u = n →
      stateG i g u = stateG i g' u from h _ q on positive rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u on positive depth
    rcases laws u on positive with agree | equal
    · have readers : frozen (stateG i g) u = frozen (stateG i g') u := frozen_congr u (fun v vis => by
        have upper := RingActiveDistanceSchedule.distance_bound v
        have deeper := vis.2.1
        exact ih _ (by omega) v (vis.1.trans on) (by omega) rfl)
      exact (stateG_eq i g u).trans ((congrArg (publishG i g u) readers).trans
        ((publishG_congr agree _).trans (stateG_eq i g' u).symm))
    · exact equal

/-- The root's frozen reader sees only the positive-distance branch cells. -/
theorem frozen_root_of_positive {i : Input} {g g' : Geometry} (root : i.certified.Atom)
    (same : ∀ q : Site i, q.val.root = root → 0 < distance q → stateG i g q = stateG i g' q) :
    frozen (stateG i g) (RingGroupedReport.origin i root) =
      frozen (stateG i g') (RingGroupedReport.origin i root) := by
  apply frozen_congr
  intro q visible
  exact same q visible.1 (by simpa [distance,RingGroupedReport.origin] using visible.2.1)

end TetraStereo.Engine.RingFrameTransport

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingSpatialTransport RingNumberedHydrogenGeometry RingWrittenPHReadings RingFrameTransport
open LocalizedChemicalRing (Input)
variable {i : Input}

/-- The inverse atom map restricts to an actual bijection of the physical
neighbors of any fixed center. It is derived from molecular bond agreement. -/
def GraphMap.inverseNeighbors (g : GraphMap i i) (c : i.certified.Atom)
    (fixed : g.atoms c = c) : i.certified.moleculeGraph.Neighbor c ≃ i.certified.moleculeGraph.Neighbor c where
  toFun n := ⟨g.atoms.symm n.val,by
    apply (g.atSourceGeometry.adj c (g.atoms.symm n.val)).mpr
    change i.certified.moleculeGraph.Adj (g.atoms c) (g.atoms (g.atoms.symm n.val))
    simpa only [fixed,g.atoms.apply_symm_apply] using n.property⟩
  invFun n := ⟨g.atoms n.val,by
    have h := (g.atSourceGeometry.adj c n.val).mp n.property
    change i.certified.moleculeGraph.Adj (g.atoms c) (g.atoms n.val) at h
    simpa only [fixed] using h⟩
  left_inv n := Subtype.ext (g.atoms.apply_symm_apply n.val)
  right_inv n := Subtype.ext (g.atoms.symm_apply_apply n.val)

/-- Slot permutation induced by the inverse molecular atom map, in the actual
canonical four-neighbor enumeration used by physical frame readback. -/
noncomputable def GraphMap.inverseNeighborPermutation (g : GraphMap i i)
    (c : i.certified.TetrahedralCenter) (fixed : g.atoms c.val = c.val) : Equiv.Perm (Fin 4) :=
  ((i.certified.canonicalLigandEquiv c).trans (g.inverseNeighbors c.val fixed)).trans
    (i.certified.canonicalLigandEquiv c).symm

theorem GraphMap.inverseNeighborPermutation_action (g : GraphMap i i)
    (c : i.certified.TetrahedralCenter) (fixed : g.atoms c.val = c.val) (k : Fin 4) :
    g.atoms.symm (i.certified.canonicalLigandAtom c k) =
      i.certified.canonicalLigandAtom c (g.inverseNeighborPermutation c fixed k) := by
  let d := i.certified.canonicalLigandEquiv c
  have eq := d.apply_symm_apply (g.inverseNeighbors c.val fixed (d k))
  exact (congrArg Subtype.val eq).symm

/-- Any molecular graph automorphism fixing a tetrahedral center and acting
oddly on its four physical neighbors reverses every occurrence's raw frame
hand when the actual coordinate table is reindexed. -/
theorem GraphMap.occurrence_frame_odd (g : GraphMap i i)
    (c : i.certified.TetrahedralCenter) (fixed : g.atoms c.val = c.val)
    (odd : Equiv.Perm.sign (g.inverseNeighborPermutation c fixed) = -1)
    {q : RingActivePairs.Site i} (fr : RingNestedActivePair.Frame i q) (center : fr.center = c) :
    readback? (geometry (reindexed i i g.atoms)) (fr.atoms (List.finRange 4)) =
      (readback? (geometry i.spatial) (fr.atoms (List.finRange 4))).map RS.swap :=
  occurrence_frame_inverse_odd g.atoms c (g.inverseNeighborPermutation c fixed)
    (g.inverseNeighborPermutation_action c fixed) odd fr center

end TetraStereo.Engine.RingHydrogenSpelling

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs RingActiveDistanceSchedule RingPyramidalPublication RingFrameTransport
open RingSpatialTransport RingWrittenPHReadings RingNumberedHydrogenGeometry
open RingGroupedReport (origin)
variable {i : Input}

/-- Pulling coordinates along a molecular automorphism preserves the native state at
a fixed root, even when it exchanges entire subtrees of the rooted digraph. -/
theorem GraphMap.state_at_fixed_root (g : GraphMap i i)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) (fixed : g.atoms a = a) :
    stateG i (geometry i.spatial) (origin i a) =
      stateG i (geometry (reindexed i i g.atoms)) (origin i a) := by
  let x := reindexed i i g.atoms
  let j := withSourceGeometry i i g.atoms
  have transported := RingReportRenumber.chemical_root g.atSourceGeometry admitted a
  change RingChemicalGraphProof.root i a = RingChemicalGraphProof.root j (g.atoms a) at transported
  have valid := RingRawRenumbering.AtomMap.coordinates g.atSourceGeometry admitted
  rw [fixed,←rootG_input admitted,←rootG_input valid,rootG_exact,rootG_exact,
    inputGeometry_eq i,inputGeometry_eq j] at transported
  exact transported.trans (by
    change stateG (atGeometry i x (reindexed_full g.atoms)) (geometry x) (origin (atGeometry i x (reindexed_full g.atoms)) a) = _
    rw [←reindex_origin i x (reindexed_full g.atoms) a]
    exact stateG_reindex i x (reindexed_full _) (geometry x) (origin i a))

/-- At real occurrences of a twin-bearing tetrahedral atom, both independently admitted
coordinate tables give a completed refusal, regardless of local frame orientation. -/
theorem TwinPair.stateG_at_two_tables (p : TwinPair i) (a : i.certified.TetrahedralCenter)
    (x : SpatialConfiguration) (hx : x.positions.length = size i)
    (valid : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (validX : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) = true)
    (q : Site i) (root : q.val.root = a.val) (real : q.val.node.provenance = .realAtom)
    (atParent : q.val.node.current? = some p.c.val) :
    stateG i (geometry i.spatial) q = stateG i (geometry x) q := by
  let j := atGeometry i x hx
  let q' := reindexSite i x hx q
  let p' : TwinPair j := ⟨p.c,p.u,p.v,p.distinct,p.records,p.lu,p.lv⟩
  have outside (b : i.certified.Atom) (leaf : Fintype.card (i.certified.moleculeGraph.Neighbor b) = 1) :
      q.val.root ≠ b := by
    rw [root]
    intro eq
    have four : Fintype.card (i.certified.moleculeGraph.Neighbor a.val) = 4 := (i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mp a.property
    rw [eq,leaf] at four
    contradiction
  have hu := outside _ p.supportU.degree_one
  have hv := outside _ p.supportV.degree_one
  have left := p.occurrence_refusal valid q hu hv real atParent
  have right := p'.occurrence_refusal validX q' hu hv real atParent
  rw [←stateG_input valid,inputGeometry_eq i] at left
  rw [←stateG_input validX,inputGeometry_eq j] at right
  exact left.trans (right.symm.trans (stateG_reindex i x hx (geometry x) q))



/-- Renumbering fixes the root answer, whereas an odd action reverses both hands
on an unchanged auxiliary reader. Only a completed refusal satisfies both laws. -/
private theorem GraphMap.refusal_of_frozen (g : GraphMap i i)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (c : i.certified.TetrahedralCenter) (fixed : g.atoms c.val = c.val)
    (odd : Equiv.Perm.sign (g.inverseNeighborPermutation c fixed) = -1)
    (reader : frozen (stateG i (geometry i.spatial)) (origin i c.val) =
      frozen (stateG i (geometry (reindexed i i g.atoms))) (origin i c.val)) :
    RingChemicalGraphProof.root i c.val = some none := by
  let q := origin i c.val
  let w := geometry i.spatial
  let x := geometry (reindexed i i g.atoms)
  have nonP : focusP i q = none := by
    have h := RingHydrogenLeafGeometry.notP_of_degree_four (i := i) c.val
      ((i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mp c.property)
    change (some c.val).filter (phosphorus i) = none
    simp [h]
  have flip : stateG i x q = flipCell (stateG i w q) := calc
    _ = publishG i x q (frozen (stateG i x) q) := stateG_eq i x q
    _ = publishG i x q (frozen (stateG i w) q) := congrArg _ reader.symm
    _ = flipCell (publishG i w q (frozen (stateG i w) q)) := by
      apply publishG_focus_flip nonP
      intro fr
      apply g.occurrence_frame_odd c fixed odd fr
      exact Subtype.ext (Option.some.inj
        (((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp fr.recognized).2.symm :
          some fr.center.val = some c.val))
    _ = _ := congrArg flipCell (stateG_eq i w q).symm
  have same := (g.state_at_fixed_root admitted c.val fixed).trans flip
  change stateG i (geometry i.spatial) q = flipCell (stateG i (geometry i.spatial) q) at same
  rw [←inputGeometry_eq i,stateG_input admitted] at same
  rw [RingChemicalGraphProof.root,RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i)]
  exact complete_fixed_flip (RingChemicalGraphProof.complete admitted q) same


/-- A real occurrence of an atom on a positive-length simple path from the root. -/
def BranchReachable (i : Input) (root b : i.certified.Atom) : Prop :=
  ∃ q : Site i, q.val.root = root ∧ 0 < distance q ∧
    q.val.node.provenance = .realAtom ∧ q.val.node.current? = some b

/-- A branch exchange must preserve the signed readings at other potential stereo
centers. A tetrahedral site with two chemically identical terminal neighbors is
already a proved refusal and imposes no sign condition. -/
structure BranchAgreement (i : Input) (c : i.certified.TetrahedralCenter)
    (x : SpatialConfiguration) : Prop where
  tetra : ∀ b : i.certified.TetrahedralCenter, b ≠ c → BranchReachable i c.val b.val → (¬ ∃ p : TwinPair i, p.c = b) →
    readback? (geometry i.spatial) (RingRetainedAuxiliary.canonical i.certified b) =
    readback? (geometry x) (RingRetainedAuxiliary.canonical i.certified b)
  pyramidal : ∀ a hp, BranchReachable i c.val a →
    let ids := RingPyramidalChoices.phosphorusFrameIds (phosphorusEnumeration i a hp)
    readback? (geometry i.spatial) (order ids 1) = readback? (geometry x) (order ids 1)

/-- The auxiliary stores are derived independently on the two coordinate tables. -/
theorem BranchAgreement.positive_states {c : i.certified.TetrahedralCenter} {x : SpatialConfiguration}
    (agreement : BranchAgreement i c x) (hx : x.positions.length = size i)
    (valid : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (validX : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) = true)
    (q : Site i) (on : q.val.root = c.val) (pos : 0 < distance q) :
    stateG i (geometry i.spatial) q = stateG i (geometry x) q := by
  apply stateG_positive_of_local_or_equal c.val ?_ q on pos
  intro u root positive
  by_cases twin : ∃ p : TwinPair i, u.val.node.provenance = .realAtom ∧ u.val.node.current? = some p.c.val
  · obtain ⟨p,real,atParent⟩ := twin
    exact Or.inr (p.stateG_at_two_tables c x hx valid validX u root real atParent)
  apply Or.inl
  apply siteAgree_of_canonical
  · intro fr
    obtain ⟨real,atCenter⟩ := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff u fr.center).mp fr.recognized
    apply agreement.tetra fr.center
    · intro eq
      exact positive_real_not_root u real positive (by simpa [eq,root] using atCenter)
    · exact ⟨u,root,positive,real,atCenter⟩
    · rintro ⟨p,eq⟩
      exact twin ⟨p,real,eq ▸ atCenter⟩
  · intro a focused row perm
    obtain ⟨d,eq⟩ := RingPhysicalFrameBridge.phosphorus_site_order u a focused row perm
    have hp := RingPhysicalFrameBridge.focusP_phosphorus focused
    obtain ⟨π,_,action⟩ := phosphorus_order_reindex d (phosphorusEnumeration i a hp)
    have permuted : order (RingPyramidalChoices.phosphorusFrameIds d) 1 =
        order (RingPyramidalChoices.phosphorusFrameIds (phosphorusEnumeration i a hp)) π := by
      simp only [order,Equiv.Perm.one_apply,action]
    rw [←eq,permuted]
    have visited : BranchReachable i c.val a := by
      refine ⟨u,root,positive,?_⟩
      unfold focusP at focused
      split at focused
      · exact ⟨by assumption,(Option.filter_eq_some_iff.mp focused).1⟩
      · contradiction
    exact order_readback_congr _ (agreement.pyramidal a hp visited) π

/-- An odd symmetry exchanging branches forces the native evaluator to refuse the
fixed root. The hypotheses refer only to the molecular graph and physical frame readings. -/
theorem GraphMap.odd_branch_refusal (g : GraphMap i i)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (c : i.certified.TetrahedralCenter) (fixed : g.atoms c.val = c.val)
    (odd : Equiv.Perm.sign (g.inverseNeighborPermutation c fixed) = -1)
    (hands : BranchAgreement i c (reindexed i i g.atoms)) :
    RingChemicalGraphProof.root i c.val = some none :=
  g.refusal_of_frozen admitted c fixed odd (frozen_root_of_positive c.val
    (hands.positive_states (reindexed_full g.atoms) admitted (RingRawRenumbering.AtomMap.coordinates g.atSourceGeometry admitted)))

end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.GraphMap.odd_branch_refusal

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (height distance)
open RingEligibleGraph (candidate)
open RingPyramidalPublication (eligible)
open RingFrameTransport (stateG)
open RingSpatialTransport RingNumberedHydrogenGeometry
open RingWrittenPHReadings (geometry)

private theorem candidate_positive {i : Input} (root : i.certified.Atom) (q : Site i)
    (hit : candidate (eligible i) root q) : 0 < distance q := by
  by_contra zero
  have empty : q.val.address = [] := List.length_eq_zero_iff.mp (by change distance q = 0; omega)
  have eq := RingGroupedReport.origin_unique q empty
  have current : q.val.node.current? = some root := by
    calc
      _ = (RingGroupedReport.origin i q.val.root).val.node.current? := congrArg (fun v : Site i => v.val.node.current?) eq
      _ = some root := congrArg some hit.1
  exact hit.2.1 current

/-- Positive branch-state equality under a graph automorphism implies an exact orbit
identity in one geometry's materialized addressed table after every batch. No rank or
ligand-key hypothesis is present, and absent versus stored-failed cells remain distinct. -/
theorem branch_store_orbit {i : Input} (g : GraphMap i i) (c : i.certified.TetrahedralCenter)
    (fixed : g.atoms c.val = c.val)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (branches : ∀ q : Site i, q.val.root = c.val → 0 < distance q →
      stateG i (geometry i.spatial) q = stateG i (geometry (reindexed i i g.atoms)) q)
    (k : Nat) (bound : k ≤ height i + 1) (q : Site i) :
    sphereEntry i c.val k q = sphereEntry i c.val k
      ((reindexSite i (reindexed i i g.atoms) (reindexed_full _)).symm
        (RingRawRenumbering.AtomMap.site g.atSourceGeometry q)) := by
  let x := reindexed i i g.atoms
  let j := withSourceGeometry i i g.atoms
  let E := reindexSite i x (reindexed_full _)
  have targetAdmitted : LocalizedChemicalRing.coordinatesAdmitted j = true :=
    RingRawRenumbering.AtomMap.coordinates g.atSourceGeometry admitted
  have heights : height j = height i := (RingReportRenumber.schedule_height g.atSourceGeometry).symm
  have sourceState (v : Site i) : stateG i (geometry i.spatial) v = RingChemicalGraphProof.state i v := by
    rw [← RingWrittenPHReadings.inputGeometry_eq i]
    exact congrFun (RingFrameTransport.stateG_input admitted) v
  have targetState (v : Site i) : RingChemicalGraphProof.state j (E v) = stateG i (geometry x) v := by
    rw [← RingFrameTransport.stateG_input targetAdmitted, RingWrittenPHReadings.inputGeometry_eq j]
    exact stateG_reindex i x (reindexed_full _) (geometry x) v
  have coordinates (v : Site i) : sphereEntry j c.val k (E v) = sphereEntry i c.val k v := by
    rw [sphereEntry_exact j c.val k (by rw [heights]; exact bound) (E v),
      sphereEntry_exact i c.val k bound v,heights]
    change (if candidate (eligible i) c.val v ∧ height i < distance v + k then
        some (RingChemicalGraphProof.state j (E v)) else none) = _
    split
    · rename_i written
      rw [targetState, ← branches v written.1.1 (candidate_positive c.val v written.1), sourceState]
    · rfl
  have renamed := RingReportRenumber.chemical_stored_entry g.atSourceGeometry admitted c.val k bound q
  change sphereEntry i c.val k q = sphereEntry j (g.atoms c.val) k
    (RingRawRenumbering.AtomMap.site g.atSourceGeometry q) at renamed
  rw [fixed] at renamed
  refine renamed.trans ?_
  have atImage := coordinates (E.symm (RingRawRenumbering.AtomMap.site g.atSourceGeometry q))
  rw [Equiv.apply_symm_apply] at atImage
  exact atImage

assert_kernel_only branch_store_orbit
end TetraStereo.Engine.RingHydrogenSpelling

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingSpatialTransport RingNumberedHydrogenGeometry RingWrittenPHReadings
variable {i : Input}

/-- Exchanging exactly two physical neighbors makes the inverse neighbor
permutation odd. This depends on the molecular map alone, never on ranks,
coordinate hands, or any previously computed publication. -/
theorem GraphMap.inverseNeighborPermutation_transposition_odd (g : GraphMap i i)
    (c : i.certified.TetrahedralCenter) (fixed : g.atoms c.val = c.val)
    (u v : i.certified.moleculeGraph.Neighbor c.val) (different : u ≠ v)
    (action : ∀ n : i.certified.moleculeGraph.Neighbor c.val,
      g.atoms.symm n.val = Equiv.swap u.val v.val n.val) :
    Equiv.Perm.sign (g.inverseNeighborPermutation c fixed) = -1 := by
  let d := i.certified.canonicalLigandEquiv c
  let h := d.symm u
  let k := d.symm v
  have ne : h ≠ k := d.symm.injective.ne different
  have uh : i.certified.canonicalLigandAtom c h = u.val := congrArg Subtype.val (d.apply_symm_apply u)
  have vk : i.certified.canonicalLigandAtom c k = v.val := congrArg Subtype.val (d.apply_symm_apply v)
  have permutation : g.inverseNeighborPermutation c fixed = Equiv.swap h k := by
    apply Equiv.ext
    intro t
    apply i.certified.canonicalLigandAtom_injective c
    calc
      _ = g.atoms.symm (i.certified.canonicalLigandAtom c t) :=
        (g.inverseNeighborPermutation_action c fixed t).symm
      _ = Equiv.swap u.val v.val (i.certified.canonicalLigandAtom c t) := action (d t)
      _ = i.certified.canonicalLigandAtom c (Equiv.swap h k t) := by
        rw [←uh,←vk]
        exact (i.certified.canonicalLigandAtom_injective c).swap_apply h k t
  rw [permutation]
  exact Equiv.Perm.sign_swap ne

end TetraStereo.Engine.RingHydrogenSpelling

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter RingWrittenPHReadings RingSpatialTransport RingHydrogenCompletion RingPyramidalChoices
open LocalizedChemicalRing (Input)
open RingGroupedReport (Report)

/-- Lift a native refusal in every actual written placement to the original singleton API. -/
theorem prepared_native_single_refusal {s i : Input} (a : i.certified.Atom)
    (source : LocalizedChemicalRing.coordinatesAdmitted s = true)
    (done : prepare? s.molecule s.spatial = some (i.molecule,i.spatial))
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (original : a.val < s.molecule.atomCount)
    (native : ∀ (y : SpatialConfiguration) (p : Placement s.molecule s.spatial i.molecule i.spatial y),
      RingChemicalGraphProof.root (atGeometry i y (p.full.trans (full_original i))) a = some none) :
    RingHydrogenReport.fromRaw? s.molecule s.spatial [a.val] = some [(a.val,none)] := by
  apply fromRaw_of_all_written (readmit s) source done _ (by simpa using original)
  intro y placement
  let hy := placement.full.trans (full_original i)
  let j := atGeometry i y hy
  have same := coordinates_of_same_ligands (i := i) hy fun c k =>
    placement.fixed _ (centers_unmoved (prepare?_certified done) i rfl c k)
  change RingHydrogenReport.fromRaw? j.molecule j.spatial [a.val] = some [(a.val,none)]
  apply (fromRaw_closed_report j (prepare?_closed done) (same.trans admitted) [a]).trans
  simp only [RingChemicalReport.report?,List.mapM_cons,List.mapM_nil]
  change ((RingChemicalGraphProof.root j a).map (fun l => (a.val,l))).bind
    (fun row => some [row]) = some [(a.val,none)]
  rw [native y placement]
  rfl

end TetraStereo.Engine.RingHydrogenSpelling


namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingSpatialTransport RingNumberedHydrogenGeometry RingHydrogenCompletion RingWrittenPHReadings
open RingActivePairs RingActiveDistanceSchedule
variable {i : Input}

/-- Every auxiliary orbit in the original public store is constant after each
batch. The graph action can permute the addresses of nonterminal branches. -/
theorem GraphMap.branch_stores (g : GraphMap i i)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (c : i.certified.TetrahedralCenter) (fixed : g.atoms c.val = c.val)
    (hands : BranchAgreement i c (reindexed i i g.atoms))
    (k : Nat) (bound : k ≤ height i + 1) (q : Site i) :
    sphereEntry i c.val k q = sphereEntry i c.val k
      ((reindexSite i (reindexed i i g.atoms) (reindexed_full _)).symm
        (RingRawRenumbering.AtomMap.site g.atSourceGeometry q)) :=
  branch_store_orbit g c fixed admitted
    (hands.positive_states (reindexed_full g.atoms) admitted (RingRawRenumbering.AtomMap.coordinates g.atSourceGeometry admitted))
    k bound q

/-- Graph-only sufficient conditions. Such a molecule has no auxiliary center
whose determinant must be compared in order to establish the refusal. -/
structure BranchesWithTwinCenters (i : Input) (c : i.certified.TetrahedralCenter) : Prop where
  other : ∀ b : i.certified.TetrahedralCenter, b ≠ c → ∃ p : TwinPair i, p.c = b
  noP : ∀ a, RingPyramidalPublication.phosphorus i a = false

theorem BranchesWithTwinCenters.atGeometry {c : i.certified.TetrahedralCenter}
    (sites : BranchesWithTwinCenters i c) (y : SpatialConfiguration) (hy : y.positions.length = size i) :
    BranchesWithTwinCenters (RingSpatialTransport.atGeometry i y hy) c := by
  refine ⟨?_,sites.noP⟩
  intro b other
  obtain ⟨p,equal⟩ := sites.other b other
  exact ⟨⟨p.c,p.u,p.v,p.distinct,p.records,p.lu,p.lv⟩,equal⟩

theorem BranchesWithTwinCenters.agreement {c : i.certified.TetrahedralCenter}
    (sites : BranchesWithTwinCenters i c) (x : SpatialConfiguration) : BranchAgreement i c x := by
  refine ⟨fun b diff _ no => (no (sites.other b diff)).elim,?_⟩
  intro a hp
  rw [sites.noP a] at hp
  contradiction

/-- On this graph class, an odd root action forces a refusal at every admitted
geometry, including geometries with independent orientations at other centers. -/
theorem GraphMap.graph_only_refusal (g : GraphMap i i) (c : i.certified.TetrahedralCenter)
    (sites : BranchesWithTwinCenters i c) (fixed : g.atoms c.val = c.val)
    (odd : Equiv.Perm.sign (g.inverseNeighborPermutation c fixed) = -1)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    RingChemicalGraphProof.root i c.val = some none :=
  g.odd_branch_refusal admitted c fixed odd (sites.agreement _)

/-- The raw singleton preserves a whole-branch refusal when the signed readings
satisfy the branch criterion in every placement considered by the public API. -/
theorem GraphMap.prepared_stereo_branch_refusal {s : Input} (g : GraphMap i i)
    (c : i.certified.TetrahedralCenter) (fixed : g.atoms c.val = c.val)
    (u v : i.certified.moleculeGraph.Neighbor c.val) (distinct : u ≠ v)
    (action : ∀ n : i.certified.moleculeGraph.Neighbor c.val, g.atoms.symm n.val = Equiv.swap u.val v.val n.val)
    (source : LocalizedChemicalRing.coordinatesAdmitted s = true)
    (done : prepare? s.molecule s.spatial = some (i.molecule,i.spatial))
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (original : c.val.val < s.molecule.atomCount)
    (hands : ∀ y (p : RingWrittenPHReadings.Placement s.molecule s.spatial i.molecule i.spatial y),
      let j := atGeometry i y (p.full.trans (full_original i))
      BranchAgreement j c (reindexed j j g.atoms)) :
    RingHydrogenReport.fromRaw? s.molecule s.spatial [c.val.val] = some [(c.val.val,none)] := by
  apply prepared_native_single_refusal c.val source done admitted original
  intro y placement
  let hy := placement.full.trans (full_original i)
  let g' := g.atTables y y hy hy
  have same := coordinates_of_same_ligands (i := i) hy fun b k =>
    placement.fixed _ (centers_unmoved (prepare?_certified done) i rfl b k)
  exact g'.odd_branch_refusal (same.trans admitted) c fixed
    (g'.inverseNeighborPermutation_transposition_odd c fixed u v distinct action) (hands y placement)

/-- An exchange of two whole branches on the prepared graph suffices for the raw
original-ID query across all generated placements, with no coordinate symmetry premise. -/
theorem GraphMap.prepared_branch_refusal {s : Input} (g : GraphMap i i)
    (c : i.certified.TetrahedralCenter) (sites : BranchesWithTwinCenters i c)
    (fixed : g.atoms c.val = c.val)
    (u v : i.certified.moleculeGraph.Neighbor c.val) (distinct : u ≠ v)
    (action : ∀ n : i.certified.moleculeGraph.Neighbor c.val, g.atoms.symm n.val = Equiv.swap u.val v.val n.val)
    (source : LocalizedChemicalRing.coordinatesAdmitted s = true)
    (done : prepare? s.molecule s.spatial = some (i.molecule,i.spatial))
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (original : c.val.val < s.molecule.atomCount) :
    RingHydrogenReport.fromRaw? s.molecule s.spatial [c.val.val] = some [(c.val.val,none)] := by
  apply g.prepared_stereo_branch_refusal c fixed u v distinct action source done admitted original
  intro y placement
  exact (sites.atGeometry y (placement.full.trans (full_original i))).agreement _

end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.GraphMap.branch_stores
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.GraphMap.prepared_branch_refusal

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingNumberedHydrogenGeometry RingWrittenPHReadings
variable {i : Input}

/-- An independently inspectable signed frame that prevents the proposed graph
symmetry from preserving the stereochemistry of the other branches. -/
inductive BranchDifference (i : Input) (c : i.certified.TetrahedralCenter)
    (x : SpatialConfiguration) : Prop where
  | tetra (b : i.certified.TetrahedralCenter) (away : b ≠ c) (reachable : BranchReachable i c.val b.val)
      (noTwins : ¬ ∃ p : TwinPair i, p.c = b)
      (changed : readback? (geometry i.spatial) (RingRetainedAuxiliary.canonical i.certified b) ≠
        readback? (geometry x) (RingRetainedAuxiliary.canonical i.certified b))
  | pyramidal (a : i.certified.Atom) (eligible : RingPyramidalPublication.phosphorus i a = true)
      (reachable : BranchReachable i c.val a)
      (changed : let ids := RingPyramidalChoices.phosphorusFrameIds (phosphorusEnumeration i a eligible)
        readback? (geometry i.spatial) (order ids 1) ≠ readback? (geometry x) (order ids 1))

theorem branchDifference_iff {c : i.certified.TetrahedralCenter} {x : SpatialConfiguration} :
    BranchDifference i c x ↔ ¬ BranchAgreement i c x := by
  classical
  constructor
  · intro witness same
    cases witness with
    | tetra b away reachable noTwins changed => exact changed (same.tetra b away reachable noTwins)
    | pyramidal a hp reachable changed => exact changed (same.pyramidal a hp reachable)
  · intro fail
    by_contra no
    apply fail
    constructor
    · intro b away reachable noTwins
      by_contra changed
      exact no (.tetra b away reachable noTwins changed)
    · intro a hp reachable
      by_contra changed
      exact no (.pyramidal a hp reachable changed)

/-- Any actual assignment at an oddly stabilized root identifies an off-root
physical reading discrepancy at a reachable center. A change confined to twin-bearing centers cannot be the witness. -/
theorem GraphMap.assignment_forces_branch_difference (g : GraphMap i i)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (c : i.certified.TetrahedralCenter) (fixed : g.atoms c.val = c.val)
    (odd : Equiv.Perm.sign (g.inverseNeighborPermutation c fixed) = -1)
    {labels : RingNestedActivePair.Labels} (assigned : RingChemicalGraphProof.root i c.val = some (some labels)) :
    BranchDifference i c (reindexed i i g.atoms) := by
  apply branchDifference_iff.mpr
  intro same
  rw [g.odd_branch_refusal admitted c fixed odd same] at assigned
  cases assigned
end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.GraphMap.assignment_forces_branch_difference

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter RingWrittenPHReadings RingHydrogenCompletion RingPyramidalChoices
open LocalizedChemicalRing (Input)
open RingGroupedReport (Report)

/-- The source, original IDs, and all prepared coordinate tables pass the public
admission checks. This condition contains no priority comparison or descriptor. -/
def PlacementAdmission (m : RawMolecule) (xyz : SpatialConfiguration) (ids : List Nat) : Prop :=
  ∃ (s : Input) (out : RawMolecule) (pos : SpatialConfiguration),
    LocalizedChemicalRing.admitRawSpatial? m xyz = some s ∧ LocalizedChemicalRing.coordinatesAdmitted s = true ∧
    (∀ n ∈ ids, n < m.atomCount) ∧ prepare? m xyz = some (out,pos) ∧
    ∀ y, Placement m xyz out pos y → ∃ j : Input, LocalizedChemicalRing.admitRawSpatial? out y = some j ∧
      LocalizedChemicalRing.coordinatesAdmitted j = true

/-- Matching physical predictions on the actual prepared placements determine the public report,
including its domain, atom order and duplicates. -/
theorem raw_labels_iff_admission (m : RawMolecule) (xyz : SpatialConfiguration) (ids : List Nat)
    (labels : Nat → Option RingNestedActivePair.Labels)
    (roots : ∀ (out : RawMolecule) (pos : SpatialConfiguration), prepare? m xyz = some (out,pos) →
      ∀ (y : SpatialConfiguration), Placement m xyz out pos y → ∀ (j : Input),
      LocalizedChemicalRing.admitRawSpatial? out y = some j → LocalizedChemicalRing.coordinatesAdmitted j = true →
      ∀ a : j.certified.Atom, a.val ∈ ids → RingChemicalGraphProof.root j a = some (labels a.val))
    (rows : Report) :
    RingHydrogenReport.fromRaw? m xyz ids = some rows ↔
      PlacementAdmission m xyz ids ∧ rows = ids.map (fun n => (n,labels n)) := by
  have computed {out : RawMolecule} {pos y : SpatialConfiguration} (done : prepare? m xyz = some (out,pos))
      (p : Placement m xyz out pos y) (bounds : ∀ n ∈ ids, n < m.atomCount) (j : Input) (hj : LocalizedChemicalRing.admitRawSpatial? out y = some j)
      (ok : LocalizedChemicalRing.coordinatesAdmitted j = true) :
      RingHydrogenReport.fromRaw? out y ids = some (ids.map fun n => (n,labels n)) := by
    obtain ⟨hm,hg⟩ := RingChemicalReport.admission_fields hj
    rw [←hm,←hg]
    apply raw_of_root_labels j labels (hm ▸ prepare?_closed done) ok ids
    · intro n member
      rw [hm]
      exact (bounds n member).trans_le (prepare?_certified done).atomCount_le
    · exact roots out pos done y p j hj ok
  constructor
  · intro got
    obtain ⟨s,out,pos,hs,source,bounds,done,_⟩ := (fromRaw_iff_written_population ..).mp got
    have actual := (fromRaw_all_placements hs source done ids bounds rows).mp got
    have accepts (y : SpatialConfiguration) (p : Placement m xyz out pos y) :
        ∃ j : Input, LocalizedChemicalRing.admitRawSpatial? out y = some j ∧
          LocalizedChemicalRing.coordinatesAdmitted j = true := by
      have result := actual y p
      rw [RingHydrogenReport.fromRaw_closed_eq (prepare?_closed done)] at result
      obtain ⟨j,hj,_,_,prepared,_⟩ := (RingChemicalReport.fromRaw_graph_iff ..).mp result
      exact ⟨j,hj,prepared.1⟩
    refine ⟨⟨s,out,pos,hs,source,bounds,done,accepts⟩,?_⟩
    obtain ⟨ps,hps⟩ := choices_exists (sites m xyz out pos) pos.positions
    let y : SpatialConfiguration := ⟨ps⟩
    have p : Placement m xyz out pos y := variant_placement (prepare?_certified done) (List.mem_map.mpr ⟨ps,hps,rfl⟩)
    obtain ⟨j,hj,ok⟩ := accepts y p
    exact Option.some.inj ((actual y p).symm.trans (computed done p bounds j hj ok))
  · rintro ⟨⟨s,out,pos,hs,source,bounds,done,accepts⟩,rfl⟩
    apply fromRaw_of_all_written hs source done ids bounds
    intro y p
    obtain ⟨j,hj,ok⟩ := accepts y p
    exact computed done p bounds j hj ok

/-- When every requested prepared root refuses, the exact public result is
determined by independent admission checks and the original ordered request. -/
theorem raw_refusals_iff_admission (m : RawMolecule) (xyz : SpatialConfiguration) (ids : List Nat)
    (roots : ∀ (out : RawMolecule) (pos : SpatialConfiguration), prepare? m xyz = some (out,pos) →
      ∀ (j : Input), j.molecule = out → LocalizedChemicalRing.coordinatesAdmitted j = true →
      ∀ a : j.certified.Atom, a.val ∈ ids → RingChemicalGraphProof.root j a = some none)
    (rows : Report) :
    RingHydrogenReport.fromRaw? m xyz ids = some rows ↔
      PlacementAdmission m xyz ids ∧ rows = ids.map (fun n => (n,none)) := by
  apply raw_labels_iff_admission m xyz ids (fun _ => none)
  intro out pos done y _ j hj valid
  exact roots out pos done j (RingChemicalReport.admission_fields hj).1 valid

end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.raw_refusals_iff_admission
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.raw_labels_iff_admission
