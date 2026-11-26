import TetraStereo.Engine.RingHydrogenPairMotion

/-! A tetrahedral atom with two identical terminal ligands receives a completed
refusal from the native chemical root and the public raw report. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingFrameTransport
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader Labels)
open RingActivePairReport (Slot)
open RingActiveDistanceSchedule (Cell View)
open RingRetainedChemicalTrace (Word)
open RingFullPathEligibility (Key)

/-- Complement both physical hands while retaining uppercase/lowercase classification. -/
def flipLabels (labels : Labels) : Labels := (labels.1.swap,labels.2.swap)
def flipCell (cell : Cell) : Cell := cell.map (Option.map flipLabels)

/-- A written-frame sign reversal reverses every priority order, including ties/absence. -/
theorem frame_hand_flip {i : Input} {f : Site i} (fr : Frame i f) {g g' : Geometry}
    (flipped : readback? g' (fr.atoms (List.finRange 4)) =
      (readback? g (fr.atoms (List.finRange 4))).map RS.swap)
    (row : List Slot) (perm : row.Perm (List.finRange 4)) :
    readback? g' (fr.atoms row) = (readback? g (fr.atoms row)).map RS.swap := by
  rw [RingOrientation.frame_read fr g' ⟨row,perm⟩,RingOrientation.frame_read fr g ⟨row,perm⟩,flipped]
  cases RingJointObservations.parity ⟨row,perm⟩ <;> rfl

theorem readTrialG_flip {i : Input} {f : Site i} (fr : Frame i f) {g g' : Geometry}
    (flipped : readback? g' (fr.atoms (List.finRange 4)) =
      (readback? g (fr.atoms (List.finRange 4))).map RS.swap)
    (w : Slot → List (List Word)) :
    readTrialG fr g' w = (readTrialG fr g w).map RS.swap := by
  unfold readTrialG
  split
  · exact frame_hand_flip fr flipped _ (RingStereoSiblingPass.legal_order w (List.finRange 4)).perm
  · rfl

def flipTrialRow (row : Option Slot × Option RS) := (row.1,row.2.map RS.swap)

theorem readingsWithG_flip {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (read read' : (Slot → List (List Word)) → Option RS)
    (flipped : ∀ w, read' w = (read w).map RS.swap) (ks : Slot → Key) :
    readingsWithG fr r read' ks = (readingsWithG fr r read ks).map (List.map flipTrialRow) := by
  unfold readingsWithG
  rw [← RingSpatialTransport.mapM_option_map]
  apply mapM_congr_mem
  intro s _
  cases words : RingFullPathTrialReadings.markWords? fr r s <;> simp [flipped,flipTrialRow]

theorem readingsG_flip {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (read read' : (Slot → List (List Word)) → Option RS)
    (flipped : ∀ w, read' w = (read w).map RS.swap) :
    readingsG fr r read' = (readingsG fr r read).map (List.map flipTrialRow) := by
  unfold readingsG
  cases keys : RingActivePairReport.four? (fun k => RingFullPathEligibility.key? i r false (RingGroupedCentre.cursor fr k)) with
  | none => rfl
  | some ks => exact readingsWithG_flip fr r read read' flipped ks

/-- Signed aggregation is odd; reversal parity and therefore uppercase/lowercase casing stay fixed. -/
theorem letters_flip (ks ms : Slot → Key) (hands : List (Option RS)) :
    RingFullPathPublication.letters ks ms (hands.map (Option.map RS.swap)) =
      (RingFullPathPublication.letters ks ms hands).map flipLabels := by
  unfold RingFullPathPublication.letters
  rw [LocalizedChemicalRingPromotionAggregation.readingBalance_swap,
    RingChemicalPriority.ReferenceFrame.survivingHand_neg]
  simp only [Option.map_map]
  apply congrArg (fun f => (RingChemicalPriority.ReferenceFrame.survivingHand
    (LocalizedChemicalRingPromotionAggregation.readingBalance hands)).map f)
  funext h
  by_cases even : RingFullPathPublication.reversals ks ms % 2 = 0 <;>
    cases h <;> simp [even,flipLabels,RingNestedActivePair.label,RS.swap,pseudoRSOfRS,
      LocalizedTetrahedralRSPseudoDescriptor.swap]

theorem centreG_flip {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (read read' : (Slot → List (List Word)) → Option RS)
    (flipped : ∀ w, read' w = (read w).map RS.swap) :
    centreG fr r read' = flipCell (centreG fr r read) := by
  unfold centreG
  rw [readingsG_flip fr r read read' flipped]
  cases RingFullPathPublication.keys? fr r false <;> cases RingFullPathPublication.keys? fr r true <;>
    cases readingsG fr r read <;> simp [flipCell,List.map_map,Function.comp_def,
      flipTrialRow,← letters_flip]

/-- Focus-only sign covariance of the actual non-P publisher on the same reader.
No state equality, coordinate admission or leaf-swap hypothesis is used. -/
theorem publishG_focus_flip {i : Input} {g g' : Geometry} {q : Site i}
    (nonP : RingPyramidalPublication.focusP i q = none)
    (flipped : ∀ fr : Frame i q, readback? g' (fr.atoms (List.finRange 4)) =
      (readback? g (fr.atoms (List.finRange 4))).map RS.swap) (r : View i) :
    publishG i g' q r = flipCell (publishG i g q r) := by
  rw [publishG_tetra g' nonP r,publishG_tetra g nonP r]
  cases found : RingNestedActivePair.frame? i q with
  | none => simp [tetraG,found,flipCell]
  | some fr =>
    rw [tetraG_centre g' found r,tetraG_centre g found r]
    exact centreG_flip fr r _ _ (readTrialG_flip fr (flipped fr))

assert_kernel_only publishG_focus_flip
end TetraStereo.Engine.RingFrameTransport

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingGraphPaths (Path)
open RingHydrogenLeafGeometry (SupportedLeaf)
open RingSpatialTransport RingNumberedHydrogenGeometry

private theorem path_current_mem {i : Input} {root current : i.certified.Atom}
    {history : List i.certified.Atom} (path : Path i root history current) : current ∈ history := by
  cases path <;> simp

private theorem path_leaf_parent_mem {i : Input} {root leaf parent : i.certified.Atom}
    {history : List i.certified.Atom} (support : SupportedLeaf i leaf parent)
    (path : Path i root history leaf) (offRoot : root ≠ leaf) : parent ∈ history := by
  cases path with
  | origin => exact False.elim (offRoot rfl)
  | @step history current next prior bond fresh =>
    have previous : current = parent := (support current).mp (i.certified.moleculeGraph.adj_symm.mp bond)
    exact List.mem_cons_of_mem _ (previous ▸ path_current_mem prior)

/-- A simple path whose two endpoints avoid a terminal leaf cannot visit that leaf internally. -/
theorem path_avoids_terminal_leaf {i : Input} {root current leaf parent : i.certified.Atom}
    {history : List i.certified.Atom} (support : SupportedLeaf i leaf parent)
    (path : Path i root history current) (offRoot : root ≠ leaf) (offCurrent : current ≠ leaf) :
    leaf ∉ history := by
  induction path with
  | origin => simpa using offRoot.symm
  | @step history current next prior bond fresh ih =>
    intro member
    rcases List.mem_cons.mp member with same | old
    · exact offCurrent same.symm
    · by_cases currentOff : current ≠ leaf
      · exact ih currentOff old
      · have same : current = leaf := by simpa using currentOff
        subst current
        have previous := path_leaf_parent_mem support prior offRoot
        have returns : next = parent := (support next).mp bond
        exact fresh (returns ▸ previous)

/-- At every real occurrence with both endpoints off the two terminal ligands,
the graph automorphism and the pure coordinate reindexing select exactly the same address. -/
theorem twin_fixed_occurrence {i : Input} (p : TwinPair i) (q : Site i)
    (real : q.val.node.provenance = .realAtom) (a : i.certified.Atom)
    (current : q.val.node.current? = some a)
    (rootU : q.val.root ≠ p.u) (rootV : q.val.root ≠ p.v)
    (atomU : a ≠ p.u) (atomV : a ≠ p.v) :
    RingRawRenumbering.AtomMap.site
      (twinSwap p.u p.v p.c.val p.records p.lu p.lv).atSourceGeometry q =
      reindexSite i (reindexed i i (Equiv.swap p.u p.v)) (reindexed_full _) q := by
  obtain ⟨b,found,path⟩ := RingGraphPaths.site_path q real
  have same : b = a := Option.some.inj (found.symm.trans current)
  subst b
  have noU := path_avoids_terminal_leaf p.supportU path rootU atomU
  have noV := path_avoids_terminal_leaf p.supportV path rootV atomV
  have history : q.val.node.history.map (Equiv.swap p.u p.v) = q.val.node.history := by
    calc
      _ = q.val.node.history.map id := by
        apply List.map_congr_left
        intro v member
        exact Equiv.swap_apply_of_ne_of_ne (fun eq => noU (eq ▸ member)) (fun eq => noV (eq ▸ member))
      _ = _ := List.map_id _
  apply RingGraphPaths.unique_site
    (i := atGeometry i (reindexed i i (Equiv.swap p.u p.v)) (reindexed_full _))
    (r := q.val.root) (h := q.val.node.history) (a := a)
  · refine ⟨?_,?_,?_,?_⟩
    · exact Equiv.swap_apply_of_ne_of_ne rootU rootV
    · exact history
    · exact real
    · change q.val.node.current?.map (Equiv.swap p.u p.v) = some a
      rw [current,Option.map_some,Equiv.swap_apply_of_ne_of_ne atomU atomV]
  · exact ⟨rfl,rfl,real,current⟩

end TetraStereo.Engine.RingHydrogenSpelling

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingSpatialTransport RingNumberedHydrogenGeometry RingWrittenPHReadings RingFrameTransport
open RingGroupedReport (origin)
open LocalizedChemicalRing (Input)
variable {i : Input}

/-- Coordinate-level odd-frame law. A supplied inverse atom action on the
canonical physical neighbors is enough; no twin or leaf hypothesis is used. -/
theorem occurrence_frame_inverse_odd (e : Equiv.Perm i.certified.Atom)
    (c : i.certified.TetrahedralCenter) (σ : Equiv.Perm (Fin 4))
    (action : ∀ k, e.symm (i.certified.canonicalLigandAtom c k) =
      i.certified.canonicalLigandAtom c (σ k))
    (odd : Equiv.Perm.sign σ = -1) {q : RingActivePairs.Site i}
    (fr : RingNestedActivePair.Frame i q) (center : fr.center = c) :
    readback? (geometry (reindexed i i e)) (fr.atoms (List.finRange 4)) =
      (readback? (geometry i.spatial) (fr.atoms (List.finRange 4))).map RS.swap := by
  let ids := i.certified.canonicalLigandAtom c
  let ns := fun j => (ids j).val
  have point (j : Fin 4) : geometry (reindexed i i e) (ns j) = geometry i.spatial (ns (σ j)) :=
    (reindexed_lookup e (ids j)).trans
      (congrArg (fun a : i.certified.Atom => i.spatial.positions[a.val]?) (action j))
  have perm : (Rule6HandednessSemantics.finFourPermutationList σ).Perm [0,1,2,3] :=
    Rule6HandednessSemantics.finFourPermutationList_perm_range σ
  have oddBoolean := (Rule6HandednessSemantics.finFourPermutationIsOdd_iff_sign_negOne σ).mpr odd
  have base := LocalizedMarkedConfigurationTransport.reordered_readback_partial (geometry i.spatial) ns _ perm
  rw [LocalizedMarkedFrameCalibration.select_permutation,oddBoolean] at base
  have reflected : readback? (geometry (reindexed i i e)) (order ns 1) =
      readback? (mirror (geometry i.spatial)) (order ns 1) := by
    rw [readback_mirror]
    calc
      _ = readback? (geometry i.spatial) [ns (σ 0),ns (σ 1),ns (σ 2),ns (σ 3)] := by
        simp only [order,Equiv.Perm.one_apply,readback?,List.mapM_cons,List.mapM_nil,point]
      _ = _ := base
  have physical : fr.ids.Perm ((List.finRange 4).map ns) := by
    simpa only [RingRetainedAuxiliary.canonical,center] using fr.physical
  obtain ⟨π,row⟩ := RingPhysicalFrameBridge.written_frame_order fr.ids
    (by simpa using physical.length_eq.symm) ns
    (fun _ _ h => i.certified.canonicalLigandAtom_injective c (Fin.ext h)) physical
  change fr.atoms (List.finRange 4) = order ns π at row
  rw [row,←readback_mirror]
  exact order_readback_congr ns reflected π

/-- Exchanging the points of two terminal ligands negates the physical reading of
every order of the parent frame. No auxiliary priorities or published labels enter. -/
theorem TwinPair.occurrence_frame_swap (p : TwinPair i) {q : RingActivePairs.Site i}
    (fr : RingNestedActivePair.Frame i q) (center : fr.center = p.c) :
    readback? (geometry (reindexed i i (Equiv.swap p.u p.v))) (fr.atoms (List.finRange 4)) =
      (readback? (geometry i.spatial) (fr.atoms (List.finRange 4))).map RS.swap := by
  let ids := i.certified.canonicalLigandAtom p.c
  let e := Equiv.swap p.u p.v
  let d := tetraEnumeration i p.c
  obtain ⟨h,hu⟩ := d.surjective ⟨p.u,i.certified.moleculeGraph.adj_symm.mpr ((p.supportU _).mpr rfl)⟩
  obtain ⟨k,hv⟩ := d.surjective ⟨p.v,i.certified.moleculeGraph.adj_symm.mpr ((p.supportV _).mpr rfl)⟩
  have u : ids h = p.u := congrArg Subtype.val hu
  have v : ids k = p.v := congrArg Subtype.val hv
  have ne : h ≠ k := fun same => p.distinct (u.symm.trans ((congrArg ids same).trans v))
  let σ := Equiv.swap h k
  have swap (j : Fin 4) : e.symm (ids j) = ids (σ j) := by
    change Equiv.swap p.u p.v (ids j) = _
    rw [←u,←v]
    exact (i.certified.canonicalLigandAtom_injective p.c).swap_apply h k j
  exact occurrence_frame_inverse_odd e p.c σ swap (Equiv.Perm.sign_swap ne) fr center

end TetraStereo.Engine.RingHydrogenSpelling

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter RingFrameTransport RingSpatialTransport RingWrittenPHReadings RingNumberedHydrogenGeometry
open RingActivePairs RingActiveDistanceSchedule RingRawRenumbering
open LocalizedChemicalRing (Input)
variable {i : Input}

theorem TwinPair.stateG_of_fixed_site (p : TwinPair i)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i)
    (fixed : AtomMap.site (twinSwap p.u p.v p.c.val p.records p.lu p.lv).atSourceGeometry q =
      reindexSite i (reindexed i i (Equiv.swap p.u p.v)) (reindexed_full _) q) :
    stateG i (geometry i.spatial) q = stateG i (geometry (reindexed i i (Equiv.swap p.u p.v))) q := by
  let g := twinSwap p.u p.v p.c.val p.records p.lu p.lv
  let x := reindexed i i g.atoms
  let j := withSourceGeometry i i g.atoms
  have gj := AtomMap.coordinates g.atSourceGeometry admitted
  have native := RingReportRenumber.publications g.atSourceGeometry admitted q
  change RingChemicalGraphProof.state i q = RingChemicalGraphProof.state j (AtomMap.site g.atSourceGeometry q) at native
  rw [fixed,←stateG_input admitted,←stateG_input gj,inputGeometry_eq i,inputGeometry_eq j] at native
  exact native.trans (stateG_reindex i x (reindexed_full _) (geometry x) q)

end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.TwinPair.stateG_of_fixed_site

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingActivePairs RingActiveDistanceSchedule RingPyramidalPublication RingFrameTransport
open RingWrittenPHReadings RingNumberedHydrogenGeometry RingSpatialTransport
open LocalizedChemicalRing (Input)
open RingGroupedReport (origin)
variable {i : Input}

/-- At a root outside the exchanged leaves, all recursive cells are invariant
at their original occurrence addresses. Active paths avoid the two terminal leaves. -/
theorem TwinPair.stateG_swap_off_leaves (p : TwinPair i) (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) (rootU : q.val.root ≠ p.u) (rootV : q.val.root ≠ p.v) :
    stateG i (geometry i.spatial) q = stateG i (geometry (reindexed i i (Equiv.swap p.u p.v))) q := by
  by_cases active : RingEligibleGraph.Eligible (eligible i) q
  · obtain ⟨real,a,current,on⟩ := active
    have diff (b : i.certified.Atom) (one : Fintype.card (i.certified.moleculeGraph.Neighbor b) = 1) : a ≠ b := by
      rintro rfl
      rw [LeafAllRequests.terminal_ineligible i a one] at on
      contradiction
    exact p.stateG_of_fixed_site admitted q (twin_fixed_occurrence p q real a current rootU rootV
      (diff p.u p.supportU.degree_one) (diff p.v p.supportV.degree_one))
  · have off (g : Geometry) : stateG i g q = some none := (stateG_eq i g q).trans (skipsG i g q _ active)
    exact (off _).trans (off _).symm

/-- A completed cell fixed by exchanging both physical hands is a refusal. -/
theorem complete_fixed_flip {cell : Cell} (complete : cell.isSome = true)
    (fixed : cell = flipCell cell) : cell = some none := by
  obtain ⟨value,hv⟩ := Option.isSome_iff_exists.mp complete
  rw [hv] at fixed ⊢
  cases value with
  | none => rfl
  | some pair =>
    have bad := congrArg Prod.fst (Option.some.inj (Option.some.inj fixed))
    rcases pair with ⟨first,second⟩
    change first = first.swap at bad
    cases first with
    | chiral h => cases h <;> cases bad
    | pseudoasymmetric h => cases h <;> cases bad

/-- Every real visit to the parent, from any root other than the two leaves,
publishes a completed refusal. All frozen reader equalities are derived from the graph. -/
theorem TwinPair.occurrence_refusal (p : TwinPair i) (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) (rootU : q.val.root ≠ p.u) (rootV : q.val.root ≠ p.v)
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some p.c.val) :
    RingChemicalGraphProof.state i q = some none := by
  let w := geometry i.spatial
  let x := geometry (reindexed i i (Equiv.swap p.u p.v))
  have same := p.stateG_swap_off_leaves admitted q rootU rootV
  have frozenEq : frozen (stateG i w) q = frozen (stateG i x) q :=
    frozen_congr q (fun u vis => p.stateG_swap_off_leaves admitted u (vis.1 ▸ rootU) (vis.1 ▸ rootV))
  have no := RingHydrogenLeafGeometry.notP_of_degree_four (i := i) p.c.val
    ((i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mp p.c.property)
  have nonP : focusP i q = none := by simp [focusP,real,current,no]
  have rev : stateG i x q = flipCell (stateG i w q) := calc
    _ = publishG i x q (frozen (stateG i x) q) := stateG_eq i x q
    _ = publishG i x q (frozen (stateG i w) q) := congrArg _ frozenEq.symm
    _ = flipCell (publishG i w q (frozen (stateG i w) q)) := by
      apply publishG_focus_flip nonP
      intro fr
      apply p.occurrence_frame_swap fr
      exact Subtype.ext (Option.some.inj
        (((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp fr.recognized).2.symm.trans current))
    _ = _ := congrArg flipCell (stateG_eq i w q).symm
  have fixed : stateG i w q = flipCell (stateG i w q) := same.trans rev
  change stateG i (geometry i.spatial) q = flipCell (stateG i (geometry i.spatial) q) at fixed
  rw [←inputGeometry_eq i,stateG_input admitted] at fixed
  exact complete_fixed_flip (RingChemicalGraphProof.complete admitted q) fixed

/-- In the actual materialized table the parent is absent before its batch and has a
stored refusal after it. Root occurrences remain excluded from their own auxiliary queue. -/
theorem TwinPair.sphere_refusal (p : TwinPair i) (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1) (q : Site i)
    (on : q.val.root = root) (rootU : root ≠ p.u) (rootV : root ≠ p.v)
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some p.c.val) :
    sphereEntry i root k q = if p.c.val ≠ root ∧ height i < distance q + k
      then some (some none) else none := by
  have four : Fintype.card (i.certified.moleculeGraph.Neighbor p.c.val) = 4 :=
    (i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mp p.c.property
  have active : RingEligibleGraph.Eligible (eligible i) q := ⟨real,p.c.val,current,by simp [eligible,four]⟩
  rw [sphereEntry_exact i root k bound q,p.occurrence_refusal admitted q (on ▸ rootU) (on ▸ rootV) real current]
  simp only [RingEligibleGraph.candidate,on,true_and,current,ne_eq,Option.some.injEq,active,and_true]

/-- The native full-path evaluator completes a refusal at the parent itself. -/
theorem TwinPair.root_refusal (p : TwinPair i) (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    RingChemicalGraphProof.root i p.c.val = some none := by
  have different (a : i.certified.Atom) (one : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 1) : p.c.val ≠ a := by
    intro eq
    have four : Fintype.card (i.certified.moleculeGraph.Neighbor p.c.val) = 4 :=
      (i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mp p.c.property
    rw [eq,one] at four
    contradiction
  rw [RingChemicalGraphProof.root,RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i)]
  exact p.occurrence_refusal admitted (origin i p.c.val)
    (different p.u p.supportU.degree_one) (different p.v p.supportV.degree_one) rfl rfl

end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.TwinPair.sphere_refusal

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter RingWrittenPHReadings RingSpatialTransport
open LocalizedChemicalRing (Input)
variable {i : Input}

/-- The public raw report emits an ordinary refusal row at the original ID. -/
theorem TwinPair.raw_refusal (p : TwinPair i) (closed : RingHydrogenCompletion.plan i.molecule = [])
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial [p.c.val.val] = some [(p.c.val.val,none)] := by
  rw [show [p.c.val.val] = [p.c.val].map Fin.val from rfl,fromRaw_closed_report i closed admitted]
  simp only [RingChemicalReport.report?,List.mapM_cons,List.mapM_nil]
  change ((RingChemicalGraphProof.root i p.c.val).map (fun l => (p.c.val.val,l))).bind
    (fun row => some [row]) = some [(p.c.val.val,none)]
  rw [p.root_refusal admitted]
  rfl

/-- A refusal on a completed graph survives actual implicit-H preparation and every
P–H placement in the original raw query, with its original atom number. -/
theorem TwinPair.prepared_refusal {s : Input} (p : TwinPair i)
    (source : LocalizedChemicalRing.coordinatesAdmitted s = true)
    (done : RingHydrogenCompletion.prepare? s.molecule s.spatial = some (i.molecule,i.spatial))
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (original : p.c.val.val < s.molecule.atomCount) :
    RingHydrogenReport.fromRaw? s.molecule s.spatial [p.c.val.val] = some [(p.c.val.val,none)] := by
  apply fromRaw_of_all_written (readmit s) source done _ (by simpa using original)
  intro y placement
  let hy := placement.full.trans (full_original i)
  let j := atGeometry i y hy
  let pair : TwinPair j := ⟨p.c,p.u,p.v,p.distinct,p.records,p.lu,p.lv⟩
  have same := coordinates_of_same_ligands (i := i) hy fun c k =>
    placement.fixed _ (centers_unmoved (RingHydrogenCompletion.prepare?_certified done) i rfl c k)
  exact pair.raw_refusal (RingHydrogenCompletion.prepare?_closed done) (same.trans admitted)

end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.TwinPair.root_refusal
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.TwinPair.prepared_refusal

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter
open LocalizedChemicalRing (Input)
open RingGroupedReport (Report)
open RingWrittenPHReadings RingSpatialTransport RingHydrogenCompletion RingPyramidalChoices

private theorem report_refusal_row (i : Input)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) (a : i.certified.Atom)
    (refusal : RingChemicalGraphProof.root i a = some none)
    (atoms : List i.certified.Atom) (rows : Report) (got : RingChemicalReport.report? i atoms = some rows)
    (row : Nat × Option RingNestedActivePair.Labels) (member : row ∈ rows) (atId : row.1 = a.val) :
    row.2 = none := by
  have correct := (RingChemicalReport.report_iff i admitted atoms rows).mp got
  clear got
  induction correct generalizing row with
  | nil => contradiction
  | @cons b head atoms rows first tail ih =>
    rcases List.mem_cons.mp member with eq | rest
    · subst row
      have ba : b = a := Fin.ext (first.1.symm.trans atId)
      have read := (RingChemicalGraphProof.root_iff admitted b head.2).mpr first.2
      rw [ba,refusal] at read
      exact (Option.some.inj read).symm
    · exact ih row rest atId

/-- Every successful closed raw report retains refusal at a specified native
root, independently of all other requests and their multiplicities. -/
theorem raw_row_refusal (i : Input) (closed : plan i.molecule = [])
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) (a : i.certified.Atom)
    (refusal : RingChemicalGraphProof.root i a = some none)
    (ids : List Nat) (rows : Report)
    (got : RingHydrogenReport.fromRaw? i.molecule i.spatial ids = some rows)
    (row : Nat × Option RingNestedActivePair.Labels) (member : row ∈ rows) (atId : row.1 = a.val) :
    row.2 = none := by
  have chemical := got
  rw [RingHydrogenReport.fromRaw_closed_eq closed] at chemical
  obtain ⟨source,hs,⟨atoms,ha⟩,_⟩ := (RingChemicalReport.fromRaw_graph_iff ..).mp chemical
  have si : source = i := Option.some.inj (hs.symm.trans (readmit i))
  subst source
  rw [←ha,fromRaw_closed_report i closed admitted] at got
  exact report_refusal_row i admitted a refusal atoms rows got row member atId

/-- A twin parent has no assigned row in any successful original raw request,
even when unrelated requested sites or unresolved P-H choices are present.
Duplicate occurrences of the parent ID are all ordinary completed refusals. -/
theorem TwinPair.prepared_rows_refusal {s i : Input} (p : TwinPair i)
    (source : LocalizedChemicalRing.coordinatesAdmitted s = true)
    (done : prepare? s.molecule s.spatial = some (i.molecule,i.spatial))
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (ids : List Nat) (rows : Report)
    (got : RingHydrogenReport.fromRaw? s.molecule s.spatial ids = some rows)
    (row : Nat × Option RingNestedActivePair.Labels) (member : row ∈ rows)
    (atId : row.1 = p.c.val.val) : row.2 = none := by
  obtain ⟨_,_,_,_,_,bounds,_,_⟩ := (fromRaw_iff_written_population ..).mp got
  obtain ⟨ps,hps⟩ := choices_exists (sites s.molecule s.spatial i.molecule i.spatial) i.spatial.positions
  let y : SpatialConfiguration := ⟨ps⟩
  have placement : Placement s.molecule s.spatial i.molecule i.spatial y :=
    variant_placement (prepare?_certified done) (List.mem_map.mpr ⟨ps,hps,rfl⟩)
  let hy := placement.full.trans (full_original i)
  let j := atGeometry i y hy
  let pair : TwinPair j := ⟨p.c,p.u,p.v,p.distinct,p.records,p.lu,p.lv⟩
  have same := coordinates_of_same_ligands (i := i) hy fun c k =>
    placement.fixed _ (centers_unmoved (prepare?_certified done) i rfl c k)
  have actual := (fromRaw_all_placements (readmit s) source done ids bounds rows).mp got y placement
  exact raw_row_refusal j (prepare?_closed done) (same.trans admitted) pair.c.val
    (pair.root_refusal (same.trans admitted)) ids rows actual row member atId
private theorem report_of_root_labels (i : Input) (labels : Nat → Option RingNestedActivePair.Labels) (atoms : List i.certified.Atom)
    (roots : ∀ a ∈ atoms, RingChemicalGraphProof.root i a = some (labels a.val)) :
    RingChemicalReport.report? i atoms = some (atoms.map fun a => (a.val,labels a.val)) := by
  induction atoms with
  | nil => rfl
  | cons a atoms ih =>
    have first := roots a List.mem_cons_self
    have rest := ih (fun b hb => roots b (List.mem_cons_of_mem _ hb))
    simp only [RingChemicalReport.report?,List.mapM_cons,List.map_cons]
    change (do
      let row ← (RingChemicalGraphProof.root i a).map (fun value => (a.val,value))
      let rows ← RingChemicalReport.report? i atoms
      pure (row :: rows)) = _
    rw [first,rest]
    rfl

/-- A closed raw request preserves the exact row order and labels of every selected native root. -/
theorem raw_of_root_labels (i : Input) (labels : Nat → Option RingNestedActivePair.Labels) (closed : plan i.molecule = [])
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) (ids : List Nat)
    (bounds : ∀ n ∈ ids, n < i.molecule.atomCount)
    (roots : ∀ a : i.certified.Atom, a.val ∈ ids → RingChemicalGraphProof.root i a = some (labels a.val)) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial ids = some (ids.map fun n => (n,labels n)) := by
  have size := i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1
  let atoms : List i.certified.Atom := ids.attach.map fun n => ⟨n.val,by rw [size]; exact bounds _ n.property⟩
  have raw : atoms.map Fin.val = ids := by simp [atoms,List.map_map,Function.comp_def]
  have all : ∀ a ∈ atoms, RingChemicalGraphProof.root i a = some (labels a.val) := by
    intro a ha
    apply roots a
    rw [←raw]
    exact List.mem_map.mpr ⟨a,ha,rfl⟩
  rw [←raw,fromRaw_closed_report i closed admitted,report_of_root_labels i labels atoms all]
  simp only [List.map_map,Function.comp_def]

/-- A closed raw request preserves the exact row order when each selected native root refuses. -/
theorem raw_all_refusals (i : Input) (closed : plan i.molecule = [])
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) (ids : List Nat)
    (bounds : ∀ n ∈ ids, n < i.molecule.atomCount)
    (roots : ∀ a : i.certified.Atom, a.val ∈ ids → RingChemicalGraphProof.root i a = some none) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial ids = some (ids.map fun n => (n,none)) :=
  raw_of_root_labels i (fun _ => none) closed admitted ids bounds roots

/-- An original request consisting entirely of twin-parent IDs always succeeds
with exactly its refusal rows, in the original order and with duplicates.
Selected P-H ambiguities elsewhere in the molecule cannot prevent this result. -/
theorem prepared_all_twin_refusals {s i : Input}
    (source : LocalizedChemicalRing.coordinatesAdmitted s = true)
    (done : prepare? s.molecule s.spatial = some (i.molecule,i.spatial))
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (ids : List Nat) (bounds : ∀ n ∈ ids, n < s.molecule.atomCount)
    (twins : ∀ n ∈ ids, ∃ p : TwinPair i, p.c.val.val = n) :
    RingHydrogenReport.fromRaw? s.molecule s.spatial ids = some (ids.map fun n => (n,none)) := by
  apply fromRaw_of_all_written (readmit s) source done ids bounds
  intro y placement
  let hy := placement.full.trans (full_original i)
  let j := atGeometry i y hy
  have same := coordinates_of_same_ligands (i := i) hy fun c k =>
    placement.fixed _ (centers_unmoved (prepare?_certified done) i rfl c k)
  apply raw_all_refusals j (prepare?_closed done) (same.trans admitted) ids
  · intro n hn
    exact (bounds n hn).trans_le (prepare?_certified done).atomCount_le
  · intro a ha
    obtain ⟨p,hp⟩ := twins a.val ha
    let pair : TwinPair j := ⟨p.c,p.u,p.v,p.distinct,p.records,p.lu,p.lv⟩
    have eq : a = pair.c.val := Fin.ext hp.symm
    rw [eq]
    exact pair.root_refusal (same.trans admitted)
end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.TwinPair.prepared_rows_refusal

assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.prepared_all_twin_refusals
