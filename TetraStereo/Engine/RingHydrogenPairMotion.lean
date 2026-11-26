import TetraStereo.Engine.RingHydrogenTwinGeometry

/-! Simultaneous motion of identical terminal ligand pairs in the public ring evaluator. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingRawRenumbering (molecularRecord)
open RingHydrogenLeafGeometry (SupportedLeaf)

/-- A pair of identical single-bond terminal ligands at one tetrahedral center. -/
structure TwinPair (i : Input) where
  c : i.certified.TetrahedralCenter
  u : i.certified.Atom
  v : i.certified.Atom
  distinct : u ≠ v
  records : (i.molecule.atoms[u.val]?).map molecularRecord =
    (i.molecule.atoms[v.val]?).map molecularRecord
  lu : ∀ a : i.certified.Atom, i.molecule.bondOrder u.val a.val = if a = c.val then 1 else 0
  lv : ∀ a : i.certified.Atom, i.molecule.bondOrder v.val a.val = if a = c.val then 1 else 0

namespace TwinPair
variable {i : Input}
def Contains (p : TwinPair i) (a : i.certified.Atom) : Prop := a = p.u ∨ a = p.v

theorem supportU (p : TwinPair i) : SupportedLeaf i p.u p.c.val := supported_of_bond_row p.lu
theorem supportV (p : TwinPair i) : SupportedLeaf i p.v p.c.val := supported_of_bond_row p.lv

theorem support (p : TwinPair i) {a : i.certified.Atom} (inside : p.Contains a) :
    SupportedLeaf i a p.c.val := by
  rcases inside with rfl | rfl
  · exact p.supportU
  · exact p.supportV

/-- Distinct supporting centers force disjoint leaf sets; no disjointness premise is assumed. -/
theorem disjoint (p q : TwinPair i) (different : p.c ≠ q.c) {a : i.certified.Atom}
    (left : p.Contains a) (right : q.Contains a) : False := by
  have edge := (q.support right q.c.val).mpr rfl
  have centers : q.c.val = p.c.val := (p.support left q.c.val).mp edge
  exact different (Subtype.ext centers.symm)

theorem choice_fixed (p : TwinPair i) (e : Equiv.Perm i.certified.Atom)
    (choice : e = 1 ∨ e = Equiv.swap p.u p.v) (a : i.certified.Atom)
    (outside : ¬p.Contains a) : e.symm a = a := by
  rcases choice with rfl | rfl
  · rfl
  · exact Equiv.swap_apply_of_ne_of_ne (fun h => outside (Or.inl h)) (fun h => outside (Or.inr h))

theorem choice_inside (p : TwinPair i) (e : Equiv.Perm i.certified.Atom)
    (choice : e = 1 ∨ e = Equiv.swap p.u p.v) (a : i.certified.Atom)
    (inside : p.Contains a) : p.Contains (e.symm a) := by
  rcases choice with rfl | rfl
  · exact inside
  · rcases inside with rfl | rfl <;> simp [Contains]
end TwinPair

private def composeGraphs {i j k : Input} (g : GraphMap i j) (h : GraphMap j k) : GraphMap i k where
  atoms := g.atoms.trans h.atoms
  records a := (h.records (g.atoms a)).trans (g.records a)
  bonds a b := (h.bonds (g.atoms a) (g.atoms b)).trans (g.bonds a b)

/-- Arbitrarily many independent identity/swap choices are realized by one molecular
automorphism. Supporting-center uniqueness derives every required leaf disjointness. -/
theorem many_twin_map {i : Input} (ps : List (TwinPair i))
    (separate : (ps.map TwinPair.c).Nodup)
    (e : (p : TwinPair i) → Equiv.Perm i.certified.Atom)
    (choice : ∀ p ∈ ps, e p = 1 ∨ e p = Equiv.swap p.u p.v) :
    ∃ g : GraphMap i i,
      (∀ p ∈ ps, ∀ a, p.Contains a → g.atoms.symm a = (e p).symm a) ∧
      (∀ a, (∀ p ∈ ps, ¬p.Contains a) → g.atoms.symm a = a) := by
  induction ps with
  | nil => exact ⟨identityGraph i,by simp,by intros; rfl⟩
  | cons p ps ih =>
    have sep := List.nodup_cons.mp separate
    have headChoice := choice p List.mem_cons_self
    have tailChoice := fun q h => choice q (List.mem_cons_of_mem p h)
    obtain ⟨tail,tailInside,tailOutside⟩ := ih sep.2 tailChoice
    obtain ⟨head,headEq⟩ := graph_of_twin_choice p.u p.v p.c.val p.records p.lu p.lv (e p) headChoice
    have headSymm (a : i.certified.Atom) : head.atoms.symm a = (e p).symm a := by rw [headEq]
    have distinct (q : TwinPair i) (mem : q ∈ ps) : p.c ≠ q.c := by
      intro eq
      exact sep.1 (List.mem_map.mpr ⟨q,mem,eq.symm⟩)
    refine ⟨composeGraphs tail head,?_,?_⟩
    · intro q mem a inside
      change tail.atoms.symm (head.atoms.symm a) = _
      rcases List.mem_cons.mp mem with same | mem
      · subst q
        rw [headSymm]
        apply tailOutside
        intro q mem other
        exact p.disjoint q (distinct q mem) (p.choice_inside (e p) headChoice a inside) other
      · have notHead : ¬p.Contains a := fun hit => p.disjoint q (distinct q mem) hit inside
        rw [headSymm,p.choice_fixed (e p) headChoice a notHead]
        exact tailInside q mem a inside
    · intro a outside
      change tail.atoms.symm (head.atoms.symm a) = a
      rw [headSymm,p.choice_fixed (e p) headChoice a (outside p List.mem_cons_self)]
      exact tailOutside a (fun q h => outside q (List.mem_cons_of_mem p h))

assert_kernel_only TwinPair.supportU
assert_kernel_only TwinPair.supportV
assert_kernel_only TwinPair.disjoint
assert_kernel_only many_twin_map
end TetraStereo.Engine.RingHydrogenSpelling

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter RingSpatialTransport RingNumberedHydrogenGeometry RingWrittenPHReadings
open RingHydrogenLeafGeometry HydrogenLeafParity LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
variable {i : Input}

private theorem frame_congr {w x : SpatialConfiguration} (ids : Fin 4 → Nat)
    (points : ∀ k, geometry w (ids k) = geometry x (ids k)) :
    readback? (geometry w) (order ids 1) = readback? (geometry x) (order ids 1) := by
  apply RingFrameTransport.readback_congr
  intro n hn
  change n ∈ [ids 0,ids 1,ids 2,ids 3] at hn
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> exact points _

private theorem TwinPair.avoids {p : TwinPair i} {a : i.certified.Atom}
    (away : a ≠ p.c.val) (b : i.certified.moleculeGraph.Neighbor a) : ¬p.Contains b.val :=
  fun h => h.elim (neighbor_avoids_leaf p.supportU away b) (neighbor_avoids_leaf p.supportV away b)

private theorem TwinPair.parity (p : TwinPair i) (w x : SpatialConfiguration)
    (hw : w.positions.length = size i) (hx : x.positions.length = size i)
    (gw : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) = true)
    (gx : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) = true) :
    ∃ e : Equiv.Perm i.certified.Atom, (e = 1 ∨ e = Equiv.swap p.u p.v) ∧
      let ids := fun k => ((tetraEnumeration i p.c) k).val.val
      readback? (geometry x) (order ids 1) =
        readback? (geometry (reindexed (atGeometry i w hw) i e)) (order ids 1) := by
  let d := tetraEnumeration i p.c
  obtain ⟨h,hu⟩ := d.surjective ⟨p.u,i.certified.moleculeGraph.adj_symm.mpr ((p.supportU _).mpr rfl)⟩
  obtain ⟨k,hv⟩ := d.surjective ⟨p.v,i.certified.moleculeGraph.adj_symm.mpr ((p.supportV _).mpr rfl)⟩
  obtain ⟨e,choice,_,reads⟩ := select_canonical_leaf_parity i w x hw hx p.c p.u p.v p.distinct h k
    (congrArg Subtype.val hu) (congrArg Subtype.val hv)
    (admitted_nonzero w hw p.c gw) (admitted_nonzero x hx p.c gx)
  exact ⟨e,choice,reads 1 false⟩

/-- The inverse atom correspondence fixes all other atoms and either preserves or
exchanges the two atoms within each designated pair. -/
def PairActions (ps : List (TwinPair i)) (g : GraphMap i i) : Prop :=
  (∀ a, (∀ p ∈ ps, ¬p.Contains a) → g.atoms.symm a = a) ∧
  ∀ p ∈ ps, (g.atoms.symm p.u = p.u ∧ g.atoms.symm p.v = p.v) ∨
    (g.atoms.symm p.u = p.v ∧ g.atoms.symm p.v = p.u)

/-- Signed readings at every tetrahedral center outside the selected pairs' parents,
and at every eligible phosphorus including its phantom slot. -/
def OtherFramesAgree (ps : List (TwinPair i)) (x w : SpatialConfiguration) : Prop :=
  (∀ c, (∀ p ∈ ps, p.c ≠ c) →
    let ids := fun k => ((tetraEnumeration i c) k).val.val
    readback? (geometry x) (order ids 1) = readback? (geometry w) (order ids 1)) ∧
  ∀ a hp, let ids := RingPyramidalChoices.phosphorusFrameIds (phosphorusEnumeration i a hp)
    readback? (geometry x) (order ids 1) = readback? (geometry w) (order ids 1)

/-- Every degree-one ligand at a selected parent can move. This includes the third
hydrogen at a methyl group even when only two of its hydrogens realize the swap. -/
theorem otherFrames_of_terminal_motion {ps : List (TwinPair i)} {x w : SpatialConfiguration}
    (stable : ∀ a : i.certified.Atom, (∀ p ∈ ps, ¬SupportedLeaf i a p.c.val) → geometry x a.val = geometry w a.val) :
    OtherFramesAgree ps x w := by
  constructor
  · intro c free
    let d := tetraEnumeration i c
    exact frame_congr _ (fun k => stable (d k).val fun p hp leaf =>
      free p hp (Subtype.ext ((leaf _).mp (i.certified.moleculeGraph.adj_symm.mp (d k).property)).symm))
  · intro a ha
    let d := phosphorusEnumeration i a ha
    have neighbors (k : Fin 3) : geometry x (d k).val.val = geometry w (d k).val.val := by
      apply stable
      intro p _ leaf
      have eq := (leaf _).mp (i.certified.moleculeGraph.adj_symm.mp (d k).property)
      have off := notP_of_degree_four (i := i) p.c.val ((i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mp p.c.property)
      rw [←eq,ha] at off
      contradiction
    have center := stable a (fun _ _ leaf => phosphorus_ne_leaf leaf ha rfl)
    apply frame_congr
    intro k
    fin_cases k
    · exact neighbors 0
    · exact neighbors 1
    · exact neighbors 2
    · exact center

/-- In particular, fixing the coordinates outside the pairs suffices. -/
theorem otherFrames_of_points {ps : List (TwinPair i)} {x w : SpatialConfiguration}
    (stable : ∀ a : i.certified.Atom, (∀ p ∈ ps, ¬p.Contains a) → geometry x a.val = geometry w a.val) :
    OtherFramesAgree ps x w :=
  otherFrames_of_terminal_motion (fun a free => stable a (fun p hp h => free p hp (p.support h)))

private theorem reindexed_other_frames (ps : List (TwinPair i)) (g : GraphMap i i)
    (outside : ∀ a, (∀ p ∈ ps, ¬p.Contains a) → g.atoms.symm a = a)
    (w : SpatialConfiguration) (hw : w.positions.length = size i) :
    OtherFramesAgree ps (reindexed (atGeometry i w hw) i g.atoms) w := by
  apply otherFrames_of_points
  intro a free
  exact (reindexed_lookup (i := atGeometry i w hw) (j := i) g.atoms a).trans
    (congrArg (fun b : i.certified.Atom => w.positions[b.val]?) (outside a free))

/-- Local choices of H identity or exchange can be realized by one graph automorphism.
Only the endpoint geometries are needed; each other center sees fixed neighbors. -/
private theorem assemble_pair_frames (ps : List (TwinPair i)) (separate : (ps.map TwinPair.c).Nodup)
    (w x : SpatialConfiguration) (hw : w.positions.length = size i) (hx : x.positions.length = size i)
    (off : OtherFramesAgree ps x w)
    (gw : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) = true)
    (gx : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) = true) :
    ∃ g : GraphMap i i, PairActions ps g ∧ ReadingMatch g w x := by
  classical
  choose e choice read using fun p : TwinPair i => p.parity w x hw hx gw gx
  obtain ⟨g,inside,outside⟩ := many_twin_map ps separate e (fun p _ => choice p)
  have stable := reindexed_other_frames ps g outside w hw
  refine ⟨g,⟨outside,?_⟩,hw,?_,?_⟩
  · intro p hp
    have u := inside p hp p.u (Or.inl rfl)
    have v := inside p hp p.v (Or.inr rfl)
    rcases choice p with id | swap
    · exact Or.inl ⟨by simpa [id] using u,by simpa [id] using v⟩
    · exact Or.inr ⟨by simpa [swap] using u,by simpa [swap] using v⟩
  · intro c
    by_cases found : ∃ p ∈ ps, p.c = c
    · obtain ⟨p,hp,rfl⟩ := found
      refine (read p).trans (frame_congr _ (fun k => ?_))
      let a := (tetraEnumeration i p.c k).val
      have action : g.atoms.symm a = (e p).symm a := by
        by_cases leaf : p.Contains a
        · exact inside p hp a leaf
        · have free : ∀ t ∈ ps, ¬t.Contains a := by
            intro t ht
            by_cases same : p.c = t.c
            · have equal := List.inj_on_of_nodup_map separate hp ht same
              simpa only [←equal] using leaf
            · exact t.avoids (fun h => same (Subtype.ext h)) (tetraEnumeration i p.c k)
          rw [outside a free]
          exact (p.choice_fixed (e p) (choice p) a leaf).symm
      change (reindexed (atGeometry i w hw) i (e p)).positions[a.val]? = (reindexed (atGeometry i w hw) i g.atoms).positions[a.val]?
      rw [reindexed_lookup,reindexed_lookup]
      exact congrArg (fun b : i.certified.Atom => w.positions[b.val]?) action.symm
    · have none : ∀ p ∈ ps, p.c ≠ c := fun p hp h => found ⟨p,hp,h⟩
      exact (off.1 c none).trans (stable.1 c none).symm
  · exact fun a hp => (off.2 a hp).trans (stable.2 a hp).symm

/-- On admitted endpoints, a molecular correspondence made of the indicated pair
swaps matches every signed frame exactly when the remaining centers agree. -/
theorem many_twin_frames_iff (ps : List (TwinPair i)) (separate : (ps.map TwinPair.c).Nodup)
    (w x : SpatialConfiguration) (hw : w.positions.length = size i) (hx : x.positions.length = size i)
    (gw : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) = true)
    (gx : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) = true) :
    (∃ g : GraphMap i i, PairActions ps g ∧ ReadingMatch g w x) ↔ OtherFramesAgree ps x w := by
  constructor
  · rintro ⟨g,action,_,hands⟩
    have stable := reindexed_other_frames ps g action.1 w hw
    exact ⟨fun c free => (hands.1 c).trans (stable.1 c free),
      fun a hp => (hands.2 a hp).trans (stable.2 a hp)⟩
  · exact fun off => assemble_pair_frames ps separate w x hw hx off gw gx

end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.many_twin_frames_iff

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter RingSpatialTransport RingNumberedHydrogenGeometry RingHydrogenCompletion
open RingActiveDistanceSchedule RingRawRenumbering RingHydrogenLeafGeometry
open LocalizedChemicalRing (Input)
variable {i j : Input}

/-- One atom correspondence works at every root and every actual queue entry, even
when the written determinants at different twin-bearing centers change independently. -/
theorem many_twin_stores (ps : List (TwinPair i)) (separate : (ps.map TwinPair.c).Nodup)
    (w x : SpatialConfiguration) (hw : w.positions.length = size i) (hx : x.positions.length = size i)
    (gw : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) = true)
    (gx : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) = true)
    (off : OtherFramesAgree ps x w) :
    ∃ g : GraphMap i i, PairActions ps g ∧
      ∀ root k, k ≤ height (atGeometry i w hw) + 1 → ∀ q,
        sphereEntry (atGeometry i w hw) root k q = sphereEntry (atGeometry i x hx) (g.atoms root) k
          ((reindexSite _ (reindexed _ _ (g.atTables w x hw hx).atoms) (reindexed_full _)).symm
            (AtomMap.site (g.atTables w x hw hx).atSourceGeometry q)) := by
  obtain ⟨g,action,_,hands⟩ := (many_twin_frames_iff ps separate w x hw hx gw gx).mpr off
  exact ⟨g,action,graph_sphereEntry (g.atTables w x hw hx) gw hands⟩

private theorem raw_gate {i : Input} (closed : plan i.molecule = []) (ids : List Nat) :
    (∃ rows, RingHydrogenReport.fromRaw? i.molecule i.spatial ids = some rows) ↔
      (∀ n ∈ ids, n < i.molecule.atomCount) ∧ LocalizedChemicalRing.coordinatesAdmitted i = true := by
  rw [RingHydrogenReport.fromRaw_closed_eq closed]
  exact closed_domain i closed ids

/-- The raw API accepts exactly the same requests and returns their exact original rows
when admission agrees and the signed readings outside the selected parents agree. -/
theorem many_twin_report (ps : List (TwinPair i)) (separate : (ps.map TwinPair.c).Nodup)
    (w x : SpatialConfiguration) (hw : w.positions.length = size i) (hx : x.positions.length = size i)
    (closed : plan i.molecule = [])
    (gate : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) =
      LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx))
    (off : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) = true → OtherFramesAgree ps x w)
    (ids : List Nat) :
    RingHydrogenReport.fromRaw? i.molecule x ids = RingHydrogenReport.fromRaw? i.molecule w ids := by
  by_cases gw : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) = true
  · obtain ⟨g,actions,matchFrames⟩ := (many_twin_frames_iff ps separate w x hw hx gw (gate ▸ gw)).mpr (off gw)
    apply LeafAllRequests.all_original_ids_many (atGeometry i w hw) x closed g.atoms _ _ ids
    · intro a degree
      have inverse : g.atoms.symm a = a := actions.1 a fun p _ h => degree (p.support h).degree_one
      exact (g.atoms.symm_apply_eq.mp inverse).symm
    · exact closed_placements g w x hx matchFrames closed closed
  · have reject (z : SpatialConfiguration) (hz : z.positions.length = size i)
        (bad : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i z hz) ≠ true) :
        RingHydrogenReport.fromRaw? i.molecule z ids = none := by
      cases result : RingHydrogenReport.fromRaw? i.molecule z ids with
      | none => rfl
      | some rows => exact (bad ((raw_gate (i := atGeometry i z hz) closed ids).mp ⟨rows,result⟩).2).elim
    rw [reject w hw gw,reject x hx (gate ▸ gw)]

/-- All public requests are invariant under motion of any terminal atoms at the
selected parents exactly when endpoint admission agrees. The pair chosen at each
parent suffices even when additional terminal ligands move there. -/
theorem terminal_motion_iff (ps : List (TwinPair i)) (separate : (ps.map TwinPair.c).Nodup)
    (w x : SpatialConfiguration) (hw : w.positions.length = size i) (hx : x.positions.length = size i)
    (closed : plan i.molecule = [])
    (fixed : ∀ a : i.certified.Atom, (∀ p ∈ ps, ¬SupportedLeaf i a p.c.val) → w.positions[a.val]? = x.positions[a.val]?) :
    (∀ ids, RingHydrogenReport.fromRaw? i.molecule x ids = RingHydrogenReport.fromRaw? i.molecule w ids) ↔
      LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) =
        LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) := by
  constructor
  · intro eq
    have empty (z : SpatialConfiguration) (hz : z.positions.length = size i) :
        (∃ rows, RingHydrogenReport.fromRaw? i.molecule z [] = some rows) ↔
          LocalizedChemicalRing.coordinatesAdmitted (atGeometry i z hz) = true := by
      simpa using raw_gate (i := atGeometry i z hz) closed []
    apply Bool.eq_iff_iff.mpr
    rw [←empty w hw,←empty x hx,eq []]
  · intro gate ids
    exact many_twin_report ps separate w x hw hx closed gate
      (fun _ => otherFrames_of_terminal_motion (fun a free => (fixed a free).symm)) ids

/-- Specialization to independent motion of exactly the indicated terminal pairs. -/
theorem many_twin_motion_iff (ps : List (TwinPair i)) (separate : (ps.map TwinPair.c).Nodup)
    (w x : SpatialConfiguration) (hw : w.positions.length = size i) (hx : x.positions.length = size i)
    (closed : plan i.molecule = [])
    (fixed : ∀ a : i.certified.Atom, (∀ p ∈ ps, ¬p.Contains a) → w.positions[a.val]? = x.positions[a.val]?) :
    (∀ ids, RingHydrogenReport.fromRaw? i.molecule x ids = RingHydrogenReport.fromRaw? i.molecule w ids) ↔
      LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) =
        LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) :=
  terminal_motion_iff ps separate w x hw hx closed
    (fun a free => fixed a (fun p hp h => free p hp (p.support h)))

/-- Compare placement tables after applying the spelling's graph map. The CH₂
parents are omitted from the signed-reading check in each admitted placement. -/
def SpellingFrames (g : GraphMap i j) (ps : List (TwinPair j)) (x y : SpatialConfiguration) : Prop :=
  ∃ (hx : x.positions.length = size i) (hy : y.positions.length = size j),
    let src := atGeometry i x hx
    let w := reindexed src j g.atoms
    let gw := LocalizedChemicalRing.coordinatesAdmitted (withSourceGeometry src j g.atoms)
    gw = LocalizedChemicalRing.coordinatesAdmitted (atGeometry j y hy) ∧ (gw = true → OtherFramesAgree ps y w)

private theorem spelling_placement_rows (g : GraphMap i j) (ps : List (TwinPair j))
    (separate : (ps.map TwinPair.c).Nodup) (x y : SpatialConfiguration)
    (matchFrames : SpellingFrames g ps x y) (left : plan i.molecule = []) (right : plan j.molecule = [])
    (ids : List Nat) :
    RingHydrogenReport.fromRaw? j.molecule y (ids.map (moveId g.atoms)) =
      (RingHydrogenReport.fromRaw? i.molecule x ids).map (List.map fun row => (moveId g.atoms row.1,row.2)) := by
  obtain ⟨hx,hy,gate,off⟩ := matchFrames
  let src := atGeometry i x hx
  let w := reindexed src j g.atoms
  rw [many_twin_report ps separate w y (reindexed_full _) hy right gate off]
  let indexed := (g.atTables x j.spatial hx (full_original j)).atSourceGeometry
  exact RingReportRenumber.closed_raw_report indexed left right ids

open RingPyramidalChoices OrdinaryHydrogenSpellings
variable {k : Nat} {coreAtom : Fin k → AtomSpec} {coreBond : Fin k → Fin k → Nat}

/-- Original input reports agree when the independent placement families cover the
same readings off the designated CH₂ parents. Each matched pair of placements may
choose its own H exchanges. The reported atom-ID map is fixed across the family. -/
theorem many_twin_spelling_report {a b : Completion coreAtom coreBond} (s : PreparedSpelling a) (t : PreparedSpelling b)
    (counts : ∀ p, totalH a p = totalH b p) (ps : List (TwinPair t.result)) (separate : (ps.map TwinPair.c).Nodup)
    (forth : ∀ x ∈ variants s.source.molecule s.source.spatial s.result.molecule s.result.spatial,
      ∃ y ∈ variants t.source.molecule t.source.spatial t.result.molecule t.result.spatial,
        SpellingFrames (preparedMap s t counts) ps x y)
    (back : ∀ y ∈ variants t.source.molecule t.source.spatial t.result.molecule t.result.spatial,
      ∃ x ∈ variants s.source.molecule s.source.spatial s.result.molecule s.result.spatial,
        SpellingFrames (preparedMap s t counts) ps x y)
    (parents : List (Fin k)) :
    RingHydrogenReport.fromRaw? t.source.molecule t.source.spatial (parents.map fun p => (b.core p).val) =
      (RingHydrogenReport.fromRaw? s.source.molecule s.source.spatial (parents.map fun p => (a.core p).val)).map
        (List.map fun row => (moveId (preparedMap s t counts).atoms row.1,row.2)) := by
  let g := preparedMap s t counts
  have moved : (parents.map fun p => (a.core p).val).map (moveId g.atoms) =
      parents.map fun p => (b.core p).val := by simp [g,List.map_map,Function.comp_def,preparedMap_core]
  have bounds (z : Completion coreAtom coreBond) (prep : PreparedSpelling z) :
      ∀ n ∈ parents.map (fun p => (z.core p).val), n < prep.source.molecule.atomCount := by
    intro n hn
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hn
    rw [prep.raw]
    exact (z.core p).isLt
  rw [←moved]
  apply RingSpellingPopulation.raw_population_transport (readmit s.source) (readmit t.source)
    s.coordinates t.coordinates s.prepared t.prepared _ _ (bounds a s) (moved ▸ bounds b t) _
    (RingSpellingPopulation.report_map_injective _ (moveId_injective g.atoms)) (SpellingFrames g ps) forth back
  exact fun x _ y _ hm => spelling_placement_rows g ps separate x y hm (prepare?_closed s.prepared)
    (prepare?_closed t.prepared) _

end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.many_twin_stores
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.many_twin_motion_iff
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.many_twin_spelling_report

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingRawRenumbering (molecularRecord)

/-- Direct raw-record and complete native single-bond-row test on two numbered vertices. -/
def twinCandidate (i : Input) (c : i.certified.TetrahedralCenter)
    (u v : i.certified.Atom) : Prop :=
  u ≠ v ∧
  (i.molecule.atoms[u.val]?).map molecularRecord = (i.molecule.atoms[v.val]?).map molecularRecord ∧
  (∀ a : i.certified.Atom, i.molecule.bondOrder u.val a.val = if a = c.val then 1 else 0) ∧
  (∀ a : i.certified.Atom, i.molecule.bondOrder v.val a.val = if a = c.val then 1 else 0)

instance (i : Input) (c : i.certified.TetrahedralCenter) (u v : i.certified.Atom) :
    Decidable (twinCandidate i c u v) := by unfold twinCandidate; infer_instance

def twinCandidate? (i : Input) (c : i.certified.TetrahedralCenter)
    (u v : i.certified.Atom) : Option (TwinPair i) :=
  if h : twinCandidate i c u v then some ⟨c,u,v,h.1,h.2.1,h.2.2.1,h.2.2.2⟩ else none

private def neighborPairs (i : Input) (c : i.certified.TetrahedralCenter) :
    List (i.certified.Atom × i.certified.Atom) :=
  let atoms := (List.finRange 4).map (i.certified.canonicalLigandAtom c)
  atoms.flatMap fun u => atoms.map fun v => (u,v)

/-- Scan the four actual neighbors of the tetrahedral center; the first passing pair carries its checked raw witnesses. -/
def detectedTwinPair? (i : Input) (c : i.certified.TetrahedralCenter) : Option (TwinPair i) :=
  (neighborPairs i c).findSome? fun uv => twinCandidate? i c uv.1 uv.2

theorem detectedTwinPair_center (i : Input) (c : i.certified.TetrahedralCenter)
    (p : TwinPair i) (found : detectedTwinPair? i c = some p) : p.c = c := by
  obtain ⟨⟨u,v⟩,_,hit⟩ := List.exists_of_findSome?_eq_some found
  unfold twinCandidate? at hit
  split at hit
  · exact congrArg TwinPair.c (Option.some.inj hit).symm
  · contradiction

/-- Detection succeeds exactly when this actual tetrahedral parent has a feasible twin pair. -/
theorem detectedTwinPair_iff (i : Input) (c : i.certified.TetrahedralCenter) :
    (detectedTwinPair? i c).isSome = true ↔ ∃ p : TwinPair i, p.c = c := by
  constructor
  · intro found
    obtain ⟨p,hit⟩ := Option.isSome_iff_exists.mp found
    exact ⟨p,detectedTwinPair_center i c p hit⟩
  · rintro ⟨p,same⟩
    have candidate : twinCandidate i c p.u p.v := by
      rw [← same]
      exact ⟨p.distinct,p.records,p.lu,p.lv⟩
    apply List.findSome?_isSome_iff.mpr
    refine ⟨(p.u,p.v),?_,?_⟩
    · subst c
      let d := RingWrittenPHReadings.tetraEnumeration i p.c
      obtain ⟨h,hu⟩ := d.surjective ⟨p.u,i.certified.moleculeGraph.adj_symm.mpr ((p.supportU _).mpr rfl)⟩
      obtain ⟨k,hv⟩ := d.surjective ⟨p.v,i.certified.moleculeGraph.adj_symm.mpr ((p.supportV _).mpr rfl)⟩
      have member {a : i.certified.Atom} {t : Fin 4} (hit : i.certified.canonicalLigandAtom p.c t = a) :
          a ∈ (List.finRange 4).map (i.certified.canonicalLigandAtom p.c) :=
        List.mem_map.mpr ⟨t,List.mem_finRange _,hit⟩
      exact List.mem_flatMap.mpr ⟨p.u,member (congrArg Subtype.val hu),
        List.mem_map.mpr ⟨p.v,member (congrArg Subtype.val hv),rfl⟩⟩
    · simp [twinCandidate?,candidate]

/-- Native tetrahedral centers appear once in ascending atom-ID order. -/
theorem canonicalCenters_nodup (i : Input) : i.certified.canonicalTetrahedralCenters.Nodup := by
  have projection : i.certified.canonicalTetrahedralCenters.map Subtype.val =
      i.certified.tetrahedralCenterSet.sort (· ≤ ·) := by
    simp [canonicalTetrahedralCenters,List.map_map]
  have nodup : (i.certified.canonicalTetrahedralCenters.map Subtype.val).Nodup := by
    rw [projection]
    exact Finset.sort_nodup _ _
  exact List.Nodup.of_map _ nodup

/-- One executable twin-pair selection per feasible native tetrahedral parent. -/
def detectedPairs (i : Input) : List (TwinPair i) :=
  i.certified.canonicalTetrahedralCenters.filterMap (detectedTwinPair? i)

theorem detectedPairs_centers (i : Input) :
    (detectedPairs i).map TwinPair.c = i.certified.canonicalTetrahedralCenters.filter
      (fun c => (detectedTwinPair? i c).isSome) := by
  unfold detectedPairs
  generalize i.certified.canonicalTetrahedralCenters = cs
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases found : detectedTwinPair? i c with
    | none => simp [found,ih]
    | some p => simp [found,ih,detectedTwinPair_center i c p found]

theorem detectedPairs_separate (i : Input) : ((detectedPairs i).map TwinPair.c).Nodup := by
  rw [detectedPairs_centers]
  exact (canonicalCenters_nodup i).filter _

/-- The graph-derived inventory contains precisely the feasible supporting parents. -/
theorem detectedPairs_parent_iff (i : Input) (c : i.certified.TetrahedralCenter) :
    c ∈ (detectedPairs i).map TwinPair.c ↔ ∃ p : TwinPair i, p.c = c := by
  rw [detectedPairs_centers,List.mem_filter]
  have member := (i.certified.mem_canonicalTetrahedralCenters_iff c).mpr c.property
  simp only [member,true_and,detectedTwinPair_iff]

open RingSpatialTransport RingHydrogenCompletion RingHydrogenLeafGeometry

/-- The graph itself selects every center with two identical terminal ligands.
Any of their terminal atoms may move, including all three H atoms at a methyl group. -/
theorem detected_terminal_motion_iff (i : Input) (w x : SpatialConfiguration)
    (hw : w.positions.length = size i) (hx : x.positions.length = size i) (closed : plan i.molecule = [])
    (fixed : ∀ a : i.certified.Atom,
      (∀ c : i.certified.TetrahedralCenter, (detectedTwinPair? i c).isSome = true → ¬SupportedLeaf i a c.val) →
        w.positions[a.val]? = x.positions[a.val]?) :
    (∀ ids, RingHydrogenReport.fromRaw? i.molecule x ids = RingHydrogenReport.fromRaw? i.molecule w ids) ↔
      LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) =
        LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) := by
  apply terminal_motion_iff (detectedPairs i) (detectedPairs_separate i) w x hw hx closed
  intro a free
  apply fixed a
  intro c detected leaf
  have mem := (detectedPairs_parent_iff i c).mpr ((detectedTwinPair_iff i c).mp detected)
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp mem
  exact free p hp leaf

assert_kernel_only detected_terminal_motion_iff
assert_kernel_only detectedTwinPair_center
assert_kernel_only detectedTwinPair_iff
assert_kernel_only detectedPairs_separate
assert_kernel_only detectedPairs_parent_iff
end TetraStereo.Engine.RingHydrogenSpelling
