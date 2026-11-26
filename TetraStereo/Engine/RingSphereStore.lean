import Batteries.Tactic.OpenPrivate
import TetraStereo.Engine.RingBranchSymmetry

/-! The public evaluator's auxiliary store as a list of addressed rows.
Every scheduled simple path occurs once. Transport preserves the complete
list up to enumeration order at each prefix of the outside-in schedule. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingSphereStore
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingGraphCache (Visit sphere)
open RingGraphPaths (Path)
open RingActiveDistanceSchedule (Cell height distance)
open RingRawRenumbering (AtomMap)
open RingRawRenumbering.AtomMap (site sites)
open RingPyramidalPublication (publish eligible)

private theorem visit_ext {i : Input} {r} (u v : Visit i r)
    (h : u.history = v.history) : u = v := by
  have head {h a} (p : Path i r h a) : h.head? = some a := by cases p <;> rfl
  have atoms : u.atom = v.atom := Option.some.inj ((head u.path).symm.trans (h ▸ head v.path))
  cases u; cases v; simp_all

open private extend children from TetraStereo.Engine.RingGraphCache

private theorem extend_history {i : Input} {r} {v w : Visit i r} {b}
    (h : extend v b = some w) : w.history = b::v.history := by
  unfold extend at h
  split at h
  · exact congrArg Visit.history (Option.some.inj h.symm)
  · contradiction

private theorem children_nodup {i : Input} {r} (v : Visit i r) : (children v).Nodup := by
  apply List.Nodup.filterMap _ (List.nodup_finRange _)
  intro a b w ha hb
  have h := (extend_history ha).symm.trans (extend_history hb)
  exact (List.cons.inj h).1

theorem sphere_nodup (i : Input) (r : i.certified.Atom) (n : Nat) : (sphere i r n).Nodup := by
  induction n with
  | zero => simp [sphere]
  | succ n ih =>
    change ((sphere i r n).flatMap children).Nodup
    apply List.nodup_flatMap.mpr
    refine ⟨fun v _ => children_nodup v,ih.imp ?_⟩
    intro u v ne w hu hv
    obtain ⟨a,_,ha⟩ := List.mem_filterMap.mp hu
    obtain ⟨b,_,hb⟩ := List.mem_filterMap.mp hv
    have h := (extend_history ha).symm.trans (extend_history hb)
    exact ne (visit_ext u v (List.cons.inj h).2)

open private select from TetraStereo.Engine.RingEligibleGraph

private theorem select_history {i : Input} {allow : i.certified.Atom → Bool} {r}
    {v : Visit i r} {q : Site i} (h : select allow v = some q) : q.val.node.history = v.history := by
  unfold select at h
  split at h
  · obtain rfl := Option.some.inj h.symm
    exact (RingGraphPaths.represents_site v.path).2.1
  · contradiction

theorem queue_nodup (i : Input) (allow : i.certified.Atom → Bool) (r : i.certified.Atom) (n : Nat) :
    (RingEligibleGraph.queue i allow r n).Nodup := by
  change ((sphere i r n).filterMap (select allow)).Nodup
  apply List.Nodup.filterMap _ (sphere_nodup i r n)
  intro u v q hu hv
  exact visit_ext u v ((select_history hu).symm.trans (select_history hv))

private theorem stored_key_time {i : Input} (rule : RingActiveDistanceSchedule.Rule i)
    (root : i.certified.Atom) (queue : Nat → List (Site i))
    (atDistance : ∀ d q, q ∈ queue d → distance q = d) (top k : Nat) (q : Site i)
    (mem : q ∈ (RingSphereQueue.stored rule root queue top k).map Prod.fst) :
    ∃ n, n < k ∧ distance q = top - n := by
  induction k with
  | zero => simp [RingSphereQueue.stored] at mem
  | succ k ih =>
    simp only [RingSphereQueue.stored,List.map_append,List.map_map,Function.comp_def,
      List.map_id',List.mem_append] at mem
    rcases mem with current | prev
    · exact ⟨k,Nat.lt_succ_self _,atDistance _ _ current⟩
    · obtain ⟨n,lt,eqn⟩ := ih prev
      exact ⟨n,Nat.lt_succ_of_lt lt,eqn⟩

theorem stored_keys_nodup {i : Input} (rule : RingActiveDistanceSchedule.Rule i)
    (root : i.certified.Atom) (queue : Nat → List (Site i))
    (atDistance : ∀ d q, q ∈ queue d → distance q = d)
    (unique : ∀ d, (queue d).Nodup) (top k : Nat) (bound : k ≤ top+1) :
    ((RingSphereQueue.stored rule root queue top k).map Prod.fst).Nodup := by
  induction k with
  | zero => simp [RingSphereQueue.stored]
  | succ k ih =>
    simp only [RingSphereQueue.stored,List.map_append,List.map_map,Function.comp_def,List.map_id']
    apply List.Nodup.append (unique _) (ih (by omega))
    intro q current prev
    have now := atDistance _ _ current
    obtain ⟨n,lt,old⟩ := stored_key_time rule root queue atDistance top k q prev
    omega

private theorem row_iff_entry {α β : Type} [DecidableEq α] (rows : List (α × β))
    (nd : (rows.map Prod.fst).Nodup) (a : α) (b : β) :
    (a,b) ∈ rows ↔ (rows.find? (fun p => decide (p.1 = a))).map Prod.snd = some b := by
  induction rows with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨off,nd⟩ := List.nodup_cons.mp nd
    by_cases eqn : p.1 = a
    · have absent : (a,b) ∉ ps := by
        intro h
        exact off (eqn ▸ List.mem_map.mpr ⟨(a,b),h,rfl⟩)
      simp [eqn,absent,Prod.ext_iff,eq_comm]
    · simp [eqn,ih nd,Prod.ext_iff,Ne.symm eqn]

theorem chemical_stored_keys_nodup (i : Input) (root : i.certified.Atom)
    (k : Nat) (bound : k ≤ height i+1) :
    ((RingSphereQueue.stored (publish i) root
      (RingEligibleGraph.queue i (eligible i) root) (height i) k).map Prod.fst).Nodup :=
  stored_keys_nodup (publish i) root _
    (fun d q h => ((RingEligibleGraph.inventory i (eligible i) root d q).mp h).2)
    (queue_nodup i (eligible i) root) _ _ bound

/-- Whole-row multiplicity transport from first-match entries and unique keys.
The value type is unrestricted, so refusals and failed cells remain distinct. -/
theorem rows_perm_of_entries {α β γ : Type} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (left : List (α × γ)) (right : List (β × γ))
    (lkeys : (left.map Prod.fst).Nodup) (rkeys : (right.map Prod.fst).Nodup)
    (agree : ∀ q, (left.find? (fun row => decide (row.1 = q))).map Prod.snd =
      (right.find? (fun row => decide (row.1 = e q))).map Prod.snd) :
    (left.map (fun row => (e row.1,row.2))).Perm right := by
  have lnd : (left.map (fun row => (e row.1,row.2))).Nodup := by
    apply List.Nodup.of_map (f := Prod.fst)
    simpa only [List.map_map,Function.comp_def] using lkeys.map e.injective
  apply (List.perm_ext_iff_of_nodup lnd (List.Nodup.of_map Prod.fst rkeys)).mpr
  rintro ⟨q,value⟩
  obtain ⟨p,rfl⟩ := e.surjective q
  have mapped : (e p,value) ∈ left.map (fun row => (e row.1,row.2)) ↔
      (p,value) ∈ left := by
    simp only [List.mem_map,Prod.exists,Prod.mk.injEq,e.injective.eq_iff]
    simp
  rw [mapped,row_iff_entry left lkeys,row_iff_entry right rkeys]
  exact congrArg (fun entry => entry = some value) (agree p) |>.to_iff

/-- The entire materialized executable store, including values and row multiplicities,
commutes with atom renumbering after every bounded batch prefix. -/
theorem chemical_stored_perm {i j : Input} (r : AtomMap i j)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (k : Nat) (bound : k ≤ height i+1) :
    ((RingSphereQueue.stored (publish i) root
      (RingEligibleGraph.queue i (eligible i) root) (height i) k).map
      (fun row => (site r row.1,row.2))).Perm
    (RingSphereQueue.stored (publish j) (r.atoms root)
      (RingEligibleGraph.queue j (eligible j) (r.atoms root)) (height j) k) := by
  let left := RingSphereQueue.stored (publish i) root
    (RingEligibleGraph.queue i (eligible i) root) (height i) k
  let right := RingSphereQueue.stored (publish j) (r.atoms root)
    (RingEligibleGraph.queue j (eligible j) (r.atoms root)) (height j) k
  have lkeys : (left.map Prod.fst).Nodup := chemical_stored_keys_nodup i root k bound
  have rkeys : (right.map Prod.fst).Nodup := chemical_stored_keys_nodup j (r.atoms root) k
    (by rw [← RingReportRenumber.schedule_height r]; exact bound)
  exact rows_perm_of_entries (sites r) left right lkeys rkeys
    (RingReportRenumber.chemical_stored_entry r admitted root k bound)

end TetraStereo.Engine.RingSphereStore

namespace TetraStereo.Engine.RingSphereQueue
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Cell Rule height)

/-- Continue the ordinary queue loop with the rows already committed after `k` batches. -/
def resume {i : Input} (rule : Rule i) (root : i.certified.Atom) (queue : Nat → List (Site i))
    (k : Nat) (rows : List (Site i × Cell)) : Nat → List (Site i × Cell)
  | 0 => rows
  | n+1 =>
    let previous := resume rule root queue k rows n
    let read := reader root (viewOf previous)
    (queue (height i - (k+n))).map (fun q => (q,rule q read)) ++ previous

theorem resume_stored {i : Input} (rule : Rule i) (root : i.certified.Atom)
    (queue : Nat → List (Site i)) (k n : Nat) :
    resume rule root queue k (stored rule root queue (height i) k) n =
      stored rule root queue (height i) (k+n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [resume,ih,stored]
    rfl

end TetraStereo.Engine.RingSphereQueue

namespace TetraStereo.Engine.RingChemicalGraphProof
open LocalizedChemicalRing (Input)
open RingActiveDistanceSchedule (height)
open RingPyramidalPublication (focusP publish eligible)
open RingSphereQueue (reader stored viewOf resume)

/-- On precisely the two branches that use the auxiliary queue, the optimized
root returns the result of continuing from *any* of its materialized prefixes. -/
theorem fastRoot_from_sphere {i : Input} (a : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1)
    (usesQueue : (focusP i (RingGroupedReport.origin i a)).isSome = true ∨
      RingZeroMassReport.zeroEarly? i (RingGroupedReport.origin i a) = none) :
    fastRoot i a =
      let queue := RingEligibleGraph.queue i (eligible i) a
      let rows := stored (publish i) a queue (height i) k
      let final := resume (publish i) a queue k rows (height i+1-k)
      publish i (RingGroupedReport.origin i a) (reader a (viewOf final)) := by
  dsimp only
  rw [RingSphereQueue.resume_stored, Nat.add_sub_of_le bound, RingSphereQueue.stored_eq]
  change fastRoot i a = RingEligibleGraph.root i (eligible i) (publish i) a
  unfold fastRoot
  dsimp only
  cases hp : focusP i (RingGroupedReport.origin i a) with
  | some _ => rfl
  | none =>
    obtain dead | miss := usesQueue
    · simp [hp] at dead
    · rw [miss]

end TetraStereo.Engine.RingChemicalGraphProof
assert_kernel_only TetraStereo.Engine.RingChemicalGraphProof.fastRoot_from_sphere

namespace TetraStereo.Engine.RingSphereStore
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Cell height)
open RingHydrogenSpelling RingNumberedHydrogenGeometry RingSpatialTransport
open RingPyramidalPublication (eligible publish)

abbrev rows (i : Input) (a : i.certified.Atom) (k : Nat) : List (Site i × Cell) :=
  RingSphereQueue.stored (publish i) a (RingEligibleGraph.queue i (eligible i) a) (height i) k

/-- The induced site bijection includes both atom renumbering and the independent
coordinate table on the second graph. -/
def siteMap {i j : Input} (g : GraphMap i j) : Site i ≃ Site j :=
  (RingRawRenumbering.AtomMap.sites g.atSourceGeometry).trans
    (reindexSite j (reindexed i j g.atoms) (reindexed_full _)).symm

open private reindexed_height from TetraStereo.Engine.RingHydrogenSpelling

/-- A core-preserving graph correspondence and matching canonical physical readings
suffice for the entire stored rows to agree at every root and sphere. -/
theorem spelling_rows {i j : Input} (g : GraphMap i j)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (hands : RingWrittenPHReadings.CanonicalPhysicalAgreement j j.spatial (reindexed i j g.atoms))
    (root : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1) :
    ((rows i root k).map (fun row => (siteMap g row.1,row.2))).Perm (rows j (g.atoms root) k) := by
  have heights : height i = height j := (RingReportRenumber.schedule_height g.atSourceGeometry).trans
    (reindexed_height j (reindexed i j g.atoms) (reindexed_full _))
  exact rows_perm_of_entries (siteMap g) _ _
    (chemical_stored_keys_nodup i root k bound)
    (chemical_stored_keys_nodup j (g.atoms root) k (heights ▸ bound))
    (graph_sphereEntry g admitted hands root k bound)

/-- Under a branch exchange, the native table maps to itself after every sphere.
Distinct paths with the same terminal atom remain distinct rows. -/
theorem branch_rows {i : Input} (g : GraphMap i i)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (c : i.certified.TetrahedralCenter) (fixed : g.atoms c.val = c.val)
    (hands : BranchAgreement i c (reindexed i i g.atoms))
    (k : Nat) (bound : k ≤ height i + 1) :
    ((rows i c.val k).map (fun row => (siteMap g row.1,row.2))).Perm (rows i c.val k) :=
  rows_perm_of_entries (siteMap g) _ _
    (chemical_stored_keys_nodup i c.val k bound) (chemical_stored_keys_nodup i c.val k bound)
    (g.branch_stores admitted c fixed hands k bound)

/-- A row in an actual store is uniquely addressed. Its value is exactly the
recursive graph derivation for an eligible simple path whose sphere has committed. -/
theorem row_iff_derives {i : Input} (valid : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (r : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1) (q : Site i)
    (v : Option RingNestedActivePair.Labels) :
    (q,some v) ∈ rows i r k ↔
      ∃ h a, ∃ p : RingGraphPaths.Path i r h a, RingGraphPaths.Represents q r h a ∧
        a ≠ r ∧ eligible i a = true ∧ height i + 1 < h.length + k ∧
        RingEligibleGraph.Derives (eligible i) (RingChemicalGraphProof.Local i) r p v :=
  (row_iff_entry _ (chemical_stored_keys_nodup i r k bound) q (some v)).trans
    (sphereEntry_iff_derives valid r k bound q v)

end TetraStereo.Engine.RingSphereStore
assert_kernel_only TetraStereo.Engine.RingSphereStore.chemical_stored_perm
assert_kernel_only TetraStereo.Engine.RingSphereStore.branch_rows
assert_kernel_only TetraStereo.Engine.RingSphereStore.row_iff_derives
assert_kernel_only TetraStereo.Engine.RingSphereStore.spelling_rows
