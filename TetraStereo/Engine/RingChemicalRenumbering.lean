import TetraStereo.Engine.RingFullPathKeyTransport
import TetraStereo.Engine.RingPyramidalRenumbering
import TetraStereo.Engine.RingTetrahedralRenumbering
import TetraStereo.Engine.RingHydrogenPlacementExact

/-! Atom renumbering for the chemical ring evaluator and its executable sphere stores. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingReportRenumber
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingActiveDistanceSchedule (View frozen Visible)
open RingGeometryExchange (Carrier Frozen Marked)
open RingRawRenumbering (AtomMap)
open RingRawRenumbering.AtomMap (arm site carrier)
open RingFullPathKeyTransport (key_transport valid_child)
variable {i j : Input}

/-- Occurrence agreement is enough to transport a site's entire frozen reader. -/
theorem frozen_carrier (r : AtomMap i j) (c : Carrier i j) (f : Site i) (s : View i) (t : View j)
    (occ : ∀ u, c.domain u → (c.image u).occurrence = site r u.occurrence)
    (earlier : ∀ u, Visible f u → s u = t (site r u)) :
    Frozen c (frozen s f) (frozen t (site r f)) := by
  intro u hu
  rw [occ u hu]
  exact frozen_site r f s t earlier u.occurrence

theorem frozen_actual (r : AtomMap i j) (f : Site i) (s : View i) (t : View j)
    (earlier : ∀ u, Visible f u → s u = t (site r u)) :
    Frozen (carrier r) (frozen s f) (frozen t (site r f)) :=
  frozen_carrier r (carrier r) f s t (fun _ _ => rfl) earlier

/-- Every retained direction is a valid aligned cursor on the original focus root. -/
theorem incident_facts (f : Site i) (u : Arm i)
    (mem : u ∈ RingRetainedAuxiliary.frame i.certified f) :
    i.certified.cursorPreviousRootAligned u ∧ i.certified.LocalizedRerootCursorValid u ∧
      u.occurrence.val.root = f.val.root := by
  have child : u ∈ i.certified.executableLocalizedRerootChildren (⟨f,none⟩ : Arm i) := mem
  refine ⟨i.certified.executableLocalizedRerootChildren_cursorAligned _ _ child,
    i.certified.localizedRerootChild_valid _ _ _
      (i.certified.executableLocalizedRerootChildren_declarative _) child,?_⟩
  exact i.certified.localizedRerootChildren_root_eq _ _ _
    (i.certified.executableLocalizedRerootChildren_declarative _) child

/-- Actual chemical frozen stores have identical full-path keys on every incident cursor.
The only store-agreement premise is the distance-induction hypothesis. -/
theorem chemical_incident_key (r : AtomMap i j)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (f : Site i)
    (earlier : ∀ u, Visible f u → RingChemicalGraphProof.state i u =
      RingChemicalGraphProof.state j (site r u)) (rev : Bool) (u : Arm i)
    (mem : u ∈ RingRetainedAuxiliary.frame i.certified f) :
    RingFullPathEligibility.key? j (frozen (RingChemicalGraphProof.state j) (site r f)) rev (arm r u) =
      RingFullPathEligibility.key? i (frozen (RingChemicalGraphProof.state i) f) rev u := by
  have facts := incident_facts f u mem
  exact key_transport (carrier r) (frozen_actual r f _ _ earlier)
    (RingChemicalGraphProof.ready geom f)
    (RingChemicalGraphProof.ready (RingRawRenumbering.AtomMap.coordinates r geom) (site r f))
    rev facts.1 facts.2.1 facts.2.2
    (valid_child r (i.certified.cursorPreviousRootAligned_of_none (⟨f,none⟩ : Arm i) rfl) mem)
    (congrArg r.atoms facts.2.2)

theorem marked_nat (r : AtomMap i j) (n : Nat) : Marked (carrier r) n (renameId r n) := by
  by_cases h : n < i.certified.certified.input.molecule.atomCount
  · simpa [renameId,h] using RingRawRenumbering.AtomMap.mark r (⟨n,h⟩ : i.certified.Atom)
  · intro u _
    have sizeEq : i.certified.certified.input.molecule.atomCount = j.certified.certified.input.molecule.atomCount := by
      simpa using Fintype.card_congr r.atoms
    have h' : ¬ n < j.certified.certified.input.molecule.atomCount := by omega
    unfold RingGroupedMark.bit
    change (u.occurrence.val.node.current?.map Fin.val == some n).toNat =
      ((arm r u).occurrence.val.node.current?.map Fin.val == some (renameId r n)).toNat
    rw [id_current]
    cases hc : u.occurrence.val.node.current? with
    | none => rfl
    | some a =>
      have na : a.val ≠ n := by have := a.isLt; omega
      have nb : (r.atoms a).val ≠ n := by have := (r.atoms a).isLt; omega
      simp [renameId,h,beq_eq_false_iff_ne.mpr na,beq_eq_false_iff_ne.mpr nb]

/-- Molecular marked words on incident directions, including invalid Nat mark IDs. -/
theorem chemical_incident_word (r : AtomMap i j)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (f : Site i)
    (earlier : ∀ u, Visible f u → RingChemicalGraphProof.state i u =
      RingChemicalGraphProof.state j (site r u)) (n : Nat) (u : Arm i)
    (mem : u ∈ RingRetainedAuxiliary.frame i.certified f) :
    (RingGroupedMark.arm? j (frozen (RingChemicalGraphProof.state j) (site r f))
      (renameId r n) (arm r u)).map (fun b => b.2.word) =
    (RingGroupedMark.arm? i (frozen (RingChemicalGraphProof.state i) f) n u).map (fun b => b.2.word) := by
  have facts := incident_facts f u mem
  obtain ⟨left,hl⟩ := RingGroupedMark.arm_ready (RingChemicalGraphProof.ready geom f) n u facts.2.1 facts.2.2
  obtain ⟨right,hr⟩ := RingGroupedMark.arm_ready
    (RingChemicalGraphProof.ready (RingRawRenumbering.AtomMap.coordinates r geom) (site r f))
    (renameId r n) (arm r u)
    (valid_child r (i.certified.cursorPreviousRootAligned_of_none (⟨f,none⟩ : Arm i) rfl) mem)
    (congrArg r.atoms facts.2.2)
  have eq := (carrier r).mark (frozen_actual r f _ _ earlier) (marked_nat r n) facts.1
    (RingGroupedMark.arm_source hl).2 (RingGroupedMark.arm_source hr).2
  rw [hl,hr]
  exact congrArg (fun x => some x.word) eq.symm

end TetraStereo.Engine.RingReportRenumber
assert_kernel_only TetraStereo.Engine.RingReportRenumber.chemical_incident_key
assert_kernel_only TetraStereo.Engine.RingReportRenumber.chemical_incident_word

namespace TetraStereo.Engine.RingReportRenumber
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingRawRenumbering (AtomMap)
open RingRawRenumbering.AtomMap (site)
open RingActiveDistanceSchedule (Visible height distance frozen)
open RingChemicalGraphProof (state)
open RingPyramidalPublication (focusP)
variable {i j : Input}

/-- At every occurrence, the two native evaluators produce the same publication.
Only strictly deeper visible occurrences contribute to the induction step. -/
theorem publications (r : AtomMap i j) (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) : state i q = state j (site r q) := by
  suffices ∀ n (f : Site i), height i - distance f = n → state i f = state j (site r f) from this _ q rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f level
    have earlier (v : Site i) (seen : Visible f v) : state i v = state j (site r v) := by
      have upper := RingActiveDistanceSchedule.distance_bound v
      have deeper := seen.2.1
      exact ih _ (by omega) v rfl
    rw [RingChemicalGraphProof.state_eq i f,RingChemicalGraphProof.state_eq j (site r f)]
    have keys := chemical_incident_key r geom f earlier
    cases hp : focusP i f with
    | none => exact (publish_tetra_rename r geom f hp earlier keys).symm
    | some a =>
      exact (publish_phosphorus_rename r _ _ f a hp (chemical_incident_word r geom f earlier) keys).symm
end TetraStereo.Engine.RingReportRenumber
assert_kernel_only TetraStereo.Engine.RingReportRenumber.publications

namespace TetraStereo.Engine.RingReportRenumber
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingRawRenumbering (AtomMap)
open RingRawRenumbering.AtomMap (site)
open RingActiveDistanceSchedule (View distance height)
open RingPyramidalPublication (eligible publish)
variable {i j : Input}

theorem eligible_atom (r : AtomMap i j) (a : i.certified.Atom) :
    eligible j (r.atoms a) = eligible i a := by
  simp only [eligible, phosphorus_atom r, ← Fintype.card_congr (neighbors r a)]

theorem site_distance (r : AtomMap i j) (q : Site i) :
    distance (site r q) = distance q := by
  have before := i.certified.carrierOccurrence_history_length_eq_address_succ q
  have after := j.certified.carrierOccurrence_history_length_eq_address_succ (site r q)
  change (q.val.node.history.map r.atoms).length = (site r q).val.address.length + 1 at after
  rw [List.length_map] at after
  change distance (site r q) = distance q
  unfold distance
  omega

theorem schedule_height (r : AtomMap i j) : height i = height j := by
  have upper (a b : Input) (f : Site a → Site b)
      (depth : ∀ q, distance (f q) = distance q) : height a ≤ height b := by
    have all (xs : List (Site a)) : xs.foldr (fun q n => max (distance q) n) 0 ≤ height b := by
      induction xs with
      | nil => exact Nat.zero_le _
      | cons q xs ih =>
        simp only [List.foldr_cons]
        exact max_le (by rw [← depth q]; exact RingActiveDistanceSchedule.distance_bound _) ih
    exact all _
  exact Nat.le_antisymm (upper i j (site r) (site_distance r))
    (upper j i (site r.symm) (site_distance r.symm))

theorem candidate_site (r : AtomMap i j) (root : i.certified.Atom) (q : Site i) :
    RingEligibleGraph.candidate (eligible j) (r.atoms root) (site r q) ↔
      RingEligibleGraph.candidate (eligible i) root q := by
  unfold RingEligibleGraph.candidate RingEligibleGraph.Eligible
  cases h : q.val.node.current? with
  | none => simp [site, RingRawRenumbering.nodeMap, h]
  | some a => simp [site, RingRawRenumbering.nodeMap, h, eligible_atom]

/-- Membership in the real executable simple-path queue preserves both masking and distance. -/
theorem chemical_queue_member (r : AtomMap i j) (root : i.certified.Atom)
    (d : Nat) (q : Site i) :
    site r q ∈ RingEligibleGraph.queue j (eligible j) (r.atoms root) d ↔
      q ∈ RingEligibleGraph.queue i (eligible i) root d := by
  rw [RingEligibleGraph.inventory, RingEligibleGraph.inventory, candidate_site, site_distance]

/-- The batches may be enumerated independently in either numbering, in any order. -/
theorem after_sphere_of_inventory (r : AtomMap i j)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) {left : Nat → List (Site i)} {right : Nat → List (Site j)}
    (source : RingEligibleGraph.Inventory (eligible i) root left)
    (target : RingEligibleGraph.Inventory (eligible j) (r.atoms root) right)
    (k : Nat) (bound : k ≤ height i + 1) (q : Site i) :
    RingSphereQueue.run (publish i) root left k q =
      RingSphereQueue.run (publish j) (r.atoms root)
        right k (site r q) := by
  rw [RingEligibleGraph.run_exact (RingChemicalGraphProof.skips i) source k bound,
    RingEligibleGraph.run_exact (RingChemicalGraphProof.skips j) target k
      (by rw [← schedule_height r]; exact bound)]
  simp only [candidate_site, site_distance, ← schedule_height r]
  change (if _ then RingChemicalGraphProof.state i q else _) =
    (if _ then RingChemicalGraphProof.state j (site r q) else _)
  rw [publications r admitted q]

/-- Exact publication store after each completed distance sphere of the actual executable queue. -/
theorem chemical_after_sphere (r : AtomMap i j)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1) (q : Site i) :
    RingSphereQueue.run (publish i) root (RingEligibleGraph.queue i (eligible i) root) k q =
      RingSphereQueue.run (publish j) (r.atoms root)
        (RingEligibleGraph.queue j (eligible j) (r.atoms root)) k (site r q) :=
  after_sphere_of_inventory r admitted root (RingEligibleGraph.inventory i (eligible i) root)
    (RingEligibleGraph.inventory j (eligible j) (r.atoms root)) k bound q

/-- The root query is evaluated only after all its auxiliary spheres have committed. -/
theorem chemical_root (r : AtomMap i j)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) :
    RingChemicalGraphProof.root i root = RingChemicalGraphProof.root j (r.atoms root) := by
  rw [RingChemicalGraphProof.root, RingChemicalGraphProof.root,
    RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i),
    RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips j)]
  exact (publications r admitted (RingGroupedReport.origin i root)).trans (congrArg (RingChemicalGraphProof.state j) (site_origin r root))

/-- Operational root masking also commutes at each intermediate store. -/
theorem chemical_reader_after_sphere (r : AtomMap i j)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1) (q : Site i) :
    RingSphereQueue.reader root
      (RingSphereQueue.run (publish i) root (RingEligibleGraph.queue i (eligible i) root) k) q =
    RingSphereQueue.reader (r.atoms root)
      (RingSphereQueue.run (publish j) (r.atoms root)
        (RingEligibleGraph.queue j (eligible j) (r.atoms root)) k) (site r q) := by
  unfold RingSphereQueue.reader
  change (if q.val.root = root then _ else _) =
    (if r.atoms q.val.root = r.atoms root then _ else _)
  simp only [r.atoms.injective.eq_iff, chemical_after_sphere r admitted root k bound q]

theorem chemical_fastRoot (r : AtomMap i j)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) :
    RingChemicalGraphProof.fastRoot i root = RingChemicalGraphProof.fastRoot j (r.atoms root) := by
  rw [RingChemicalGraphProof.fastRoot_exact, RingChemicalGraphProof.fastRoot_exact]
  exact chemical_root r admitted root

/-- The actual selected chemical report keeps query order, all assignments/refusals,
and changes only its atom identifiers. -/
theorem chemical_report (r : AtomMap i j)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) :
    RingChemicalReport.report? j (atoms.map r.atoms) =
      (RingChemicalReport.report? i atoms).map (List.map (RingRawRenumbering.AtomMap.renameRow r)) := by
  induction atoms with
  | nil => rfl
  | cons a rest ih =>
    simp only [RingChemicalReport.report?, List.map_cons, List.mapM_cons]
    change (do let v ← (RingChemicalGraphProof.root j (r.atoms a)).map (fun l => ((r.atoms a).val,l))
               let vs ← RingChemicalReport.report? j (rest.map r.atoms)
               pure (v :: vs)) = Option.map _ (do
                 let v ← (RingChemicalGraphProof.root i a).map (fun l => (a.val,l))
                 let vs ← RingChemicalReport.report? i rest
                 pure (v :: vs))
    rw [← chemical_root r admitted, ih]
    cases RingChemicalGraphProof.root i a <;>
      cases RingChemicalReport.report? i rest <;>
      simp [RingRawRenumbering.AtomMap.renameRow, a.isLt]

/-- One admitted source produces complete public reports in both numberings. -/
theorem chemical_reports_complete (r : AtomMap i j)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) :
    ∃ rows, RingChemicalReport.report? i atoms = some rows ∧
      RingChemicalReport.report? j (atoms.map r.atoms) =
        some (rows.map (RingRawRenumbering.AtomMap.renameRow r)) := by
  obtain ⟨rows, correct⟩ := RingChemicalReport.report_total admitted atoms
  have source := (RingChemicalReport.report_iff i admitted atoms rows).mpr correct
  exact ⟨rows, source, by rw [chemical_report r admitted atoms, source]; rfl⟩

assert_kernel_only chemical_reader_after_sphere
assert_kernel_only chemical_fastRoot
assert_kernel_only chemical_report
assert_kernel_only chemical_reports_complete
assert_kernel_only chemical_queue_member
assert_kernel_only chemical_after_sphere
assert_kernel_only chemical_root
end TetraStereo.Engine.RingReportRenumber

namespace TetraStereo.Engine.RingReportRenumber
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingRawRenumbering (AtomMap)
open RingRawRenumbering.AtomMap (site)
open RingActiveDistanceSchedule (Cell View Rule height)
open RingPyramidalPublication (eligible publish)

/-- Optional actual table entry: `none` is an unwritten address; `some none` is a stored
failed evaluation. The extra option is retained, unlike `viewOf`'s default lookup. -/
def storedEntry {i : Input} (rows : List (Site i × Cell)) (q : Site i) : Option Cell :=
  (rows.find? (fun row => decide (row.1 = q))).map Prod.snd

def storedPresent {i : Input} (rows : List (Site i × Cell)) (q : Site i) : Prop :=
  ∃ value, (q,value) ∈ rows

theorem storedPresent_succ {i : Input} (rule : Rule i) (root : i.certified.Atom)
    (queue : Nat → List (Site i)) (top k : Nat) (q : Site i) :
    storedPresent (RingSphereQueue.stored rule root queue top (k+1)) q ↔
      q ∈ queue (top-k) ∨ storedPresent (RingSphereQueue.stored rule root queue top k) q := by
  simp only [storedPresent, RingSphereQueue.stored, List.mem_append, List.mem_map]
  constructor
  · rintro ⟨value, (⟨x,member,eq⟩ | old)⟩
    · have same : x = q := congrArg Prod.fst eq
      subst x
      exact Or.inl member
    · exact Or.inr ⟨value,old⟩
  · rintro (member | ⟨value,old⟩)
    · exact ⟨_,Or.inl ⟨q,member,rfl⟩⟩
    · exact ⟨value,Or.inr old⟩

theorem storedEntry_presence {i : Input} (rows : List (Site i × Cell)) (q : Site i) :
    (storedEntry rows q).isSome = true ↔ storedPresent rows q := by
  simp only [storedEntry, Option.isSome_map, List.find?_isSome, decide_eq_true_eq, storedPresent]
  constructor
  · rintro ⟨⟨key,value⟩,member,eq⟩
    exact ⟨value,eq ▸ member⟩
  · rintro ⟨value,member⟩
    exact ⟨(q,value),member,rfl⟩

/-- Actual materialized tables contain corresponding addressed entries after every batch. -/
theorem chemical_stored_presence {i j : Input} (r : AtomMap i j)
    (root : i.certified.Atom) (k : Nat) (q : Site i) :
    storedPresent (RingSphereQueue.stored (publish i) root
      (RingEligibleGraph.queue i (eligible i) root) (height i) k) q ↔
    storedPresent (RingSphereQueue.stored (publish j) (r.atoms root)
      (RingEligibleGraph.queue j (eligible j) (r.atoms root)) (height j) k) (site r q) := by
  induction k with
  | zero => simp [storedPresent,RingSphereQueue.stored]
  | succ k ih =>
    rw [storedPresent_succ, storedPresent_succ, ← schedule_height r, chemical_queue_member]
    apply or_congr Iff.rfl
    simpa only [schedule_height r] using ih

private theorem option_eq_of_presence {α : Type} (a b : Option α) (default : α)
    (present : a.isSome = b.isSome) (values : a.getD default = b.getD default) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Exact actual first-match table cell, preserving the distinction between an unwritten
address, a stored refusal, and a stored failure, after every executable sphere. -/
theorem chemical_stored_entry {i j : Input} (r : AtomMap i j)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1) (q : Site i) :
    storedEntry (RingSphereQueue.stored (publish i) root
      (RingEligibleGraph.queue i (eligible i) root) (height i) k) q =
    storedEntry (RingSphereQueue.stored (publish j) (r.atoms root)
      (RingEligibleGraph.queue j (eligible j) (r.atoms root)) (height j) k) (site r q) := by
  apply option_eq_of_presence _ _ (some none)
  · apply Bool.eq_iff_iff.mpr
    rw [storedEntry_presence, storedEntry_presence]
    exact chemical_stored_presence r root k q
  · change RingSphereQueue.viewOf _ q = RingSphereQueue.viewOf _ (site r q)
    rw [RingSphereQueue.stored_eq, RingSphereQueue.stored_eq]
    exact chemical_after_sphere r admitted root k bound q

private theorem actual_row_of_entry {i : Input} (rows : List (Site i × Cell)) (q : Site i) :
    rows.find? (fun row => decide (row.1 = q)) = (storedEntry rows q).map (fun value => (q,value)) := by
  cases found : rows.find? (fun row => decide (row.1 = q)) with
  | none => simp [storedEntry,found]
  | some row =>
    have key0 := List.find?_some (p := fun row : Site i × Cell => decide (row.1 = q)) found
    have key : row.1 = q := by simpa using key0
    simp only [storedEntry, found, Option.map_some]
    exact congrArg some (Prod.ext key rfl)

/-- The actual first matching addressed row itself corresponds, before any defaulting. -/
theorem chemical_stored_addressed_row {i j : Input} (r : AtomMap i j)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1) (q : Site i) :
    ((RingSphereQueue.stored (publish i) root
      (RingEligibleGraph.queue i (eligible i) root) (height i) k).find?
        (fun row => decide (row.1 = q))).map (fun row => (site r row.1,row.2)) =
    (RingSphereQueue.stored (publish j) (r.atoms root)
      (RingEligibleGraph.queue j (eligible j) (r.atoms root)) (height j) k).find?
        (fun row => decide (row.1 = site r q)) := by
  rw [actual_row_of_entry, actual_row_of_entry, ← chemical_stored_entry r admitted root k bound q]
  simp only [Option.map_map]
  rfl

assert_kernel_only chemical_stored_addressed_row
assert_kernel_only chemical_stored_presence
assert_kernel_only chemical_stored_entry
end TetraStereo.Engine.RingReportRenumber

namespace TetraStereo.Engine.RingReportRenumber
open OneCenter
open RingRawRenumbering (AtomMap)
open RingRawRenumbering.AtomMap (coordinates renameRow)
open LocalizedChemicalRing (Input)
open RingHydrogenCompletion (plan)
open RingWrittenPHReadings (fromRaw_closed_report)
variable {i j : Input}

private theorem index_bound (r : AtomMap i j) (n : Nat) :
    renameId r n < j.molecule.atomCount ↔ n < i.molecule.atomCount := by
  have left := i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1
  have right := j.molecule.toSemanticMolecule?_atomCount _ j.agreement.1
  have card : i.certified.certified.input.molecule.atomCount = j.certified.certified.input.molecule.atomCount := by
    simpa using Fintype.card_congr r.atoms
  unfold renameId
  split
  · rename_i hn
    exact iff_of_true (right ▸ (r.atoms ⟨n,hn⟩).isLt) (left ▸ hn)
  · omega

private theorem closed_reject {k : Input} (cl : plan k.molecule = []) (ids : List Nat)
    (bad : ¬ ((∀ n ∈ ids, n < k.molecule.atomCount) ∧ LocalizedChemicalRing.coordinatesAdmitted k = true)) :
    RingHydrogenReport.fromRaw? k.molecule k.spatial ids = none := by
  cases found : RingHydrogenReport.fromRaw? k.molecule k.spatial ids with
  | none => rfl
  | some rows =>
    rw [RingHydrogenReport.fromRaw_closed_eq cl] at found
    exact (bad ((RingSpatialTransport.closed_domain k cl ids).mp ⟨rows,found⟩)).elim

/-- All raw requests on completed graphs, including invalid indices and failed
coordinate admission. Only atom identifiers are changed in a successful report. -/
theorem closed_raw_report (r : AtomMap i j) (cl : plan i.molecule = []) (cl' : plan j.molecule = [])
    (ids : List Nat) :
    RingHydrogenReport.fromRaw? j.molecule j.spatial (ids.map (renameId r)) =
      (RingHydrogenReport.fromRaw? i.molecule i.spatial ids).map (List.map (renameRow r)) := by
  have domain : ((∀ n ∈ ids.map (renameId r), n < j.molecule.atomCount) ∧
        LocalizedChemicalRing.coordinatesAdmitted j = true) ↔
      ((∀ n ∈ ids, n < i.molecule.atomCount) ∧ LocalizedChemicalRing.coordinatesAdmitted i = true) := by
    simp only [List.forall_mem_map,index_bound]
    exact and_congr_right' ⟨coordinates r.symm,coordinates r⟩
  by_cases ok : (∀ n ∈ ids, n < i.molecule.atomCount) ∧ LocalizedChemicalRing.coordinatesAdmitted i = true
  · have sizeEq := i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1
    let as : List i.certified.Atom := ids.attach.map fun n => ⟨n.val,by rw [sizeEq]; exact ok.1 _ n.property⟩
    have raw : as.map Fin.val = ids := by simp [as,List.map_map,Function.comp_def]
    have renamed : (as.map r.atoms).map Fin.val = ids.map (renameId r) := by
      rw [←raw]; simp [List.map_map,Function.comp_def]
    rw [←renamed,←raw,fromRaw_closed_report i cl ok.2,fromRaw_closed_report j cl' (coordinates r ok.2)]
    exact chemical_report r ok.2 as
  · rw [closed_reject cl ids ok,closed_reject cl' _ (mt domain.mp ok)]
    rfl
end TetraStereo.Engine.RingReportRenumber

assert_kernel_only TetraStereo.Engine.RingReportRenumber.closed_raw_report

namespace TetraStereo.Engine.RingReportRenumber
open OneCenter
open LocalizedChemicalRing (Input)

/-- Two source spellings may each append hydrogens. If both preparations fix a
single placement and the completed graphs are related by the raw bijection,
the original API calls agree for requests valid on both source molecules. -/
theorem materialized_raw_report {s t i j : Input} (r : RingRawRenumbering.AtomMap i j)
    (geom : LocalizedChemicalRing.coordinatesAdmitted s = true)
    (geom' : LocalizedChemicalRing.coordinatesAdmitted t = true)
    (left : RingHydrogenCompletion.prepare? s.molecule s.spatial = some (i.molecule,i.spatial))
    (right : RingHydrogenCompletion.prepare? t.molecule t.spatial = some (j.molecule,j.spatial))
    (fixed : RingPyramidalChoices.sites s.molecule s.spatial i.molecule i.spatial = [])
    (fixed' : RingPyramidalChoices.sites t.molecule t.spatial j.molecule j.spatial = [])
    (ids : List Nat) (bounds : ∀ n ∈ ids, n < s.molecule.atomCount)
    (bounds' : ∀ n ∈ ids.map (renameId r), n < t.molecule.atomCount) :
    RingHydrogenReport.fromRaw? t.molecule t.spatial (ids.map (renameId r)) =
      (RingHydrogenReport.fromRaw? s.molecule s.spatial ids).map (List.map (RingRawRenumbering.AtomMap.renameRow r)) := by
  rw [RingHydrogenReport.fromRaw_materialized_eq (RingSpatialTransport.readmit t) geom' right fixed' _ bounds',
    RingHydrogenReport.fromRaw_materialized_eq (RingSpatialTransport.readmit s) geom left fixed _ bounds]
  exact closed_raw_report r (RingHydrogenCompletion.prepare?_closed left)
    (RingHydrogenCompletion.prepare?_closed right) ids
end TetraStereo.Engine.RingReportRenumber
assert_kernel_only TetraStereo.Engine.RingReportRenumber.materialized_raw_report
