import TetraStereo.Engine.RingGraphCache
import TetraStereo.Engine.RingGraphLocal

/-! A complete report calculated from molecular paths and coordinates in the frozen
auxiliary profile. Each requested atom starts its own simple path. -/

set_option autoImplicit false

namespace TetraStereo.Engine.RingGraphReport
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingGraphPaths (Path site)
open RingActiveDistanceSchedule (Cell frozen)
open RingNestedActivePair (Labels)

/-- Reconstruct every branch priority (including duplicate mass zero), apply the molecular
marks, and read the coordinates. All recursive descriptor requests follow atom paths. -/
def atPath {i : Input} {r h a} (p : Path i r h a) : Cell :=
  RingGraphAuxiliaries.value (RingRebuiltStereo.publish i) p

theorem atPath_exact {i : Input} (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {r h a} (p : Path i r h a) : atPath p = RingGroupedPublication.state i (site p) := by
  apply RingGraphAuxiliaries.value_exact
  intro q
  have step := RingActiveDistanceSchedule.evaluate_eq (RingRebuiltStereo.publish i) q
  rw [RingRebuiltStereo.state_exact i coords] at step
  exact step.symm

/-- Each path has a covered result. The inner option distinguishes a completed refusal
from an assigned pair of molecular letters. -/
theorem unique_value {i : Input} (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {r h a} (p : Path i r h a) : ∃! v : Option Labels, atPath p = some v := by
  rw [atPath_exact coords]
  obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp
    (RingGroupedPublication.complete (RingGroupedGeometry.physical coords) (site p))
  exact ⟨v,hv,fun _ hw => Option.some.inj (hw.symm.trans hv)⟩

def report (i : Input) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun a => (atPath (Path.origin (i := i) (root := a))).map fun v => (a.val,v)

theorem report_exact (i : Input) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) : report i atoms = RingGroupedReport.forAtoms? i atoms := by
  have root (a : i.certified.Atom) : site (Path.origin (i := i) (root := a)) = RingGroupedReport.origin i a :=
    RingGroupedReport.origin_unique _ rfl
  simp only [report,atPath_exact coords,root]
  rfl

/-- A graph proof has one independent local judgement per visited path; the two
geometries each get their own strict ligand orders and coordinate readbacks. -/
abbrev Derivation {i r h a} (p : Path i r h a) (v : Option Labels) :=
  RingGraphAuxiliaries.Derives (RingGraphLocal.Decides i) r p v

theorem derivation_iff {i : Input} (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {r h a} (p : Path i r h a) (v : Option Labels) :
    Derivation p v ↔ atPath p = some v := by
  rw [atPath_exact coords]
  exact RingGraphAuxiliaries.derives_iff coords (RingGraphLocal.Decides.iff_state coords) p v

private theorem consistent {i r h a} {p : Path i r h a} {v} (proof : Derivation p v) :
    v.all RingNestedActivePair.consistent = true := by
  cases proof with
  | step _ _ observed _ => exact observed.consistency

/-- Construct a finite proof from the deepest bonded paths inward. Local totality on
ready molecular readings and the atom-count bound suffice for existence. Uniqueness
follows by comparing the two derivation trees at their children. -/
theorem path_derivation {i : Input} (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {r h a} (p : Path i r h a) : ∃! v, Derivation p v := by
  classical
  have build (n : Nat) : ∀ {h a} (p : Path i r h a),
      i.certified.certified.input.molecule.atomCount < h.length + n → ∃ v, Derivation p v := by
    induction n with
    | zero =>
      intro h a p enough
      have size := RingGraphAuxiliaries.length_bound p
      omega
    | succ n ih =>
      intro h a p enough
      have child {k b} (c : Path i r k b) (longer : h.length < k.length) : ∃ v, Derivation c v :=
        ih c (by omega)
      let next {k b} (c : Path i r k b) :=
        if longer : h.length < k.length then (child c longer).choose else none
      have checked {k b} (c : Path i r k b) (longer : h.length < k.length) : Derivation c (next c) := by
        simp only [next,dif_pos longer]
        exact (child c longer).choose_spec
      have ready := RingGraphAuxiliaries.reader_ready p next (fun c longer _ _ => consistent (checked c longer))
      obtain ⟨v,localProof⟩ := RingGraphLocal.Decides.inhabited coords ready
      exact ⟨v,.step p next localProof (fun c longer _ _ => checked c longer)⟩
  obtain ⟨v,proof⟩ := build (i.certified.certified.input.molecule.atomCount+1) p (by omega)
  exact ⟨v,proof,fun w other => RingGraphAuxiliaries.Derives.unique (law := RingGraphLocal.Decides i)
    (fun _ _ _ _ x y => RingGraphLocal.Decides.unique x y) other proof⟩

/-- Real occurrences get their molecular path proof. A duplicate is a structural absence. -/
def Explains {i : Input} (q : RingActivePairs.Site i) (v : Option Labels) : Prop :=
  (q.val.node.provenance ≠ .realAtom ∧ v = none) ∨
    ∃ a, ∃ p : Path i q.val.root q.val.node.history a,
      RingGraphPaths.Represents q q.val.root q.val.node.history a ∧ Derivation p v

theorem occurrence_exact {i : Input} (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : RingActivePairs.Site i) (v : Option Labels) :
    Explains q v ↔ RingGroupedPublication.state i q = some v := by
  have result {a} (p : Path i q.val.root q.val.node.history a)
      (rep : RingGraphPaths.Represents q q.val.root q.val.node.history a) :
      Derivation p v ↔ RingGroupedPublication.state i q = some v := by
    rw [derivation_iff coords,atPath_exact coords,
      RingGraphPaths.unique_site (RingGraphPaths.represents_site p) rep]
  by_cases real : q.val.node.provenance = .realAtom
  · obtain ⟨a,atom,p⟩ := RingGraphPaths.site_path q real
    have rep : RingGraphPaths.Represents q q.val.root q.val.node.history a := ⟨rfl,rfl,real,atom⟩
    constructor
    · rintro (⟨bad,_⟩ | ⟨b,other,hr,hv⟩)
      · exact (bad real).elim
      · exact (result other hr).mp hv
    · intro h
      exact Or.inr ⟨a,p,rep,(result p rep).mpr h⟩
  · have missing : i.certified.localizedOccurrenceDescriptorCenter? q = none := by
      cases h : i.certified.localizedOccurrenceDescriptorCenter? q with
      | none => rfl
      | some c => exact (real ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mp h).1).elim
    have blank := (RingGraphLocal.Decides.iff_state coords q none).mp (.absent missing)
    rw [blank]
    constructor
    · rintro (⟨_,rfl⟩ | ⟨a,p,rep,_⟩)
      · rfl
      · exact (real rep.2.2.1).elim
    · intro h
      exact Or.inl ⟨real,(Option.some.inj h).symm⟩

abbrev DerivedReport (i : Input) := RingGraphAuxiliaries.Report (RingGraphLocal.Decides i)

/-- Exact row-by-row correspondence, retaining requested order and repeated atoms. -/
theorem report_iff (i : Input) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) (rows : RingGroupedReport.Report) :
    DerivedReport i atoms rows ↔ RingGroupedReport.forAtoms? i atoms = some rows :=
  RingGraphAuxiliaries.report_iff coords (RingGraphLocal.Decides.iff_state coords) atoms rows

/-- Derive the complete report from the graph by visiting the requested atoms in order. -/
theorem unique_derived_report (i : Input) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) : ∃! rows, DerivedReport i atoms rows := by
  induction atoms with
  | nil =>
    exact ⟨[],.nil,fun other proof => by cases proof; rfl⟩
  | cons a atoms ih =>
    obtain ⟨v,hv,only⟩ := path_derivation coords (Path.origin (i := i) (root := a))
    obtain ⟨rows,tail,uniqueTail⟩ := ih
    refine ⟨(a.val,v)::rows,.cons ⟨rfl,hv⟩ tail,?_⟩
    intro other h
    cases h with
    | cons first rest =>
      obtain ⟨id,tree⟩ := first
      exact congrArg₂ List.cons (Prod.ext id (only _ tree)) (uniqueTail _ rest)

/-- The molecular graph has one derivable report, and both the direct calculation
and the grouped evaluator issue it. -/
theorem whole_report (i : Input) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) :
    ∃! rows, DerivedReport i atoms rows ∧ report i atoms = some rows ∧
      RingGroupedReport.forAtoms? i atoms = some rows := by
  obtain ⟨rows,proof,unique⟩ := unique_derived_report i coords atoms
  have issued := (report_iff i coords atoms rows).mp proof
  exact ⟨rows,⟨proof,(report_exact i coords atoms).trans issued,issued⟩,fun _ h => unique _ h.1⟩

/-- Materialize deeper cells once during each root evaluation. The auxiliary inventory is
enumerated from bonds. The direct path recursion specifies the result of every lookup. -/
def cachedReport (i : Input) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun a => (RingGraphCache.root i a).map fun v => (a.val,v)

theorem cached_exact (i : Input) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) : cachedReport i atoms = report i atoms := by
  rw [report_exact i coords]
  simp only [cachedReport,RingGraphCache.root_exact coords]
  rfl

private def requested (i : Input) (ids : List Nat) : Option (List i.certified.Atom) :=
  ids.mapM fun id => if ok : id < i.certified.certified.input.molecule.atomCount then some ⟨id,ok⟩ else none

/-- Bind raw bond records, rational coordinates and requested atom IDs at a single boundary. -/
def fromRaw (m : RawMolecule) (xyz : SpatialConfiguration) (ids : List Nat) : Option RingGroupedReport.Report := do
  let i ← LocalizedChemicalRing.admitRawSpatial? m xyz
  guard (LocalizedChemicalRing.coordinatesAdmitted i)
  cachedReport i (← requested i ids)

theorem raw_exact (m : RawMolecule) (xyz : SpatialConfiguration) (ids : List Nat) :
    fromRaw m xyz ids = (do
      let i ← LocalizedChemicalRing.admitRawSpatial? m xyz
      guard (LocalizedChemicalRing.coordinatesAdmitted i)
      RingGroupedReport.forAtoms? i (← requested i ids)) := by
  unfold fromRaw
  cases adm : LocalizedChemicalRing.admitRawSpatial? m xyz with
  | none => rfl
  | some i =>
    cases coord : LocalizedChemicalRing.coordinatesAdmitted i with
    | false => simp [coord,guard]
    | true => simp [coord,cached_exact i coord,report_exact i coord]

end TetraStereo.Engine.RingGraphReport

assert_kernel_only TetraStereo.Engine.RingGraphReport.atPath_exact
assert_kernel_only TetraStereo.Engine.RingGraphReport.unique_value
assert_kernel_only TetraStereo.Engine.RingGraphReport.report_exact
assert_kernel_only TetraStereo.Engine.RingGraphReport.raw_exact
assert_kernel_only TetraStereo.Engine.RingGraphReport.path_derivation
assert_kernel_only TetraStereo.Engine.RingGraphReport.occurrence_exact
assert_kernel_only TetraStereo.Engine.RingGraphReport.report_iff
assert_kernel_only TetraStereo.Engine.RingGraphReport.whole_report
assert_kernel_only TetraStereo.Engine.RingGraphReport.unique_derived_report
assert_kernel_only TetraStereo.Engine.RingGraphReport.cached_exact
