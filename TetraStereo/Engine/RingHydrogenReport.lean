import TetraStereo.Engine.RingPopulationReport
import TetraStereo.Engine.RingHydrogenCertificate
import TetraStereo.Engine.RingPyramidalChoiceCoverage

set_option autoImplicit false
namespace TetraStereo.Engine.RingHydrogenReport
open OneCenter
open RingGroupedReport (Report)

abbrev GeometryInput := RawMolecule × SpatialConfiguration

open RingPyramidalChoices (Site choices)
open RingHydrogenCompletion (Point)

private def agrees (evaluate : List Point → Option Report) (rows : Report) :
    List Site → List Point → Bool
  | [], ps => evaluate ps == some rows
  | s :: rest, ps =>
      agrees evaluate rows rest (ps.set s.hydrogen s.plus) &&
      agrees evaluate rows rest (ps.set s.hydrogen s.minus)

private theorem agrees_iff (evaluate : List Point → Option Report) (rows : Report)
    (sites : List Site) (ps : List Point) :
    agrees evaluate rows sites ps = true ↔ ∀ v ∈ choices sites ps, evaluate v = some rows := by
  induction sites generalizing ps with
  | nil => simp [agrees,choices]
  | cons s rest ih => simp [agrees,choices,ih,List.mem_append,or_imp,forall_and]

/-- Read placements depth first, keeping the first complete report. Stop as soon as a
placement fails admission or differs at any requested atom. -/
def search? (evaluate : List Point → Option Report) : List Site → List Point → Option Report
  | [], ps => evaluate ps
  | s :: rest, ps => do
      let rows ← search? evaluate rest (ps.set s.hydrogen s.plus)
      guard (agrees evaluate rows rest (ps.set s.hydrogen s.minus))
      return rows

theorem search?_iff (evaluate : List Point → Option Report) (sites : List Site) (ps : List Point)
    (rows : Report) :
    search? evaluate sites ps = some rows ↔ ∀ v ∈ choices sites ps, evaluate v = some rows := by
  induction sites generalizing ps with
  | nil => simp [search?,choices]
  | cons s rest ih =>
    simp only [choices,List.mem_append,or_imp,forall_and,← ih,search?]
    cases h : search? evaluate rest (ps.set s.hydrogen s.plus) with
    | none => simp
    | some first =>
      cases ok : agrees evaluate first rest (ps.set s.hydrogen s.minus) <;> simp [guard,ok] <;>
        rintro rfl <;> simp_all
      · have missing : ¬ ∀ v ∈ choices rest (ps.set s.hydrogen s.minus), evaluate v = some first := by
          intro all
          have contradiction := ok.symm.trans ((agrees_iff ..).mpr all)
          cases contradiction
        simpa [not_forall] using missing
      · exact (agrees_iff ..).mp ok

structure PreparedGeometry where
  molecule : RawMolecule
  positions : List Point
  sites : List Site

def preparedSource? (source : LocalizedChemicalRing.Input) (ids : List Nat) :
    Option PreparedGeometry := do
  guard (LocalizedChemicalRing.coordinatesAdmitted source)
  guard (ids.all fun n => decide (n < source.molecule.atomCount))
  let (out,pos) ← RingHydrogenCompletion.prepare? source.molecule source.spatial
  return ⟨out,pos.positions,RingPyramidalChoices.sites source.molecule source.spatial out pos⟩

/-- On an admitted source with a full coordinate row and valid original IDs,
construction of the set of hydrogen placements always succeeds. -/
theorem preparedSource?_total (source : LocalizedChemicalRing.Input) (ids : List Nat)
    (geom : LocalizedChemicalRing.coordinatesAdmitted source = true)
    (full : source.spatial.positions.length = source.molecule.atomCount)
    (valid : ∀ n ∈ ids, n < source.molecule.atomCount) :
    ∃ p, preparedSource? source ids = some p := by
  obtain ⟨out,pos,prepared,_,_⟩ := RingHydrogenCertificate.prepare?_total _ _ source.admissible full
  refine ⟨⟨out,pos.positions,RingPyramidalChoices.sites source.molecule source.spatial out pos⟩,?_⟩
  simp [preparedSource?,geom,guard,prepared]
  rw [if_pos valid]
  rfl

def preparedGeometry? (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) :
    Option PreparedGeometry :=
  if (RingHydrogenCompletion.plan m).isEmpty then some ⟨m,g.positions,[]⟩ else do
    let source ← LocalizedChemicalRing.admitRawSpatial? m g
    preparedSource? source ids

abbrev Judgment := (i : LocalizedChemicalRing.Input) → List i.certified.Atom → Report → Prop

/-- Raw source and prepared graph witnesses for a single fully specified reading. -/
def Graph (judge : Judgment) (p : GeometryInput) (ids : List Nat) (rows : Report) : Prop :=
  ∃ source, LocalizedChemicalRing.admitRawSpatial? p.1 p.2 = some source ∧
    (∃ original : List source.certified.Atom, original.map Fin.val = ids) ∧
    ∃ i, RingChemicalReport.Prepared source i ∧ ∃ atoms : List i.certified.Atom,
      atoms.map Fin.val = ids ∧ judge i atoms rows

/-- Admission and agreement are evaluated for the whole request. In particular,
two placements that both give a completed refusal agree, while an assignment
and a refusal disagree. -/
def Exact (judge : Judgment) (m : RawMolecule) (g : SpatialConfiguration)
    (ids : List Nat) (rows : Report) : Prop :=
  ∃ prepared, preparedGeometry? m g ids = some prepared ∧
    ∀ ps ∈ choices prepared.sites prepared.positions, Graph judge (prepared.molecule,⟨ps⟩) ids rows

def fromRaw? (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) : Option Report := do
  let prepared ← preparedGeometry? m g ids
  search? (fun ps => RingChemicalReport.fromRaw? prepared.molecule ⟨ps⟩ ids)
    prepared.sites prepared.positions

private theorem exact_iff (judge : Judgment)
    (one : ∀ (p : GeometryInput) ids rows, RingChemicalReport.fromRaw? p.1 p.2 ids = some rows ↔ Graph judge p ids rows)
    (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) (rows : Report) :
    fromRaw? m g ids = some rows ↔ Exact judge m g ids rows := by
  simp only [fromRaw?,Option.bind_eq_bind,Option.bind_eq_some_iff,search?_iff,Exact]
  apply exists_congr
  intro p
  exact and_congr_right' (forall₂_congr fun ps _ => one (p.molecule,⟨ps⟩) ids rows)

theorem fromRaw_graph_iff (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) (rows : Report) :
    fromRaw? m g ids = some rows ↔ Exact RingChemicalReport.Correct m g ids rows :=
  exact_iff RingChemicalReport.Correct (fun p => RingChemicalReport.fromRaw_graph_iff p.1 p.2) m g ids rows

theorem fromRaw_population_iff (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) (rows : Report) :
    fromRaw? m g ids = some rows ↔ Exact RingPopulationReport.Correct m g ids rows :=
  exact_iff RingPopulationReport.Correct (fun p => RingPopulationReport.fromRaw_iff p.1 p.2) m g ids rows

/-- Structural and coordinate conditions for one fully specified geometry. -/
def Admitted (p : GeometryInput) (ids : List Nat) : Prop :=
  (∀ n ∈ ids, n < p.1.atomCount) ∧ ∃ source i, LocalizedChemicalRing.admitRawSpatial? p.1 p.2 = some source ∧
    RingChemicalReport.Prepared source i

/-- A request is decided exactly when preparation succeeds, every placement
admits the original requested rows, and no two graph derivations disagree. -/
theorem fromRaw_domain_iff (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) :
    (∃ rows, fromRaw? m g ids = some rows) ↔ ∃ p, preparedGeometry? m g ids = some p ∧
      (∀ ps ∈ choices p.sites p.positions, Admitted (p.molecule,⟨ps⟩) ids) ∧
      (∀ ps ∈ choices p.sites p.positions, ∀ qs ∈ choices p.sites p.positions, ∀ r s,
        Graph RingChemicalReport.Correct (p.molecule,⟨ps⟩) ids r →
        Graph RingChemicalReport.Correct (p.molecule,⟨qs⟩) ids s → r = s) := by
  constructor
  · rintro ⟨rows, got⟩
    obtain ⟨p,hp,uniform⟩ := (fromRaw_graph_iff ..).mp got
    have actual := fun ps hps => (RingChemicalReport.fromRaw_graph_iff ..).mpr (uniform ps hps)
    refine ⟨p,hp,fun ps hps => (RingChemicalReport.fromRaw_domain_iff ..).mp ⟨rows,actual ps hps⟩,?_⟩
    intro ps hps qs hqs r s hr hs
    have left := (RingChemicalReport.fromRaw_graph_iff ..).mpr hr
    have right := (RingChemicalReport.fromRaw_graph_iff ..).mpr hs
    exact Option.some.inj (left.symm.trans (actual ps hps)) |>.trans
      (Option.some.inj ((actual qs hqs).symm.trans right))
  · rintro ⟨p,hp,ready,agree⟩
    obtain ⟨ps,hps⟩ := RingPyramidalChoices.choices_exists p.sites p.positions
    obtain ⟨rows,got⟩ := (RingChemicalReport.fromRaw_domain_iff ..).mpr (ready ps hps)
    have base := (RingChemicalReport.fromRaw_graph_iff ..).mp got
    refine ⟨rows,(fromRaw_graph_iff ..).mpr ⟨p,hp,?_⟩⟩
    intro qs hqs
    obtain ⟨other,ho⟩ := (RingChemicalReport.fromRaw_domain_iff ..).mpr (ready qs hqs)
    have graph := (RingChemicalReport.fromRaw_graph_iff ..).mp ho
    simpa only [agree qs hqs ps hps other rows graph base] using graph

theorem fromRaw_closed_eq {m : RawMolecule} (closed : RingHydrogenCompletion.plan m = [])
    (g : SpatialConfiguration) (ids : List Nat) :
    fromRaw? m g ids = RingChemicalReport.fromRaw? m g ids := by
  simp [fromRaw?,preparedGeometry?,closed,search?]

theorem fromRaw_closed_total {m : RawMolecule} {g : SpatialConfiguration}
    {i : LocalizedChemicalRing.Input} (h : LocalizedChemicalRing.admitRawSpatial? m g = some i)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (positions : g.positions.length = m.atomCount) (closed : RingHydrogenCompletion.plan m = [])
    (ids : List Nat) (bounds : ∀ n ∈ ids, n < m.atomCount) :
    ∃! rows, fromRaw? m g ids = some rows := by
  rw [fromRaw_closed_eq closed]
  exact RingChemicalReport.fromRaw_closed_total h geom positions closed ids bounds

/-- If the remaining coordinates specify one hydrogen placement, making that
completion explicit preserves admission, all labels, and all completed refusals. -/
theorem fromRaw_materialized_eq {m out : RawMolecule} {g pos : SpatialConfiguration}
    {source : LocalizedChemicalRing.Input} (hs : LocalizedChemicalRing.admitRawSpatial? m g = some source)
    (geom : LocalizedChemicalRing.coordinatesAdmitted source = true)
    (hc : RingHydrogenCompletion.prepare? m g = some (out,pos))
    (fixed : RingPyramidalChoices.sites m g out pos = [])
    (ids : List Nat) (valid : ∀ n ∈ ids, n < m.atomCount) :
    fromRaw? m g ids = fromRaw? out pos ids := by
  rw [fromRaw_closed_eq (RingHydrogenCompletion.prepare?_closed hc)]
  by_cases closed : RingHydrogenCompletion.plan m = []
  · rw [fromRaw_closed_eq closed]
    exact RingChemicalReport.fromRaw_materialized_eq hs geom hc ids valid
  · obtain ⟨hm,hg⟩ := RingChemicalReport.admission_fields hs
    simp [fromRaw?,preparedGeometry?,preparedSource?,closed,hs,geom,guard,hm,hg,hc,fixed]
    rw [if_pos valid]
    rfl

private def forIds? (source : LocalizedChemicalRing.Input) (ids : List Nat) : Option Report := do
  let p ← preparedSource? source ids
  search? (fun ps => RingChemicalReport.fromRaw? p.molecule ⟨ps⟩ ids) p.sites p.positions

def forAtoms? (source : LocalizedChemicalRing.Input) (atoms : List source.certified.Atom) :=
  forIds? source (atoms.map Fin.val)

theorem forAtoms_iff (source : LocalizedChemicalRing.Input) (atoms : List source.certified.Atom) (rows : Report) :
    forAtoms? source atoms = some rows ↔ ∃ p, preparedSource? source (atoms.map Fin.val) = some p ∧
      ∀ ps ∈ choices p.sites p.positions, Graph RingChemicalReport.Correct
        (p.molecule,⟨ps⟩) (atoms.map Fin.val) rows := by
  simp only [forAtoms?,forIds?,Option.bind_eq_bind,Option.bind_eq_some_iff,search?_iff,
    Graph,RingChemicalReport.fromRaw_graph_iff]

def centres? (source : LocalizedChemicalRing.Input) : Option Report := do
  let i ← RingChemicalReport.prepared? source
  let atoms := (List.finRange i.certified.certified.input.molecule.atomCount).filter fun a =>
    a.val < source.molecule.atoms.length && RingPyramidalPublication.eligible i a
  forIds? source (atoms.map Fin.val)

def carbons? (source : LocalizedChemicalRing.Input) := forAtoms? source (RingGroupedReport.carbons source)

end TetraStereo.Engine.RingHydrogenReport

assert_kernel_only TetraStereo.Engine.RingHydrogenReport.fromRaw_graph_iff
assert_kernel_only TetraStereo.Engine.RingHydrogenReport.fromRaw_population_iff
assert_kernel_only TetraStereo.Engine.RingHydrogenReport.fromRaw_materialized_eq
assert_kernel_only TetraStereo.Engine.RingHydrogenReport.preparedSource?_total
