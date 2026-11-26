import TetraStereo.Engine.RingHydrogenReport

/-! Arbitrary typed evaluations lifted through the exact public raw preparation,
original-ID resolution, admission gates and implicit P–H consensus procedure. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingRawComparisonLift
open OneCenter
open LocalizedChemicalRing (Input)
open RingGroupedReport (Report)

abbrev TypedEvaluation := (i : Input) → List i.certified.Atom → Option Report

def preparedWith (evaluate : TypedEvaluation) (source : Input) (original : List source.certified.Atom) : Option Report := do
  let i ← RingChemicalReport.prepared? source
  evaluate i (← RingMolecularReport.resolve i (original.map Fin.val))

def chemicalWith (evaluate : TypedEvaluation) (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) : Option Report := do
  let source ← LocalizedChemicalRing.admitRawSpatial? m g
  preparedWith evaluate source (← RingMolecularReport.resolve source ids)

/-- Replace only the final typed evaluation. Every public raw gate and every
branch of implicit P–H agreement remains the actual public operation. -/
def fromRaw (evaluate : TypedEvaluation) (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) : Option Report := do
  let p ← RingHydrogenReport.preparedGeometry? m g ids
  RingHydrogenReport.search? (fun ps => chemicalWith evaluate p.molecule ⟨ps⟩ ids) p.sites p.positions

/-- Exact native specialization, with no admission, closure or conformance premise. -/
theorem native : fromRaw RingChemicalReport.report? = RingHydrogenReport.fromRaw? := rfl

def judgment (evaluate : TypedEvaluation) : RingHydrogenReport.Judgment := fun i atoms rows => evaluate i atoms = some rows

theorem chemical_graph_iff (evaluate : TypedEvaluation) (m : RawMolecule) (g : SpatialConfiguration)
    (ids : List Nat) (rows : Report) :
    chemicalWith evaluate m g ids = some rows ↔ RingHydrogenReport.Graph (judgment evaluate) (m,g) ids rows := by
  simp only [chemicalWith,preparedWith,Option.bind_eq_bind,Option.bind_eq_some_iff,
    RingChemicalReport.prepared_iff,RingMolecularReport.resolve_iff]
  constructor
  · rintro ⟨source,admit,original,oldIDs,i,prepared,atoms,newIDs,evaluated⟩
    exact ⟨source,admit,⟨original,oldIDs⟩,i,prepared,atoms,newIDs.trans oldIDs,evaluated⟩
  · rintro ⟨source,admit,⟨original,oldIDs⟩,i,prepared,atoms,newIDs,evaluated⟩
    exact ⟨source,admit,original,oldIDs,i,prepared,atoms,newIDs.trans oldIDs.symm,evaluated⟩

/-- A successful raw result is exactly admission and agreement of the whole
request on every public implicit P–H choice, evaluated by the supplied typed rule. -/
theorem fromRaw_iff (evaluate : TypedEvaluation) (m : RawMolecule) (g : SpatialConfiguration)
    (ids : List Nat) (rows : Report) :
    fromRaw evaluate m g ids = some rows ↔ RingHydrogenReport.Exact (judgment evaluate) m g ids rows := by
  simp only [fromRaw,Option.bind_eq_bind,Option.bind_eq_some_iff,RingHydrogenReport.search?_iff,
    RingHydrogenReport.Exact]
  apply exists_congr
  intro p
  exact and_congr_right' (forall₂_congr fun ps _ => chemical_graph_iff evaluate p.molecule ⟨ps⟩ ids rows)

/-- An actual typed call reached through the public single-placement pipeline. -/
def ChemicalTrace (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (i : Input) (atoms : List i.certified.Atom) : Prop :=
  ∃ source, LocalizedChemicalRing.admitRawSpatial? m g = some source ∧
    ∃ original : List source.certified.Atom, RingMolecularReport.resolve source ids = some original ∧
      RingChemicalReport.prepared? source = some i ∧
      RingMolecularReport.resolve i (original.map Fin.val) = some atoms

/-- The outer public preparation and one of its actual P–H coordinate choices,
followed by a fully admitted and resolved typed call. -/
def RawTrace (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (i : Input) (atoms : List i.certified.Atom) : Prop :=
  ∃ p, RingHydrogenReport.preparedGeometry? m g ids = some p ∧
    ∃ ps ∈ RingPyramidalChoices.choices p.sites p.positions,
      ChemicalTrace p.molecule ⟨ps⟩ ids i atoms

theorem ChemicalTrace.prepared {m g ids i atoms} (trace : ChemicalTrace m g ids i atoms) :
    ∃ source, RingChemicalReport.Prepared source i := by
  obtain ⟨source,_,original,_,prepared,_⟩ := trace
  exact ⟨source,(RingChemicalReport.prepared_iff source i).mp prepared⟩

theorem ChemicalTrace.ids {m g ids i atoms} (trace : ChemicalTrace m g ids i atoms) : atoms.map Fin.val = ids := by
  obtain ⟨source,_,original,oldIDs,_,newIDs⟩ := trace
  exact ((RingMolecularReport.resolve_iff i _ atoms).mp newIDs).trans
    ((RingMolecularReport.resolve_iff source ids original).mp oldIDs)

theorem RawTrace.ids {m g ids i atoms} (trace : RawTrace m g ids i atoms) : atoms.map Fin.val = ids := by
  obtain ⟨_,_,_,_,typed⟩ := trace
  exact typed.ids

theorem RawTrace.admitted {m g ids i atoms} (trace : RawTrace m g ids i atoms) :
    LocalizedChemicalRing.coordinatesAdmitted i = true := by
  obtain ⟨_,_,_,_,typed⟩ := trace
  obtain ⟨_,_,_,_,_,_,admitted⟩ := typed.prepared
  exact admitted

theorem search_congr (left right : List RingHydrogenCompletion.Point → Option Report)
    (sites : List RingPyramidalChoices.Site) (ps : List RingHydrogenCompletion.Point)
    (agree : ∀ p ∈ RingPyramidalChoices.choices sites ps, left p = right p) :
    RingHydrogenReport.search? left sites ps = RingHydrogenReport.search? right sites ps := by
  apply Option.ext
  intro rows
  rw [RingHydrogenReport.search?_iff,RingHydrogenReport.search?_iff]
  exact forall₂_congr (fun p member => by rw [agree p member])

theorem search_difference (left right : List RingHydrogenCompletion.Point → Option Report)
    (sites : List RingPyramidalChoices.Site) (ps : List RingHydrogenCompletion.Point)
    (different : RingHydrogenReport.search? left sites ps ≠ RingHydrogenReport.search? right sites ps) :
    ∃ p ∈ RingPyramidalChoices.choices sites ps, left p ≠ right p := by
  classical
  by_contra absent
  push_neg at absent
  exact different (search_congr left right sites ps absent)

theorem chemical_difference (left right : TypedEvaluation) (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (different : chemicalWith left m g ids ≠ chemicalWith right m g ids) :
    ∃ i atoms, ChemicalTrace m g ids i atoms ∧ left i atoms ≠ right i atoms := by
  unfold chemicalWith preparedWith at different
  cases admit : LocalizedChemicalRing.admitRawSpatial? m g with
  | none => simp [admit] at different
  | some source =>
    rw [admit] at different
    simp only [Option.bind_eq_bind,Option.bind_some] at different
    cases oldIDs : RingMolecularReport.resolve source ids with
    | none => simp [oldIDs] at different
    | some original =>
      rw [oldIDs] at different
      simp only [Option.bind_some] at different
      cases prepared : RingChemicalReport.prepared? source with
      | none => simp [prepared] at different
      | some i =>
        rw [prepared] at different
        simp only [Option.bind_some] at different
        cases newIDs : RingMolecularReport.resolve i (original.map Fin.val) with
        | none => simp [newIDs] at different
        | some atoms =>
          rw [newIDs] at different
          simp only [Option.bind_some] at different
          exact ⟨i,atoms,⟨source,admit,original,oldIDs,prepared,newIDs⟩,different⟩

/-- Any raw difference, including failure versus success or a P–H consensus
failure, reaches an actual prepared typed evaluation where the rules differ. -/
theorem difference (left right : TypedEvaluation) (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (different : fromRaw left m g ids ≠ fromRaw right m g ids) :
    ∃ i atoms, RawTrace m g ids i atoms ∧ left i atoms ≠ right i atoms := by
  unfold fromRaw at different
  cases prepared : RingHydrogenReport.preparedGeometry? m g ids with
  | none => simp [prepared] at different
  | some p =>
    rw [prepared] at different
    simp only [Option.bind_eq_bind,Option.bind_some] at different
    obtain ⟨ps,member,localDifference⟩ := search_difference _ _ p.sites p.positions different
    obtain ⟨i,atoms,trace,typedDifference⟩ := chemical_difference left right p.molecule ⟨ps⟩ ids localDifference
    exact ⟨i,atoms,⟨p,prepared,ps,member,trace⟩,typedDifference⟩

/-- Agreement only on calls reachable from this raw request suffices. -/
theorem congr (left right : TypedEvaluation) (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (agree : ∀ i atoms, RawTrace m g ids i atoms → left i atoms = right i atoms) :
    fromRaw left m g ids = fromRaw right m g ids := by
  classical
  by_contra different
  obtain ⟨i,atoms,trace,failed⟩ := difference left right m g ids different
  exact failed (agree i atoms trace)

/-- Native/raw agreement requires only prepared typed agreement, not a raw output premise. -/
theorem eq_native (evaluate : TypedEvaluation) (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (agree : ∀ i atoms, RawTrace m g ids i atoms → evaluate i atoms = RingChemicalReport.report? i atoms) :
    fromRaw evaluate m g ids = RingHydrogenReport.fromRaw? m g ids := by
  rw [←native]
  exact congr evaluate RingChemicalReport.report? m g ids agree

/-- A typed theorem on admitted inputs lifts to every raw request, including
requests rejected before a typed call is reached. -/
theorem eq_native_of_admitted (evaluate : TypedEvaluation)
    (agree : ∀ i atoms, LocalizedChemicalRing.coordinatesAdmitted i = true →
      evaluate i atoms = RingChemicalReport.report? i atoms) :
    fromRaw evaluate = RingHydrogenReport.fromRaw? := by
  funext m g ids
  apply eq_native evaluate m g ids
  intro i atoms trace
  exact agree i atoms trace.admitted

/-- A raw discrepancy has a fully admitted typed witness with the same requested
original IDs, in their original order and with repetitions preserved. -/
theorem difference_admitted (left right : TypedEvaluation) (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (different : fromRaw left m g ids ≠ fromRaw right m g ids) :
    ∃ i atoms, RawTrace m g ids i atoms ∧ LocalizedChemicalRing.coordinatesAdmitted i = true ∧
      atoms.map Fin.val = ids ∧ left i atoms ≠ right i atoms := by
  obtain ⟨i,atoms,trace,failed⟩ := difference left right m g ids different
  exact ⟨i,atoms,trace,trace.admitted,trace.ids,failed⟩

assert_kernel_only eq_native_of_admitted
assert_kernel_only difference_admitted
assert_kernel_only native
assert_kernel_only fromRaw_iff
assert_kernel_only difference
assert_kernel_only eq_native
end TetraStereo.Engine.RingRawComparisonLift
