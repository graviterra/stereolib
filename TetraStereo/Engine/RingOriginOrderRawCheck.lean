import TetraStereo.Engine.RingOriginOrderCheck

/-! Streaming raw order-domain checking over the public preparation gates and
all implicit P–H choices. No chemical descriptor is evaluated. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginOrderRawCheck
open OneCenter
open LocalizedChemicalRing (Input)
open RingHydrogenCompletion (Point)
open RingPyramidalChoices (Site choices)
open RingRawComparisonLift (ChemicalTrace RawTrace)

/-- A missing placement dominates a negative order certificate. -/
def combine : Option Bool → Option Bool → Option Bool
  | some a, some b => some (a && b)
  | _, _ => none

private theorem combine_true (a b : Option Bool) :
    combine a b = some true ↔ a = some true ∧ b = some true := by
  cases a <;> cases b <;> simp [combine]

private theorem combine_none (a b : Option Bool) :
    combine a b = none ↔ a = none ∨ b = none := by
  cases a <;> cases b <;> simp [combine]

/-- Traverse the two placements depth first without constructing their product. -/
def search (evaluate : List Point → Option Bool) : List Site → List Point → Option Bool
  | [], ps => evaluate ps
  | s :: rest, ps => combine
      (search evaluate rest (ps.set s.hydrogen s.plus))
      (search evaluate rest (ps.set s.hydrogen s.minus))

theorem search_true (evaluate : List Point → Option Bool) (sites : List Site) (ps : List Point) :
    search evaluate sites ps = some true ↔ ∀ p ∈ choices sites ps, evaluate p = some true := by
  induction sites generalizing ps with
  | nil => simp [search,choices]
  | cons s rest ih => simp [search,combine_true,choices,ih,List.mem_append,or_imp,forall_and]

theorem search_none (evaluate : List Point → Option Bool) (sites : List Site) (ps : List Point) :
    search evaluate sites ps = none ↔ ∃ p ∈ choices sites ps, evaluate p = none := by
  induction sites generalizing ps with
  | nil => simp [search,choices]
  | cons s rest ih => simp [search,combine_none,choices,ih,List.mem_append,or_and_right,exists_or]

theorem search_false (evaluate : List Point → Option Bool) (sites : List Site) (ps : List Point)
    (failed : search evaluate sites ps = some false) :
    ∃ p ∈ choices sites ps, evaluate p = some false := by
  induction sites generalizing ps with
  | nil => exact ⟨ps,by simp [choices],failed⟩
  | cons s rest ih =>
    have branch : search evaluate rest (ps.set s.hydrogen s.plus) = some false ∨
        search evaluate rest (ps.set s.hydrogen s.minus) = some false := by
      have h := failed
      simp only [search] at h
      cases a : search evaluate rest (ps.set s.hydrogen s.plus) <;>
        cases b : search evaluate rest (ps.set s.hydrogen s.minus) <;>
        simp_all [combine]
      rename_i x y
      cases x <;> cases y <;> simp_all
    rcases branch with left | right
    · obtain ⟨p,mem,hit⟩ := ih _ left
      exact ⟨p,by simp [choices,mem],hit⟩
    · obtain ⟨p,mem,hit⟩ := ih _ right
      exact ⟨p,by simp [choices,mem],hit⟩

/-- The exact single-placement preparation, ending with the finite order test. -/
def chemical (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) : Option Bool := do
  let source ← LocalizedChemicalRing.admitRawSpatial? m g
  let original ← RingMolecularReport.resolve source ids
  let i ← RingChemicalReport.prepared? source
  let atoms ← RingMolecularReport.resolve i (original.map Fin.val)
  return atoms.all (RingOriginOrderCheck.check i)

theorem chemical_iff (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) (b : Bool) :
    chemical m g ids = some b ↔ ∃ i atoms, ChemicalTrace m g ids i atoms ∧
      atoms.all (RingOriginOrderCheck.check i) = b := by
  simp only [chemical,ChemicalTrace,Option.bind_eq_bind,Option.bind_eq_some_iff]
  aesop

theorem chemical_trace {m g ids i atoms} (trace : ChemicalTrace m g ids i atoms) :
    chemical m g ids = some (atoms.all (RingOriginOrderCheck.check i)) := by
  obtain ⟨source,admit,original,oldIDs,prepared,newIDs⟩ := trace
  simp [chemical,admit,oldIDs,prepared,newIDs]

/-- `none` means a public preparation gate failed in at least one placement;
`some false` means preparation succeeded but an order test failed. -/
def check (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) : Option Bool := do
  let p ← RingHydrogenReport.preparedGeometry? m g ids
  search (fun ps => chemical p.molecule ⟨ps⟩ ids) p.sites p.positions

theorem true_iff (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) :
    check m g ids = some true ↔ ∃ p, RingHydrogenReport.preparedGeometry? m g ids = some p ∧
      ∀ ps ∈ choices p.sites p.positions, ∃ i atoms,
        ChemicalTrace p.molecule ⟨ps⟩ ids i atoms ∧
          ∀ r ∈ atoms, RingOriginOrderDomain.Qualifies i r := by
  simp only [check,Option.bind_eq_bind,Option.bind_eq_some_iff,search_true,chemical_iff,
    List.all_eq_true,RingOriginOrderCheck.check_iff]

theorem true_sound {m g ids} (ok : check m g ids = some true)
    {i atoms} (trace : RawTrace m g ids i atoms) :
    ∀ r ∈ atoms, RingOriginOrderDomain.Qualifies i r := by
  obtain ⟨p,hp,ps,mem,typed⟩ := trace
  have all : search (fun ps => chemical p.molecule ⟨ps⟩ ids) p.sites p.positions = some true := by
    simpa [check,hp] using ok
  have hit := (search_true _ _ _).mp all ps mem
  rw [chemical_trace typed] at hit
  exact fun r hr => RingOriginOrderCheck.sound ((List.all_eq_true.mp (Option.some.inj hit)) r hr)

theorem raw_exact {m g ids} (ok : check m g ids = some true) :
    RingOriginMetricReport.fromRaw? m g ids = RingHydrogenReport.fromRaw? m g ids :=
  RingOriginOrderDomain.raw_exact m g ids (fun _ _ trace => true_sound ok trace)

theorem rows_exact {m g ids} (ok : check m g ids = some true)
    {i atoms} (trace : RawTrace m g ids i atoms) {r : i.certified.Atom} (mem : r ∈ atoms) (batches : Nat) :
    RingOriginMetricReport.rows i r batches = RingSphereStore.rows i r batches :=
  RingOriginOrderDomain.rows_exact trace.admitted (true_sound ok trace r mem) batches

/-- Failure of the sufficient domain test supplies an actual reached root
outside that domain. It makes no assertion about descriptor disagreement. -/
theorem false_sound {m g ids} (failed : check m g ids = some false) :
    ∃ i atoms, RawTrace m g ids i atoms ∧ ∃ r ∈ atoms, ¬ RingOriginOrderDomain.Qualifies i r := by
  classical
  obtain ⟨p,hp,hit⟩ := Option.bind_eq_some_iff.mp failed
  obtain ⟨ps,mem,bad⟩ := search_false _ _ _ hit
  obtain ⟨i,atoms,trace,negative⟩ := (chemical_iff _ _ _ false).mp bad
  refine ⟨i,atoms,⟨p,hp,ps,mem,trace⟩,?_⟩
  by_contra! all
  have yes : atoms.all (RingOriginOrderCheck.check i) = true :=
    List.all_eq_true.mpr (fun r hr => RingOriginOrderCheck.complete (all r hr))
  rw [negative] at yes
  contradiction

private theorem chemical_failed (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (failed : chemical m g ids = none) (evaluate : RingRawComparisonLift.TypedEvaluation) :
    RingRawComparisonLift.chemicalWith evaluate m g ids = none := by
  unfold chemical at failed
  unfold RingRawComparisonLift.chemicalWith RingRawComparisonLift.preparedWith
  cases ha : LocalizedChemicalRing.admitRawSpatial? m g with
  | none => simp
  | some source =>
    cases ho : RingMolecularReport.resolve source ids with
    | none => simp [ho]
    | some original =>
      cases hp : RingChemicalReport.prepared? source with
      | none => simp [ho,hp]
      | some i =>
        cases hn : RingMolecularReport.resolve i (original.map Fin.val) with
        | none => simp [ho,hp,hn]
        | some atoms => simp [ha,ho,hp,hn] at failed

private theorem failed_evaluation {m g ids} (failed : check m g ids = none)
    (evaluate : RingRawComparisonLift.TypedEvaluation) :
    RingRawComparisonLift.fromRaw evaluate m g ids = none := by
  unfold RingRawComparisonLift.fromRaw
  cases hp : RingHydrogenReport.preparedGeometry? m g ids with
  | none => simp
  | some p =>
    have gone : search (fun ps => chemical p.molecule ⟨ps⟩ ids) p.sites p.positions = none := by
      simpa [check,hp] using failed
    obtain ⟨ps,mem,bad⟩ := (search_none _ _ _).mp gone
    simp only [Option.bind_eq_bind,Option.bind_some]
    cases result : RingHydrogenReport.search?
        (fun ps => RingRawComparisonLift.chemicalWith evaluate p.molecule ⟨ps⟩ ids) p.sites p.positions with
    | none => rfl
    | some rows =>
      have hit := (RingHydrogenReport.search?_iff _ _ _ _).mp result ps mem
      rw [chemical_failed _ _ _ bad evaluate] at hit
      contradiction

/-- A preparation failure forces both full raw responses to be absent,
independently of any order-domain assertion. -/
theorem none_sound {m g ids} (failed : check m g ids = none) :
    RingOriginMetricReport.fromRaw? m g ids = none ∧ RingHydrogenReport.fromRaw? m g ids = none :=
  ⟨failed_evaluation failed _, by rw [← RingRawComparisonLift.native]; exact failed_evaluation failed _⟩

end TetraStereo.Engine.RingOriginOrderRawCheck
assert_kernel_only TetraStereo.Engine.RingOriginOrderRawCheck.true_iff
assert_kernel_only TetraStereo.Engine.RingOriginOrderRawCheck.raw_exact
assert_kernel_only TetraStereo.Engine.RingOriginOrderRawCheck.rows_exact
assert_kernel_only TetraStereo.Engine.RingOriginOrderRawCheck.none_sound

assert_kernel_only TetraStereo.Engine.RingOriginOrderRawCheck.false_sound
