import TetraStereo.Engine.RingFullPathConstitution
import TetraStereo.Engine.RingGraphAuxiliaries

/-! # Public full-path reports from raw molecular graphs and coordinates -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingMolecularReport
open OneCenter
open LocalizedChemicalRing (Input)
open RingGroupedReport (Report)
open RingFullPathReport (Correct)

def forAtoms? (i : Input) (atoms : List i.certified.Atom) : Option Report :=
  RingFullPathConstitution.fastReport i atoms

theorem forAtoms_iff {i : Input} (coord : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) (rows : Report) :
    forAtoms? i atoms = some rows ↔ Correct i atoms rows :=
  RingFullPathConstitution.fast_report_iff i coord atoms rows

/-- Detect all tetrahedral centers, including centers with a completed refusal. -/
def centres? (i : Input) := forAtoms? i (RingGroupedReport.centres i)

/-- Report on carbon atoms in input order. -/
def carbons? (i : Input) := forAtoms? i (RingGroupedReport.carbons i)

private def resolve (i : Input) (ids : List Nat) : Option (List i.certified.Atom) :=
  ids.mapM fun id => if h : id < i.certified.certified.input.molecule.atomCount then some ⟨id,h⟩ else none

private theorem resolve_iff (i : Input) (ids : List Nat) (atoms : List i.certified.Atom) :
    resolve i ids = some atoms ↔ atoms.map Fin.val = ids := by
  induction ids generalizing atoms with
  | nil => cases atoms <;> simp [resolve]
  | cons n ns ih =>
    simp only [resolve,List.mapM_cons]
    change (do let a ← (if h : n < _ then some (⟨n,h⟩ : i.certified.Atom) else none)
               let rest ← resolve i ns
               pure (a::rest)) = some atoms ↔ _
    by_cases bound : n < i.certified.certified.input.molecule.atomCount
    · simp only [dif_pos bound,Option.bind_eq_bind,Option.bind_some,Option.pure_def,
        Option.bind_eq_some_iff,Option.some.injEq]
      cases atoms with
      | nil => simp
      | cons a as =>
        simp only [List.cons.injEq,List.map_cons,ih]
        constructor
        · rintro ⟨t,ht,h,rfl⟩
          exact ⟨congrArg Fin.val h.symm,ht⟩
        · rintro ⟨ha,hs⟩
          exact ⟨as,hs,Fin.ext ha.symm,rfl⟩
    · simp only [dif_neg bound,Option.bind_eq_bind,Option.bind_none,reduceCtorEq,false_iff]
      cases atoms with
      | nil => simp
      | cons a as =>
        intro eqn
        exact bound ((List.cons.inj eqn).1 ▸ a.isLt)

/-- Atom IDs are zero-based. Invalid input, inadmissible coordinates or an
out-of-range ID fail the request. A completed refusal occupies its own row. -/
def fromRaw? (m : RawMolecule) (xyz : SpatialConfiguration) (ids : List Nat) : Option Report := do
  let i ← LocalizedChemicalRing.admitRawSpatial? m xyz
  guard (LocalizedChemicalRing.coordinatesAdmitted i)
  forAtoms? i (← resolve i ids)

/-- Characterize the raw API by molecular admission and the independent
recursive two-geometry derivation. Request order and multiplicity are explicit. -/
theorem fromRaw_iff (m : RawMolecule) (xyz : SpatialConfiguration) (ids : List Nat) (rows : Report) :
    fromRaw? m xyz ids = some rows ↔ ∃ i : Input, LocalizedChemicalRing.admitRawSpatial? m xyz = some i ∧
      LocalizedChemicalRing.coordinatesAdmitted i = true ∧ ∃ atoms : List i.certified.Atom,
      atoms.map Fin.val = ids ∧ Correct i atoms rows := by
  unfold fromRaw?
  cases adm : LocalizedChemicalRing.admitRawSpatial? m xyz with
  | none => simp
  | some i =>
    cases coord : LocalizedChemicalRing.coordinatesAdmitted i with
    | false => simp [coord,guard]
    | true =>
      simp only [Option.bind_eq_bind,Option.bind_some,coord,guard,if_true,Option.pure_def,
        Option.some.injEq,Option.bind_eq_some_iff]
      constructor
      · rintro ⟨atoms,got,ok⟩
        exact ⟨i,rfl,coord,atoms,(resolve_iff ..).mp got,(forAtoms_iff coord ..).mp ok⟩
      · rintro ⟨_,rfl,_,atoms,ids,proof⟩
        exact ⟨atoms,(resolve_iff ..).mpr ids,(forAtoms_iff coord ..).mpr proof⟩

/-- At every simple bonded path, the full-path source judgment derives
exactly the publication computed at that occurrence. -/
theorem path_iff {i : Input} (coord : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {r h a} (p : RingGraphPaths.Path i r h a) (v : Option RingNestedActivePair.Labels) :
    RingGraphAuxiliaries.Derives (RingFullPathPublication.TwoGeometry i) r p v ↔
      RingFullPathPublication.state i (RingGraphPaths.site p) = some v := by
  apply RingGraphAuxiliaries.derives_iff_store
  · intro q no
    exact (RingFullPathPublication.state_eq i q).trans (RingFullPathReport.skips i q _ no)
  · exact RingFullPathPublication.complete coord
  · intro q w
    rw [RingFullPathPublication.state_eq i q]
    exact (RingFullPathPublication.two_geometry_iff coord q _ (RingFullPathPublication.ready coord q) w).symm

private theorem graph_iff {i : Input} (coord : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) (rows : Report) :
    Correct i atoms rows ↔ RingGraphAuxiliaries.Report (RingFullPathPublication.TwoGeometry i) atoms rows := by
  have root (a : i.certified.Atom) (v : Option RingNestedActivePair.Labels) :
      RingFullPathPublication.Molecular i (RingGroupedReport.origin i a) v ↔
      RingGraphAuxiliaries.Derives (RingFullPathPublication.TwoGeometry i) a .origin v := by
    rw [path_iff coord,← RingFullPathPublication.molecular_iff coord]
    rw [RingGroupedReport.origin_unique (RingGraphPaths.site (.origin : RingGraphPaths.Path i a [a] a)) rfl]
    rfl
  exact ⟨fun h => h.imp (fun a row m => ⟨m.1,(root a row.2).mp m.2⟩),
    fun h => h.imp (fun a row m => ⟨m.1,(root a row.2).mpr m.2⟩)⟩

/-- From raw input to atom paths. Every requested row has an independent
two-geometry derivation, including every deeper auxiliary read from the graph. -/
theorem fromRaw_graph_iff (m : RawMolecule) (xyz : SpatialConfiguration) (ids : List Nat) (rows : Report) :
    fromRaw? m xyz ids = some rows ↔ ∃ i : Input, LocalizedChemicalRing.admitRawSpatial? m xyz = some i ∧
      LocalizedChemicalRing.coordinatesAdmitted i = true ∧ ∃ atoms : List i.certified.Atom,
      atoms.map Fin.val = ids ∧ RingGraphAuxiliaries.Report (RingFullPathPublication.TwoGeometry i) atoms rows := by
  rw [fromRaw_iff]
  exact ⟨fun ⟨i,hi,hg,a,ids,h⟩ => ⟨i,hi,hg,a,ids,(graph_iff hg a rows).mp h⟩,
    fun ⟨i,hi,hg,a,ids,h⟩ => ⟨i,hi,hg,a,ids,(graph_iff hg a rows).mpr h⟩⟩

end TetraStereo.Engine.RingMolecularReport
assert_kernel_only TetraStereo.Engine.RingMolecularReport.fromRaw_iff
assert_kernel_only TetraStereo.Engine.RingMolecularReport.fromRaw_graph_iff
