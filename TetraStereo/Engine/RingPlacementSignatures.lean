import TetraStereo.Engine.RingPhysicalSignatures

/-! A raw ring request with unresolved P–H positions is a consensus over
physical signatures on one fixed, completed molecular graph. -/
set_option autoImplicit false
noncomputable section
namespace TetraStereo.Engine.RingPhysicalSignatures
open OneCenter
open LocalizedChemicalRing (Input)
open RingHydrogenSpelling RingSpatialTransport RingHydrogenCompletion
open RingWrittenPHReadings RingPyramidalChoices
open RingGroupedReport (Report)

/-- Distinct signatures in the actual finite P–H placement search. -/
def placementSignatures (s i : Input) (ps : List (TwinPair i)) (y : SpatialConfiguration) :
    Finset (Signature i ps) := by
  classical
  exact ((variants s.molecule s.spatial i.molecule y).map (signature i ps)).toFinset

private theorem mem_placementSignatures (s i : Input) (ps : List (TwinPair i))
    (y : SpatialConfiguration) (t : Signature i ps) :
    t ∈ placementSignatures s i ps y ↔
      ∃ w ∈ variants s.molecule s.spatial i.molecule y, signature i ps w = t := by
  classical
  simp [placementSignatures]

private theorem variant_valid (s i : Input) {y w : SpatialConfiguration}
    (done : prepare? s.molecule s.spatial = some (i.molecule,y))
    (hy : y.positions.length = size i)
    (valid : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i y hy) = true)
    (mem : w ∈ variants s.molecule s.spatial i.molecule y) :
    ∃ hw : w.positions.length = size i,
      LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) = true := by
  let j := atGeometry i y hy
  have hw := (variants_positions_length mem).trans hy
  have p := variant_placement (prepare?_certified done) mem
  have gate := coordinates_of_same_ligands (i := j) (g := w) hw
    (fun c k => p.fixed _ (centers_unmoved (prepare?_certified done) j rfl c k))
  exact ⟨hw,gate.trans valid⟩

/-- A raw request succeeds with exactly these rows iff every represented physical
signature yields them. Multiple placements with the same signature count once. -/
theorem raw_iff_signature_consensus (s i : Input) (ps : List (TwinPair i))
    (separate : (ps.map TwinPair.c).Nodup) (y : SpatialConfiguration)
    (source : LocalizedChemicalRing.coordinatesAdmitted s = true)
    (done : prepare? s.molecule s.spatial = some (i.molecule,y))
    (hy : y.positions.length = size i)
    (valid : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i y hy) = true)
    (ids : List Nat) (bounds : ∀ n ∈ ids, n < s.molecule.atomCount) (rows : Report) :
    RingHydrogenReport.fromRaw? s.molecule s.spatial ids = some rows ↔
      ∀ t : Realized i ps, t.val ∈ placementSignatures s i ps y →
        RingHydrogenReport.fromRaw? i.molecule (representative t) ids = some rows := by
  rw [fromRaw_all_placements (readmit s) source done ids bounds rows]
  have same (t : Realized i ps) (w : SpatialConfiguration)
      (mem : w ∈ variants s.molecule s.spatial i.molecule y) (sign : signature i ps w = t.val) :
      RingHydrogenReport.fromRaw? i.molecule w ids =
        RingHydrogenReport.fromRaw? i.molecule (representative t) ids := by
    obtain ⟨hw,gw⟩ := variant_valid s i done hy valid mem
    obtain ⟨hr,gr,repr⟩ := representative_valid t
    exact signature_reports i ps separate (representative t) w hr hw gr gw
      (prepare?_closed done) (sign.trans repr.symm) ids
  constructor
  · intro all t sel
    obtain ⟨w,mem,sign⟩ := (mem_placementSignatures ..).mp sel
    rw [←same t w mem sign]
    exact all w (variant_placement (prepare?_certified done) mem)
  · intro all w placement
    obtain ⟨x,mem,matchRows⟩ := all_requests_represented done placement
    obtain ⟨hx,gx⟩ := variant_valid s i done hy valid mem
    let t : Realized i ps := ⟨signature i ps x,x,hx,gx,rfl⟩
    rw [matchRows ids,same t x mem rfl]
    exact all t ((mem_placementSignatures ..).mpr ⟨x,mem,rfl⟩)

/-- Matching sets of possible signs on the prepared graph suffice for equality
of the original requests, including a failure of consensus on any requested row. -/
theorem raw_eq_of_placementSignatures (s t i : Input) (ps : List (TwinPair i))
    (separate : (ps.map TwinPair.c).Nodup) (x y : SpatialConfiguration)
    (gs : LocalizedChemicalRing.coordinatesAdmitted s = true)
    (gt : LocalizedChemicalRing.coordinatesAdmitted t = true)
    (sx : prepare? s.molecule s.spatial = some (i.molecule,x))
    (ty : prepare? t.molecule t.spatial = some (i.molecule,y))
    (hx : x.positions.length = size i) (hy : y.positions.length = size i)
    (gx : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) = true)
    (gy : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i y hy) = true)
    (same : placementSignatures s i ps x = placementSignatures t i ps y)
    (ids : List Nat) (bs : ∀ n ∈ ids, n < s.molecule.atomCount)
    (bt : ∀ n ∈ ids, n < t.molecule.atomCount) :
    RingHydrogenReport.fromRaw? s.molecule s.spatial ids = RingHydrogenReport.fromRaw? t.molecule t.spatial ids := by
  have iffSome (rows : Report) : RingHydrogenReport.fromRaw? s.molecule s.spatial ids = some rows ↔
      RingHydrogenReport.fromRaw? t.molecule t.spatial ids = some rows := by
    rw [raw_iff_signature_consensus s i ps separate x gs sx hx gx ids bs rows, same,
      raw_iff_signature_consensus t i ps separate y gt ty hy gy ids bt rows]
  cases l : RingHydrogenReport.fromRaw? s.molecule s.spatial ids with
  | some rows => exact ((iffSome rows).mp l).symm
  | none =>
    cases r : RingHydrogenReport.fromRaw? t.molecule t.spatial ids with
    | none => rfl
    | some rows => exact (by simpa [l] using (iffSome rows).mpr r : False).elim

end TetraStereo.Engine.RingPhysicalSignatures
assert_kernel_only TetraStereo.Engine.RingPhysicalSignatures.raw_iff_signature_consensus
assert_kernel_only TetraStereo.Engine.RingPhysicalSignatures.raw_eq_of_placementSignatures

namespace TetraStereo.Engine.RingPhysicalSignatures
open OneCenter RingHydrogenSpelling RingSpatialTransport RingHydrogenCompletion
open LocalizedChemicalRing (Input)
open RingGroupedReport (Report)

/-- For each represented signature only one complete original-ID-indexed table
on the prepared graph is needed. The request may repeat indices or combine
individually determined and ambiguous atoms. Bounds refer to the source molecule. -/
theorem raw_iff_full_tables (s i : Input) (ps : List (TwinPair i))
    (separate : (ps.map TwinPair.c).Nodup) (y : SpatialConfiguration)
    (source : LocalizedChemicalRing.coordinatesAdmitted s = true)
    (done : prepare? s.molecule s.spatial = some (i.molecule,y))
    (hy : y.positions.length = size i)
    (valid : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i y hy) = true)
    (ids : List Nat) (rows : Report) :
    RingHydrogenReport.fromRaw? s.molecule s.spatial ids = some rows ↔
      (∀ n ∈ ids, n < s.molecule.atomCount) ∧
      ∀ t : Realized i ps, t.val ∈ placementSignatures s i ps y →
        (RingHydrogenReport.fromRaw? i.molecule (representative t) (List.range i.molecule.atomCount)).map
          (selectRows ids) = some rows := by
  by_cases bounded : ∀ n ∈ ids, n < s.molecule.atomCount
  · rw [raw_iff_signature_consensus s i ps separate y source done hy valid ids bounded rows,
      and_iff_right bounded]
    have inPrepared : ∀ n ∈ ids, n < i.molecule.atomCount :=
      fun n mem => (bounded n mem).trans_le (prepare?_certified done).atomCount_le
    apply forall_congr'
    intro t
    apply forall_congr'
    intro _
    obtain ⟨hr,gr,_⟩ := representative_valid t
    exact congrArg (· = some rows)
      (select_full_report (atGeometry i (representative t) hr) (prepare?_closed done) gr ids inPrepared) |>.to_iff
  · constructor
    · intro got
      obtain ⟨_,_,_,_,_,bounds,_,_⟩ := (RingWrittenPHReadings.fromRaw_iff_written_population ..).mp got
      exact (bounded bounds).elim
    · intro got
      exact (bounded got.1).elim

end TetraStereo.Engine.RingPhysicalSignatures
assert_kernel_only TetraStereo.Engine.RingPhysicalSignatures.raw_iff_full_tables

namespace TetraStereo.Engine.RingPhysicalSignatures
open OneCenter RingHydrogenSpelling RingSpatialTransport RingHydrogenCompletion RingPyramidalChoices
open LocalizedChemicalRing (Input)

/-- Each geometry visited by the raw P–H search has a selected representative
with the same full, addressed store at every root and every committed sphere. -/
theorem placement_rows (s i : Input) (ps : List (TwinPair i))
    (separate : (ps.map TwinPair.c).Nodup) (y w : SpatialConfiguration)
    (done : prepare? s.molecule s.spatial = some (i.molecule,y))
    (hy : y.positions.length = size i)
    (valid : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i y hy) = true)
    (picked : w ∈ variants s.molecule s.spatial i.molecule y) :
    ∃ t : Realized i ps, t.val ∈ placementSignatures s i ps y ∧
      ∃ hw : w.positions.length = size i, ∃ hr : (representative t).positions.length = size i,
      ∃ g : GraphMap i i, PairActions ps g ∧ ∀ root k,
        k ≤ RingActiveDistanceSchedule.height (atGeometry i w hw) + 1 →
        ((RingSphereStore.rows (atGeometry i w hw) root k).map (fun row =>
          (RingSphereStore.siteMap (g.atTables w (representative t) hw hr) row.1,row.2))).Perm
          (RingSphereStore.rows (atGeometry i (representative t) hr) (g.atoms root) k) := by
  obtain ⟨hw,gw⟩ := variant_valid s i done hy valid picked
  let t : Realized i ps := ⟨signature i ps w,w,hw,gw,rfl⟩
  obtain ⟨hr,gr,same⟩ := representative_valid t
  exact ⟨t,(mem_placementSignatures ..).mpr ⟨w,picked,rfl⟩,hw,hr,
    signature_rows i ps separate w (representative t) hw hr gw gr same⟩

end TetraStereo.Engine.RingPhysicalSignatures
assert_kernel_only TetraStereo.Engine.RingPhysicalSignatures.placement_rows
