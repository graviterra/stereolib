import TetraStereo.Engine.RingResidualPairDecision
import TetraStereo.Engine.RingSparseTwinReport

/-! Ordinary ligand comparisons at reached tetrahedral sites, including sites
whose public schedule jumps straight to nominated Rule 6 trials. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOrdinaryPairVerdict
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActivePairReport (Slot)
open RingNestedActivePair (Frame Reader)
open RingActiveDistanceSchedule (height)
open RingResidualPairDecision (Table TableExact Classification HasExchange classify)
open private matrix matrix_exact from TetraStereo.Engine.RingResidualPairDecision
open private keys_exact from TetraStereo.Engine.RingFullPathPublication
open private frame_eq from TetraStereo.Engine.RingGroupedReport

/-- Reconstruct the public reader immediately preceding the specified batch. -/
def reader (i : Input) (root : i.certified.Atom) (batch : Nat) :=
  RingSphereQueue.reader root (RingSphereQueue.viewOf
    (RingSparseTwinReport.sparse i root (height i + 1 - batch)))

theorem reader_eq {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {root : i.certified.Atom} {batch : Nat} {f : Site i}
    (called : RingGlobalComparison.Called i root batch f) :
    reader i root batch = RingGlobalComparison.prior i root batch := by
  have bound : batch ≤ height i + 1 := called.elim (fun h => h.1.le) (fun h => h.1.le)
  unfold reader RingGlobalComparison.prior
  rw [(RingSparseTwinReport.sparse_exact geom root _).2,
    show height i+1-(height i+1-batch) = batch by omega]

/-- Compare the four ligands on an already materialized reader. -/
def onReader? {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (rev : Bool) :
    Option Table := (RingFullPathPublication.keys? fr r rev).map fun ks => matrix ks (fun _ => [])

/-- All sixteen ordered pairs before nomination, for the chosen geometry. -/
def table? (i : Input) (root : i.certified.Atom) (batch : Nat) (f : Site i) (rev : Bool) :
    Option Table := do
  let fr ← RingNestedActivePair.frame? i f
  onReader? fr (reader i root batch) rev

theorem at_call {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {root : i.certified.Atom} {batch : Nat} {f : Site i}
    (called : RingGlobalComparison.Called i root batch f) (fr : Frame i f) (rev : Bool) :
    table? i root batch f rev = onReader? fr (RingGlobalComparison.prior i root batch) rev := by
  simp [table?,frame_eq fr,reader_eq geom called]

/-- Every direction and first deciding stage agrees with all legal ordinary
readings on the actual prior store. A tie means equality through Rule 5. -/
theorem exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {root : i.certified.Atom} {batch : Nat} {f : Site i}
    (called : RingGlobalComparison.Called i root batch f) (fr : Frame i f) (rev : Bool) :
    ∃ t, table? i root batch f rev = some t ∧
      TableExact fr (RingGlobalComparison.prior i root batch) rev none t := by
  have ready : RingGroupedStereo.Ready f (RingGlobalComparison.prior i root batch) := by
    rw [RingGlobalComparison.prior_exact called]
    exact RingChemicalGraphProof.ready geom f
  obtain ⟨ks,got,only⟩ := keys_exact fr ready rev
  refine ⟨matrix ks (fun _ => []),?_,matrix_exact only (fun _ => ?_)⟩
  · simp [at_call geom called fr rev,onReader?,got]
  · exact ⟨fun h => funext h,fun h _ => congrFun h _⟩

/-- An ordinary stage winner precludes a hand-preserving exchange. For an
ordinary tie the finite exchange test distinguishes the two possibilities. -/
theorem classify_iff {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {root : i.certified.Atom} {batch : Nat} {f : Site i}
    (called : RingGlobalComparison.Called i root batch f) (fr : Frame i f) {rev : Bool} {t : Table}
    (hit : table? i root batch f rev = some t) (a b : Slot) (c : Classification) :
    classify fr (reader i root batch) none a b t[a.val][b.val] = c ↔
      t[a.val][b.val] = c.verdict ∧
        (HasExchange fr (RingGlobalComparison.prior i root batch) none a b ↔ c.exchanged = true) := by
  obtain ⟨u,hu,lawful⟩ := exact geom called fr rev
  obtain rfl := Option.some.inj (hu.symm.trans hit)
  rw [reader_eq geom called]
  apply RingResidualPairDecision.classify_iff fr _ lawful
  rw [RingGlobalComparison.prior_exact called]
  exact RingChemicalGraphProof.ready geom f

end TetraStereo.Engine.RingOrdinaryPairVerdict
assert_kernel_only TetraStereo.Engine.RingOrdinaryPairVerdict.exact
assert_kernel_only TetraStereo.Engine.RingOrdinaryPairVerdict.classify_iff
