import TetraStereo.Engine.RingUniversalLigandOrder

/-! The native comparison oracle, with explicit defaults outside observable facts. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingLigandNativeAnswers
open RingUniversalLigandOrder
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (View)

/-- Bounds are checked independently for both physical row positions. -/
def rowAnswer (row : Option Pyramidal.Row) (a b : Nat) : Bool :=
  match row with
  | none => false
  | some w => if ha : a < w.size then
      if hb : b < w.size then w.less ⟨a,ha⟩ ⟨b,hb⟩ else false
    else false

/-- Only an available native matrix can answer a query. Unavailable matrices,
wrong observation kinds and out-of-range indices receive the harmless default false. -/
def nativeAnswer {i : Input} {q : Site i} (o : Observation i q) : Answers :=
  fun query => match o,query with
  | .tetra (some (some (_,d))), .tetra rev .ordinary a b => d.ordinary rev a b
  | .tetra (some (some (_,d))), .tetra rev (.marked mark) a b =>
      ((d.marked rev mark).map (fun w => w a b)).getD false
  | .pyramidal _ d, .pyramidal rev .ordinary a b => rowAnswer (d.ordinary rev) a b
  | .pyramidal _ d, .pyramidal rev (.marked mark) a b => rowAnswer (d.marked rev mark) a b
  | _,_ => false

theorem rowAnswer_some (w : Pyramidal.Row) (a b : Fin w.size) :
    rowAnswer (some w) a.val b.val = w.less a b := by
  simp [rowAnswer,a.isLt,b.isLt]

theorem nativeAnswer_of_fact {i : Input} {q : Site i} {o : Observation i q}
    {t : Query} {b : Bool} (fact : Fact o t b) : nativeAnswer o t = b := by
  cases fact with
  | tetra => rfl
  | tetraMarked rev mark present a b ne => simp [nativeAnswer,present]
  | pyramidal rev present a b ne => simp [nativeAnswer,present,rowAnswer_some]
  | pyramidalMarked rev mark present a b ne => simp [nativeAnswer,present,rowAnswer_some]

theorem replace_native {i : Input} {q : Site i} (o : Observation i q) :
    replace (nativeAnswer o) o = o :=
  replace_eq o (nativeAnswer o) (fun _ _ h => nativeAnswer_of_fact h)

/-- Executable oracle extracted before replacement, with no requested output premise. -/
def nativeOracle (i : Input) (q : Site i) (r : View i) : Answers :=
  nativeAnswer (observe i q r)

theorem interpret_replace_native (i : Input) (q : Site i) (r : View i) :
    interpret (replace (nativeOracle i q r) (observe i q r)) = interpret (observe i q r) := by
  exact congrArg interpret (replace_native (observe i q r))


/-- Native pairwise answers reproduce all bounded materialized stores and the
complete typed report, without a comparison-agreement hypothesis. -/
theorem native_exact (i : Input) (valid : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    (∀ a k, k ≤ RingActiveDistanceSchedule.height i + 1 →
      rows valid (nativeOracle i) a k = RingSphereStore.rows i a k) ∧
    ∀ atoms, report valid (nativeOracle i) atoms = RingChemicalReport.report? i atoms := by
  exact exact_of_comparisons valid (nativeOracle i)
    (fun _ _ _ _ _ _ fact => nativeAnswer_of_fact fact)

theorem native_rows (i : Input) (valid : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) (k : Nat) (bound : k ≤ RingActiveDistanceSchedule.height i + 1) :
    rows valid (nativeOracle i) a k = RingSphereStore.rows i a k :=
  (native_exact i valid).1 a k bound

theorem native_report (i : Input) (valid : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) :
    report valid (nativeOracle i) atoms = RingChemicalReport.report? i atoms :=
  (native_exact i valid).2 atoms

end TetraStereo.Engine.RingLigandNativeAnswers
assert_kernel_only TetraStereo.Engine.RingLigandNativeAnswers.nativeAnswer_of_fact
assert_kernel_only TetraStereo.Engine.RingLigandNativeAnswers.replace_native
assert_kernel_only TetraStereo.Engine.RingLigandNativeAnswers.native_exact
