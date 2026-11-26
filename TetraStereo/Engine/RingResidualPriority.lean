import TetraStereo.Engine.RingAtomicNeighborReport

/-! Independent graph decisions with an arbitrary residual local rule. Only
unresolved sites impose a residual obligation, at their native frozen readers. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingResidualPriority
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Cell View Rule evaluate frozen)
open RingGroupedReport (origin Report)
open RingAtomicNeighborOrder (Decision classify?)

def nativeRule (i : Input) : Rule i := RingPyramidalPublication.publish i

/-- Direct atomic-number priorities at every real occurrence; completed graph
refusals at their original roots; and native ineligible known absences.
Other auxiliary refusals are deliberately left to the residual rule. -/
def graphCell? (i : Input) (q : Site i) : Option Cell :=
  if ¬ RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) q then some (some none)
  else if q.val.node.provenance = .realAtom then
    match q.val.node.current? with
    | none => none
    | some a => match classify? i.molecule a.val with
      | none => none
      | some (.ranked points) => some (some ((Decision.ranked points).read i.spatial))
      | some .refuse => if q = origin i a then some (some none) else none
  else none

theorem graphCell_sound (i : Input) (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) (cell : Cell) (found : graphCell? i q = some cell) :
    cell = RingChemicalGraphProof.state i q := by
  unfold graphCell? at found
  split at found
  · rename_i inactive
    cases found
    exact ((RingChemicalGraphProof.state_eq i q).trans (RingChemicalGraphProof.skips i q _ inactive)).symm
  · split at found
    · rename_i real
      cases current : q.val.node.current? with
      | none => simp [current] at found
      | some a =>
        rw [current] at found
        dsimp only at found
        cases decision : classify? i.molecule a.val with
        | none => simp [decision] at found
        | some d =>
          rw [decision] at found
          cases d with
          | ranked points =>
            dsimp only at found
            cases found
            exact (RingAtomicNeighborOrder.ranked_state i ok q a real current points decision).symm
          | refuse =>
            dsimp only at found
            split at found
            · rename_i original
              cases found
              subst q
              have root := RingAtomicNeighborOrder.root_of_decision i ok a .refuse decision
              have same : RingChemicalGraphProof.root i a = RingChemicalGraphProof.state i (origin i a) :=
                RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i) a
              exact (same.symm.trans root).symm
            · contradiction
    · contradiction

/-- A direct decision does not evaluate the fallback local rule. -/
def splice {i : Input} (direct : Site i → Option Cell) (residual : Rule i) : Rule i :=
  fun q read => match direct q with
  | some cell => cell
  | none => residual q read

theorem splice_direct {i : Input} (direct : Site i → Option Cell) (residual : Rule i)
    (q : Site i) (cell : Cell) (found : direct q = some cell) (read : View i) :
    splice direct residual q read = cell := by simp [splice,found]

def ResidualAgreement {i : Input} (direct : Site i → Option Cell) (residual : Rule i) : Prop :=
  ∀ q, direct q = none → residual q (frozen (RingChemicalGraphProof.state i) q) =
    nativeRule i q (frozen (RingChemicalGraphProof.state i) q)

/-- Necessary and sufficient residual obligation. The primitive is constrained
only at unresolved sites, and only on the actual native frozen reader. -/
theorem splice_state_iff {i : Input} (direct : Site i → Option Cell) (residual : Rule i)
    (sound : ∀ q cell, direct q = some cell → cell = RingChemicalGraphProof.state i q) :
    evaluate (splice direct residual) = RingChemicalGraphProof.state i ↔ ResidualAgreement direct residual := by
  constructor
  · intro same q unresolved
    have equation := RingActiveDistanceSchedule.evaluate_eq (splice direct residual) q
    rw [same] at equation
    simp only [splice,unresolved] at equation
    exact equation.symm.trans (RingChemicalGraphProof.state_eq i q)
  · intro agree
    apply Eq.symm
    apply RingActiveDistanceSchedule.unique
    intro q
    cases found : direct q with
    | none =>
      simp only [splice,found]
      exact (RingChemicalGraphProof.state_eq i q).trans (agree q found).symm
    | some cell =>
      simp only [splice,found]
      exact (sound q cell found).symm

def state (i : Input) (residual : Rule i) : View i := evaluate (splice (graphCell? i) residual)

theorem state_iff (i : Input) (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (residual : Rule i) :
    state i residual = RingChemicalGraphProof.state i ↔ ResidualAgreement (graphCell? i) residual :=
  splice_state_iff (graphCell? i) residual (graphCell_sound i ok)

/-- Root reports take a direct result before constructing any recursive store. -/
def root (i : Input) (residual : Rule i) (a : i.certified.Atom) : Cell :=
  match graphCell? i (origin i a) with
  | some cell => cell
  | none => state i residual (origin i a)

theorem root_state (i : Input) (residual : Rule i) (a : i.certified.Atom) :
    root i residual a = state i residual (origin i a) := by
  unfold root
  cases found : graphCell? i (origin i a) with
  | none => rfl
  | some cell =>
    have equation := RingActiveDistanceSchedule.evaluate_eq (splice (graphCell? i) residual) (origin i a)
    simpa only [splice,found] using equation.symm

def report (i : Input) (residual : Rule i) (atoms : List i.certified.Atom) : Option Report :=
  atoms.mapM fun a => (root i residual a).map fun labels => (a.val,labels)

theorem root_eq_native (i : Input) (residual : Rule i)
    (same : state i residual = RingChemicalGraphProof.state i) (a : i.certified.Atom) :
    root i residual a = RingChemicalGraphProof.root i a := by
  rw [root_state,same]
  exact (RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i) a).symm

theorem report_eq_native (i : Input) (residual : Rule i)
    (same : state i residual = RingChemicalGraphProof.state i) (atoms : List i.certified.Atom) :
    report i residual atoms = RingChemicalReport.report? i atoms := by
  unfold report RingChemicalReport.report?
  apply RingFrameTransport.mapM_congr_mem
  intro a _
  rw [root_eq_native i residual same]
  rfl

theorem native_state_admitted (i : Input) (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    state i (nativeRule i) = RingChemicalGraphProof.state i :=
  (state_iff i ok (nativeRule i)).mpr (fun _ _ => rfl)

/-- Guard once at the public typed entry. On admitted inputs direct graph
results bypass native ranking; other inputs retain the exact native behavior. -/
def nativeState (i : Input) : View i :=
  if LocalizedChemicalRing.coordinatesAdmitted i then state i (nativeRule i) else RingChemicalGraphProof.state i

def nativeReport (i : Input) (atoms : List i.certified.Atom) : Option Report :=
  if LocalizedChemicalRing.coordinatesAdmitted i then report i (nativeRule i) atoms else RingChemicalReport.report? i atoms

/-- Unconditional native fallback specialization, including nonadmitted inputs. -/
theorem nativeState_eq (i : Input) : nativeState i = RingChemicalGraphProof.state i := by
  unfold nativeState
  split
  · exact native_state_admitted i (by assumption)
  · rfl

theorem nativeReport_eq (i : Input) (atoms : List i.certified.Atom) :
    nativeReport i atoms = RingChemicalReport.report? i atoms := by
  unfold nativeReport
  split
  · exact report_eq_native i (nativeRule i) (native_state_admitted i (by assumption)) atoms
  · rfl

assert_kernel_only graphCell_sound
assert_kernel_only splice_state_iff
assert_kernel_only state_iff
assert_kernel_only nativeState_eq
assert_kernel_only nativeReport_eq
end TetraStereo.Engine.RingResidualPriority
