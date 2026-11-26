import TetraStereo.Engine.RingAtomicMetricIndependence
import TetraStereo.Engine.RingOriginOrderCheck

/-! A strict Rule 1a comparison survives a complete rebuild of both ligand
trees under the active-focus duplicate metric. When four such words differ,
both tetrahedral publishers give the same letters on arbitrary prior stores. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingAtomicMetricPublication
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActivePairReport (Slot)
open RingNestedActivePair (Frame Reader)
open RingRetainedChemicalPreorder (Direction keyFor orderWord)
open RingRetainedChemicalTrace (Word Key)
open RingSingleCycleComparison (rebuilt)
open RingGeometryCriterion (Signature)
open private word from TetraStereo.Engine.RingOriginPriorityStore
open private constitutional from TetraStereo.Engine.RingSphereQueue
open private orientation_congr from TetraStereo.Engine.RingZeroMassReport
attribute [local instance] lexOrd

def atomic {i : Input} {f : Site i} (d : Direction i f) : Word := (keyFor d).atomic.word

private theorem head_decides (k l : Key) (apart : k.atomic.word ≠ l.atomic.word) :
    compare (orderWord k) (orderWord l) = compare k.atomic.word l.atomic.word := by
  cases h : compare k.atomic.word l.atomic.word with
  | eq => exact (apart (Std.compare_eq_eq_iff_eq.mp h)).elim
  | lt => simp [orderWord,List.compare_cons_cons,h]
  | gt => simp [orderWord,List.compare_cons_cons,h]

/-- All strictly separated pairs keep their full constitutional comparison,
even at an auxiliary and even when every other pair of ligands is tied. -/
theorem directions {i : Input} {f : Site i} (a b : Direction i f)
    (apart : atomic a ≠ atomic b) :
    compare (word a) (word b) = compare (atomic a) (atomic b) ∧
    compare (orderWord (keyFor a)) (orderWord (keyFor b)) = compare (atomic a) (atomic b) := by
  have get (d : Direction i f) : ∃ k, rebuilt i f ⟨d.val,some f⟩ = some k ∧ k.atomic = (keyFor d).atomic := by
    have eqn := RingAtomicMetricIndependence.direction_atomic d
    cases h : rebuilt i f ⟨d.val,some f⟩ with
    | none => simp [h] at eqn
    | some k => exact ⟨k,rfl,by simpa [h] using eqn⟩
  obtain ⟨k,hk,ka⟩ := get a
  obtain ⟨l,hl,lb⟩ := get b
  have ne : k.atomic.word ≠ l.atomic.word := by simpa only [ka,lb,atomic] using apart
  exact ⟨by simp only [word,hk,hl,Option.map_some,Option.getD_some,head_decides k l ne,ka,lb,atomic],
    head_decides _ _ apart⟩

/-- Zero parity is precisely a tie between some two of the four atomic words.
A failed frame likewise supplies no atomic decision. -/
def early? (i : Input) (f : Site i) : Option Signature := do
  let fr ← RingNestedActivePair.frame? i f
  let parity := RingOrientation.orientation fun j => atomic (fr.direction j)
  if parity = 0 then none else some ⟨RingOrientation.baseline fr * parity,0⟩

theorem early_exact {i : Input} {f : Site i} {s : Signature} (hit : early? i f = some s) :
    RingOriginPriorityStore.early? i f = some s ∧ RingZeroMassReport.zeroEarly? i f = some s := by
  rw [RingZeroMassReport.zero_early_exact]
  cases hr : RingNestedActivePair.frame? i f with
  | none => simp [early?,hr] at hit
  | some fr =>
    let v := fun j : Slot => atomic (fr.direction j)
    have nz : RingOrientation.orientation v ≠ 0 := by
      intro zero
      simp [v] at zero
      simp [early?,hr,zero] at hit
    have inj : Function.Injective v := by
      by_contra bad
      exact nz ((RingOrientation.orientation_zero v).mpr bad)
    have ord (j k : Slot) :
        compare (word (fr.direction j)) (word (fr.direction k)) = compare (v j) (v k) ∧
        compare (constitutional fr j) (constitutional fr k) = compare (v j) (v k) := by
      by_cases eqn : j = k
      · subst k; simp
      · exact directions _ _ (inj.ne eqn)
    have x := orientation_congr (fun j => word (fr.direction j)) v (fun j k => (ord j k).1)
    have y := orientation_congr (constitutional fr) v (fun j k => (ord j k).2)
    simp [early?,hr] at hit
    simpa [RingOriginPriorityStore.early?,RingSphereQueue.early?,hr,x,y,v] using And.intro hit hit

theorem publish_exact {i : Input} {f : Site i} (tetra : RingPyramidalPublication.focusP i f = none)
    {s : Signature} (hit : early? i f = some s) (a b : Reader i) :
    RingOriginMetricReport.publish i f a = some s.letters ∧
    RingPyramidalPublication.publish i f b = some s.letters := by
  obtain ⟨x,y⟩ := early_exact hit
  simp [RingOriginMetricReport.publish,RingPyramidalPublication.publish,
    RingFullPathConstitution.fastPublish,tetra,x,y]

private theorem readers {i : Input} {f : Site i} (tetra : RingPyramidalPublication.focusP i f = none)
    {s : Signature} (hit : early? i f = some s) (a b : Reader i) :
    RingOriginMetricReport.publish i f a = RingPyramidalPublication.publish i f b :=
  (publish_exact tetra hit a b).1.trans (publish_exact tetra hit a b).2.symm

/-- At each eligible occurrence the graph test or the atomic comparison can
establish its publication. The choice can vary within the same sphere. -/
def Covered {i : Input} (f : Site i) : Prop :=
  RingOriginOrderDomain.PreservesOrder f ∨ (RingPyramidalPublication.focusP i f = none ∧ (early? i f).isSome)

/-- Finite check on the public inventory. At a failed graph check, try the
atomic comparison only for a tetrahedral publisher. -/
def check (i : Input) (r : i.certified.Atom) : Bool :=
  (RingActiveDistanceSchedule.sites i).all fun f =>
    if RingEligibleGraph.candidate (RingPyramidalPublication.eligible i) r f then
      RingOriginOrderCheck.focus f || ((RingPyramidalPublication.focusP i f).isNone && (early? i f).isSome)
    else true

theorem check_iff (i : Input) (r : i.certified.Atom) :
    check i r = true ↔ ∀ f, RingEligibleGraph.candidate (RingPyramidalPublication.eligible i) r f →
      Covered f := by
  simp only [check,List.all_eq_true]
  constructor
  · intro all f cand
    have h := all f (List.mem_attach ..)
    simpa [cand,Covered,RingOriginOrderCheck.focus_iff] using h
  · intro all f _
    split_ifs with cand
    · simpa [Covered,RingOriginOrderCheck.focus_iff] using all f cand
    · rfl

theorem rows_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {r : i.certified.Atom} (ok : ∀ f, RingEligibleGraph.candidate (RingPyramidalPublication.eligible i) r f →
      Covered f) (batches : Nat) : RingOriginMetricReport.rows i r batches = RingSphereStore.rows i r batches := by
  unfold RingOriginMetricReport.rows RingSphereStore.rows
  induction batches with
  | zero => rfl
  | succ n ih =>
    simp only [RingSphereQueue.stored,ih]
    congr 1
    apply List.map_congr_left
    intro f mem
    have cand := ((RingEligibleGraph.inventory i _ r _ f).mp mem).1
    rcases ok f cand with order | ⟨tetra,strict⟩
    · rw [RingOriginOrderTransport.publish_exact geom f (RingOriginOrderDomain.factors f cand.2.2.1 order)]
    · obtain ⟨s,hit⟩ := Option.isSome_iff_exists.mp strict
      congr 1
      exact readers tetra hit _ _

theorem raw_exact (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (ok : ∀ i atoms, RingRawComparisonLift.RawTrace m g ids i atoms → ∀ r ∈ atoms,
      ∀ f, RingEligibleGraph.candidate (RingPyramidalPublication.eligible i) r f → Covered f) :
    RingOriginMetricReport.fromRaw? m g ids = RingHydrogenReport.fromRaw? m g ids := by
  apply RingRawComparisonLift.eq_native
  intro i atoms trace
  unfold RingOriginMetricReport.report RingChemicalReport.report?
  apply RingFrameTransport.mapM_congr_mem
  intro r mem
  have root : RingOriginMetricReport.root i r = RingChemicalGraphProof.root i r := by
    unfold RingOriginMetricReport.root
    rw [rows_exact trace.admitted (ok i atoms trace r mem),RingOriginRootAll.publish_origin trace.admitted]
    unfold RingSphereStore.rows
    rw [RingSphereQueue.stored_eq]
    rfl
  rw [root]
  rfl

/-- A raw output difference requires both an order reversal or broken tie
between two closure origins and failure of the tetrahedral Rule 1a shortcut
at the same output-changing auxiliary. -/
theorem raw_witness {m : RawMolecule} {g : SpatialConfiguration} {ids : List Nat}
    (diff : RingOriginMetricReport.fromRaw? m g ids ≠ RingHydrogenReport.fromRaw? m g ids) :
    ∃ i atoms, RingRawComparisonLift.RawTrace m g ids i atoms ∧ ∃ r ∈ atoms,
      ∃ before f after, RingOriginCausal.Switch r f before after ∧
        (RingPyramidalPublication.focusP i f = none → early? i f = none) ∧
        ∃ q p d e, RingOriginOrderDomain.Closure f q d ∧ RingOriginOrderDomain.Closure f p e ∧
          compare d e ≠ compare (RingOriginOrderDomain.distance f q d) (RingOriginOrderDomain.distance f p e) := by
  obtain ⟨i,atoms,trace,r,mem,before,f,after,sw,origins⟩ := RingOriginOrderDomain.raw_witness diff
  refine ⟨i,atoms,trace,r,mem,before,f,after,sw,?_,origins⟩
  intro tetra
  cases h : early? i f with
  | none => rfl
  | some s =>
    obtain ⟨_,_,_,_,changed⟩ := sw.localDifference
    exact (changed (readers tetra h _ _)).elim

end TetraStereo.Engine.RingAtomicMetricPublication
assert_kernel_only TetraStereo.Engine.RingAtomicMetricPublication.directions
assert_kernel_only TetraStereo.Engine.RingAtomicMetricPublication.publish_exact
assert_kernel_only TetraStereo.Engine.RingAtomicMetricPublication.rows_exact
assert_kernel_only TetraStereo.Engine.RingAtomicMetricPublication.raw_exact
assert_kernel_only TetraStereo.Engine.RingAtomicMetricPublication.raw_witness
