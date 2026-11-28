import TetraStereo.Engine.RingPlanarHydrogenChoices
import TetraStereo.Engine.RingRawComparisonLift
import TetraStereo.Engine.RingSphereStore

/-! Blue Book P-93.3.3.2 and P-93.3.4.1 place a lowest-priority phantom
on the perpendicular to the ligand plane, beyond the trigonal apex. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPerpendicularPhantom
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingHydrogenCompletion
open RingPlanarHydrogenChoices (normal)
open CartesianPoint3 (orientedVolume)
open private scalePoint from TetraStereo.Engine.RingHydrogenFrame

/-- Vary the phantom's distance on the outward normal ray. The signed
volume in the displacement selects the outward side regardless of the
orientation in which the three bonded points are listed. -/
def point (a b c apex : Point) (t : ℚ) : Point :=
  vsub apex (scalePoint (t * orientedVolume a b c apex) (normal a b c))

theorem perpendicular (a b c p : Point) (t : ℚ) :
    vdot (vsub (point a b c p t) p) (vsub b a) = 0 ∧
    vdot (vsub (point a b c p t) p) (vsub c a) = 0 := by
  constructor <;> simp only [point,scalePoint,normal,vsub,vcross,vdot] <;> ring

theorem volume (a b c p : Point) (t : ℚ) :
    orientedVolume a b c (point a b c p t) =
      (1 + t * normSq (normal a b c)) * orientedVolume a b c p := by
  rw [point,RingPlanarHydrogenChoices.volume_offset]
  ring

private theorem norm_nonneg (q : Point) : 0 ≤ normSq q := by
  unfold normSq vdot
  exact add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _)

/-- Every positive step moves a nonflat apex strictly farther from the base. -/
theorem outward (a b c p : Point) {t : ℚ} (positive : 0 < t)
    (noncollinear : normal a b c ≠ zeroVector) (raised : orientedVolume a b c p ≠ 0) :
    |orientedVolume a b c p| < |orientedVolume a b c (point a b c p t)| := by
  have pos := mul_pos positive (RingHydrogenCompletion.normSq_pos noncollinear)
  rw [volume,abs_mul,abs_of_pos (by linarith : 0 < 1 + t * normSq (normal a b c))]
  nlinarith [mul_pos pos (abs_pos.mpr raised)]

/-- Every outward displacement along the base normal of a nonflat pyramid
occurs in this family. The coefficient may have either sign because the
chosen normal changes sign when two bonded ligands are interchanged. -/
theorem covers_ray (a b c p : Point) (s : ℚ) (nonflat : orientedVolume a b c p ≠ 0)
    (out : 0 ≤ s * orientedVolume a b c p) :
    ∃ t : ℚ, 0 ≤ t ∧ point a b c p t = vsub p (scalePoint s (normal a b c)) := by
  let v := orientedVolume a b c p
  refine ⟨s * v / v^2,div_nonneg out (sq_nonneg v),?_⟩
  have parent : s * v / v^2 * v = s := by field_simp [v,nonflat]
  exact congrArg (fun k => vsub p (scalePoint k (normal a b c))) parent

/-- Includes both hands, flat frames, arbitrary priority order of the three
ligands, and arbitrary distances along the ray. -/
theorem hand (a b c p : Point) {t : ℚ} (nonneg : 0 ≤ t) :
    descriptorOfPriorityOrderedPoints? [a,b,c,point a b c p t] =
    descriptorOfPriorityOrderedPoints? [a,b,c,p] := by
  have pos : 0 < 1 + t * normSq (normal a b c) := by nlinarith [mul_nonneg nonneg (norm_nonneg (normal a b c))]
  simp [descriptorOfPriorityOrderedPoints?,volume,descriptorOfOrientedVolume?,mul_neg_iff,pos,not_lt.mpr pos.le,
    mul_pos_iff_of_pos_left pos]

def points? (t : ℚ) : List Point → Option RS
  | [a,b,c,p] => descriptorOfPriorityOrderedPoints? [a,b,c,point a b c p t]
  | _ => none

def read? (t : ℚ) (g : Geometry) (ids : List Nat) : Option RS := do
  points? t (← ids.mapM g)

theorem read_eq {t : ℚ} (nonneg : 0 ≤ t) : read? t = readback? := by
  have same : points? t = descriptorOfPriorityOrderedPoints? := by
    funext ps
    rcases ps with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨p,_ | ⟨e,tail⟩⟩⟩⟩⟩ <;> first | rfl | exact hand a b c p nonneg
  funext g ids
  simp only [read?,readback?,same]

open LocalizedChemicalRing (Input)
open RingActiveDistanceSchedule (View)
open RingPyramidalPublication (Ligand)
open RingRetainedChemicalTrace (Word)

/-- Recompute an ordinary or marked pyramidal trial using the perpendicular
phantom at its actual sorted coordinates, including on the reflected geometry. -/
def trial? {i : Input} (t : ℚ) (r : View i) (a : i.certified.Atom) (rev : Bool)
    (xs : List (Ligand i)) (mark : Option Nat) : Option (Option RS) := do
  let rows ← xs.mapM fun x => do
    let word ← match mark with
      | none => some ([] : Word)
      | some id => (RingGroupedMark.arm? i r id x.arm).map fun b => b.2.word
    return (x.atom,RingFullPathTrialReadings.trialKey x.priority word)
  if !(rows.map Prod.snd).Nodup then return none
  let g := LocalizedChemicalRingPhysicalSense.inputGeometry i.certified
  return read? t (if rev then mirror g else g) ((RingStereoSiblingPass.order Prod.snd rows).map Prod.fst ++ [a.val])

theorem trial_exact {i : Input} {t : ℚ} (nonneg : 0 ≤ t) (r : View i) (a : i.certified.Atom)
    (rev : Bool) (xs : List (Ligand i)) (mark : Option Nat) :
    trial? t r a rev xs mark = RingPyramidalPublication.trial? r a rev xs mark := by
  unfold trial? RingPyramidalPublication.trial?
  rw [read_eq nonneg]
  rfl

open RingActivePairs (Site)
open RingPyramidalPublication (eligible focusP ligands?)
open RingActiveDistanceSchedule (Cell Rule height)

private def hands? (t : ℚ) (i : Input) (q : Site i) (r : View i) (a : i.certified.Atom) (rev : Bool) := do
  let xs ← ligands? i q r rev
  let marks : List (Option Nat) := match xs with
    | [x,y,z] => if x.priority == y.priority && y.priority == z.priority then
        [some x.atom,some y.atom,some z.atom] else [none]
    | _ => []
  marks.mapM (trial? t r a rev xs)

/-- The pyramid contributes its hand to the ordinary sphere schedule using
the physical phantom on both geometries. -/
def publish (t : ℚ) (i : Input) (q : Site i) (r : View i) : Cell :=
  match focusP i q with
  | none => RingFullPathConstitution.fastPublish i q r
  | some a => some (do
      guard ((RingRetainedAuxiliary.frame i.certified q).length = 3)
      let hs ← hands? t i q r a false
      let ms ← hands? t i q r a true
      RingFullPathPublication.crossed hs ms)

theorem publish_eq {t : ℚ} (nonneg : 0 ≤ t) (i : Input) :
    publish t i = RingPyramidalPublication.publish i := by
  have tr : @trial? i t = @RingPyramidalPublication.trial? i := by
    funext r a rev xs m
    exact trial_exact nonneg r a rev xs m
  have hs : hands? t i = RingPyramidalPublication.hands? i := by
    funext q r a rev
    unfold hands? RingPyramidalPublication.hands?
    rw [tr]
    rfl
  funext q r
  cases focus : focusP i q <;> simp only [publish,RingPyramidalPublication.publish,focus,RingPyramidalPublication.pLabels,hs]

theorem rows_exact {t : ℚ} (nonneg : 0 ≤ t) (i : Input) (a : i.certified.Atom) (k : Nat) :
    RingSphereQueue.stored (publish t i) a (RingEligibleGraph.queue i (eligible i) a) (height i) k =
    RingSphereStore.rows i a k := by rw [publish_eq nonneg]

def report (t : ℚ) : RingRawComparisonLift.TypedEvaluation := fun i atoms =>
  atoms.mapM fun a => (RingEligibleGraph.root i (eligible i) (publish t i) a).map fun v => (a.val,v)

/-- For any raw graph, coordinates and atom list, using the source normal
construction throughout yields the same complete optional response. -/
theorem raw_exact {t : ℚ} (nonneg : 0 ≤ t) :
    RingRawComparisonLift.fromRaw (report t) = RingHydrogenReport.fromRaw? := by
  have same : report t = RingChemicalReport.report? := by
    funext i atoms
    unfold report
    rw [publish_eq nonneg]
    rfl
  rw [same,RingRawComparisonLift.native]

end TetraStereo.Engine.RingPerpendicularPhantom
assert_kernel_only TetraStereo.Engine.RingPerpendicularPhantom.perpendicular
assert_kernel_only TetraStereo.Engine.RingPerpendicularPhantom.covers_ray
assert_kernel_only TetraStereo.Engine.RingPerpendicularPhantom.outward
assert_kernel_only TetraStereo.Engine.RingPerpendicularPhantom.trial_exact
assert_kernel_only TetraStereo.Engine.RingPerpendicularPhantom.rows_exact
assert_kernel_only TetraStereo.Engine.RingPerpendicularPhantom.raw_exact
