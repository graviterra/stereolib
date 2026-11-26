import TetraStereo.Engine.RingOccurrenceCoordinateTransport
import TetraStereo.Engine.RingSpatialTransport
import TetraStereo.Engine.RingFullPathEligibility

set_option autoImplicit false

namespace TetraStereo.Engine.RingStereoKeyCoordinates
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingSpatialTransport

abbrev moved (i : Input) (g : SpatialConfiguration) (full : g.positions.length = size i) :=
  atGeometry i g full

abbrev cursor (i : Input) (g : SpatialConfiguration) (full : g.positions.length = size i)
    (q : Arm i) : Arm (moved i g full) := sameMoleculeCursor (by rfl) q
abbrev site (i : Input) (g : SpatialConfiguration) (full : g.positions.length = size i)
    (q : Site i) : Site (moved i g full) := sameMoleculeOccurrenceEquiv (by rfl) _ q

theorem observation_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (q : Arm i) (terminal : Bool) :
    RingRetainedChemicalTrace.observation? (moved i g full) (cursor i g full q) terminal =
      RingRetainedChemicalTrace.observation? i q terminal := by
  rfl

theorem children_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (q : Arm i) :
    (i.certified.executableLocalizedRerootChildren q).map (cursor i g full) =
      (moved i g full).certified.executableLocalizedRerootChildren (cursor i g full q) :=
  sameMolecule_children_map (by rfl) q

theorem budget_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (q : Arm i) :
    (moved i g full).certified.localizedRerootCursorBudget (cursor i g full q) =
      i.certified.localizedRerootCursorBudget q := by
  cases h : q.previous? <;> simp [localizedRerootCursorBudget,cursor,sameMoleculeCursor,
    sameMoleculeFrame,h,moved,atGeometry]

theorem constitution_key_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (q : Arm i) :
    RingRetainedChemicalTrace.key? (moved i g full) (cursor i g full q) =
      RingRetainedChemicalTrace.key? i q := by
  unfold RingRetainedChemicalTrace.key?
  have count : (moved i g full).certified.certified.input.molecule.atomCount =
      i.certified.certified.input.molecule.atomCount := rfl
  simp only [count]
  generalize 2 * (i.certified.certified.input.molecule.atomCount + 1 + 1) + 1 = n
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    change (RingRetainedChemicalTrace.observation? (moved i g full) (cursor i g full q)
      ((moved i g full).certified.executableLocalizedRerootChildren (cursor i g full q)).isEmpty >>= _) =
      (RingRetainedChemicalTrace.observation? i q (i.certified.executableLocalizedRerootChildren q).isEmpty >>= _)
    rw [← children_atGeometry]
    simp only [List.isEmpty_map,observation_atGeometry]
    congr 1
    funext root
    simp only [List.mapM_map,Function.comp_def,ih]
theorem unit_build_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (r : Reader i) (s : Reader (moved i g full))
    (read : ∀ q, s (site i g full q) = r q) (n : Nat) (q : Arm i) :
    RingRetainedUnitPass.build (moved i g full) s n (cursor i g full q) =
      RingRetainedUnitPass.build i r n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [RingRetainedUnitPass.build,constitution_key_atGeometry]
    have qr : s (cursor i g full q).occurrence = r q.occurrence := read q.occurrence
    rw [qr]
    simp only [← children_atGeometry]
    simp only [List.map_eq_nil_iff,List.mapM_map,Function.comp_def,ih]

theorem unit_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (r : Reader i) (s : Reader (moved i g full))
    (read : ∀ q, s (site i g full q) = r q) (q : Arm i) :
    RingRetainedUnitPass.atArm (moved i g full) s (cursor i g full q) =
      RingRetainedUnitPass.atArm i r q := by
  unfold RingRetainedUnitPass.atArm
  rw [budget_atGeometry,unit_build_atGeometry i g full r s read]

theorem refine_build_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (r : Reader i) (s : Reader (moved i g full))
    (read : ∀ q, s (site i g full q) = r q)
    (p : Arm i → Option RingStereoSiblingPass.Branch)
    (p' : Arm (moved i g full) → Option RingStereoSiblingPass.Branch)
    (prior : ∀ q, p' (cursor i g full q) = p q)
    (obs : RingRetainedStereoRefinement.Observation) (rev : Bool) (n : Nat) (q : Arm i) :
    RingRetainedStereoRefinement.build (moved i g full) p' s obs rev n (cursor i g full q) =
      RingRetainedStereoRefinement.build i p r obs rev n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [RingRetainedStereoRefinement.build,prior]
    have qr : s (cursor i g full q).occurrence = r q.occurrence := read q.occurrence
    rw [qr]
    simp only [← children_atGeometry]
    simp only [List.mapM_map,Function.comp_def,ih]

theorem priority_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (r : Reader i) (s : Reader (moved i g full))
    (read : ∀ q, s (site i g full q) = r q) (rev : Bool)
    (os : List RingRetainedStereoRefinement.Observation) (q : Arm i) :
    RingRetainedStereoRefinement.priority (moved i g full) s rev os (cursor i g full q) =
      RingRetainedStereoRefinement.priority i r rev os q := by
  induction os generalizing q with
  | nil => exact unit_atGeometry i g full r s read q
  | cons o os ih =>
    simp only [RingRetainedStereoRefinement.priority,budget_atGeometry]
    exact refine_build_atGeometry i g full r s read _ _ ih o rev _ q
theorem marked_bit_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (atom : Nat) (q : Arm i) :
    RingGroupedMark.bit atom (cursor i g full q) = RingGroupedMark.bit atom q := rfl

theorem marked_build_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (r : Reader i) (s : Reader (moved i g full))
    (read : ∀ q, s (site i g full q) = r q) (atom n : Nat) (q : Arm i) :
    RingGroupedMark.build (moved i g full) s atom
      (RingRetainedChemicalTrace.key? (moved i g full))
      (moved i g full).certified.executableLocalizedRerootChildren n (cursor i g full q) =
    RingGroupedMark.build i r atom (RingRetainedChemicalTrace.key? i)
      i.certified.executableLocalizedRerootChildren n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [RingGroupedMark.build,constitution_key_atGeometry]
    have qr : s (cursor i g full q).occurrence = r q.occurrence := read q.occurrence
    rw [qr]
    simp only [← children_atGeometry,List.map_eq_nil_iff,List.mapM_map,Function.comp_def,ih]
    simp only [RingGroupedMark.join,marked_bit_atGeometry]

theorem marked_arm_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (r : Reader i) (s : Reader (moved i g full))
    (read : ∀ q, s (site i g full q) = r q) (atom : Nat) (q : Arm i) :
    RingGroupedMark.arm? (moved i g full) s atom (cursor i g full q) =
      RingGroupedMark.arm? i r atom q := by
  unfold RingGroupedMark.arm?
  simp only [budget_atGeometry]
  exact marked_build_atGeometry i g full r s read atom _ q

theorem mapM_output {α β γ : Type} (f : α → Option β) (g : β → γ) (xs : List α) :
    xs.mapM (fun x => (f x).map g) = (xs.mapM f).map (List.map g) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.mapM_cons,ih]
    cases f a <;> cases xs.mapM f <;> rfl

theorem order_map {α β κ : Type} [LinearOrder κ] (f : α → β)
    (key : α → κ) (key' : β → κ) (same : ∀ a, key' (f a) = key a) (xs : List α) :
    RingStereoSiblingPass.order key' (xs.map f) =
      (RingStereoSiblingPass.order key xs).map f := by
  symm
  exact List.map_mergeSort (by intro a _ b _; simp only [same])

theorem sphereRun_map {α β κ : Type} [LinearOrder κ] (f : α → β)
    (key : α → κ) (key' : β → κ) (same : ∀ a, key' (f a) = key a)
    (next : α → Option (List α)) (next' : β → Option (List β))
    (step : ∀ a, next' (f a) = (next a).map (List.map f))
    (n : Nat) (row : List α) :
    RingFullPathPairs.sphereRun key' next' n (row.map f) =
      (RingFullPathPairs.sphereRun key next n row).map (List.map f) := by
  induction n generalizing row with
  | zero => cases row <;> rfl
  | succ n ih =>
    cases row with
    | nil => rfl
    | cons a row =>
      simp only [List.map_cons,RingFullPathPairs.sphereRun]
      have blocks : (a :: row).mapM (fun x => next' (f x)) =
          ((a :: row).mapM next).map (List.map (List.map f)) := by
        simp only [step,mapM_output]
      simp only [← List.map_cons, List.mapM_map, Function.comp_def]
      rw [blocks]
      cases hb : (a :: row).mapM next with
      | none => rfl
      | some bs =>
        simp only [Option.map,Option.bind_eq_bind,Option.bind_some]
        rw [← List.map_flatten,order_map f key key' same,ih]
        cases hx : RingFullPathPairs.sphereRun key next n (RingStereoSiblingPass.order key bs.flatten) <;>
          simp [List.map_append]
def visit (i : Input) (g : SpatialConfiguration) (full : g.positions.length = size i)
    (v : RingFullPathPairs.FullVisit i) : RingFullPathPairs.FullVisit (moved i g full) :=
  ⟨cursor i g full v.cursor,v.path⟩

theorem like_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (r : Reader i) (s : Reader (moved i g full))
    (read : ∀ q, s (site i g full q) = r q) (rev : Bool) (seed : RS) (q : Arm i) :
    RingFullPathPairs.likeAt (moved i g full) s rev seed (cursor i g full q) =
      RingFullPathPairs.likeAt i r rev seed q := by
  simp only [RingFullPathPairs.likeAt,RingFullPathPairs.handAt]
  rw [show s (cursor i g full q).occurrence = r q.occurrence from read q.occurrence]

theorem next_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (r : Reader i) (s : Reader (moved i g full))
    (read : ∀ q, s (site i g full q) = r q) (rev : Bool)
    (os : List RingRetainedStereoRefinement.Observation) (seed : RS)
    (v : RingFullPathPairs.FullVisit i) :
    (RingFullPathPairs.stage (moved i g full) s rev os).next?
      (RingFullPathPairs.likeAt (moved i g full) s rev seed) (visit i g full v) =
    ((RingFullPathPairs.stage i r rev os).next? (RingFullPathPairs.likeAt i r rev seed) v).map
      (List.map (visit i g full)) := by
  simp only [RingFullPathPairs.Oracle.next?,RingFullPathPairs.stage,visit]
  simp only [← children_atGeometry,List.mapM_map,Function.comp_def]
  rw [← mapM_output]
  congr 1
  funext c
  simp only [priority_atGeometry i g full r s read,like_atGeometry i g full r s read]
  cases RingRetainedStereoRefinement.priority i r rev os c <;> rfl

theorem stageWords_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (r : Reader i) (s : Reader (moved i g full))
    (read : ∀ q, s (site i g full q) = r q) (rev : Bool)
    (os : List RingRetainedStereoRefinement.Observation) (seed : RS) (q : Arm i) :
    RingFullPathPairs.stageWords (moved i g full) s rev os seed (cursor i g full q) =
      RingFullPathPairs.stageWords i r rev os seed q := by
  unfold RingFullPathPairs.stageWords RingFullPathPairs.Oracle.bits? RingFullPathPairs.Oracle.visits?
  simp only [budget_atGeometry]
  have root : RingFullPathPairs.Oracle.root
      (RingFullPathPairs.likeAt (moved i g full) s rev seed) (cursor i g full q) =
      visit i g full (RingFullPathPairs.Oracle.root (RingFullPathPairs.likeAt i r rev seed) q) := by
    simp only [RingFullPathPairs.Oracle.root,visit,like_atGeometry i g full r s read]
  rw [root]
  have natural := sphereRun_map (visit i g full) RingFullPathPairs.FullVisit.path
    RingFullPathPairs.FullVisit.path (fun _ => rfl)
    ((RingFullPathPairs.stage i r rev os).next? (RingFullPathPairs.likeAt i r rev seed))
    ((RingFullPathPairs.stage (moved i g full) s rev os).next?
      (RingFullPathPairs.likeAt (moved i g full) s rev seed))
    (next_atGeometry i g full r s read rev os seed)
    (i.certified.localizedRerootCursorBudget q + 1)
    [RingFullPathPairs.Oracle.root (RingFullPathPairs.likeAt i r rev seed) q]
  simp only [List.map_cons,List.map_nil] at natural
  rw [natural]
  simp only [Option.map_map,Function.comp_def,List.filterMap_map,visit,
    like_atGeometry i g full r s read]

/-- Executable full-path eligibility keys depend on topology and the transported
frozen reader. Replacing the coordinates introduces no additional key premise. -/
theorem key_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (r : Reader i) (s : Reader (moved i g full))
    (read : ∀ q, s (site i g full q) = r q) (rev : Bool) (q : Arm i) :
    RingFullPathEligibility.key? (moved i g full) s rev (cursor i g full q) =
      RingFullPathEligibility.key? i r rev q := by
  simp only [RingFullPathEligibility.key?,RingFullPathPairs.pairs?,RingFullPathRule5.word?,
    priority_atGeometry i g full r s read,stageWords_atGeometry i g full r s read]

/-- The fixed-reference Rule 5 comparison on any two molecular cursors is
unchanged when the frozen site readings commute with coordinate replacement. -/
theorem rule5_score_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (r : Reader i) (s : Reader (moved i g full))
    (read : ∀ q, s (site i g full q) = r q) (rev : Bool) (a b : Arm i) :
    RingFullPathRule5.score? (moved i g full) s rev (cursor i g full a) (cursor i g full b) =
      RingFullPathRule5.score? i r rev a b := by
  simp only [RingFullPathRule5.score?,RingFullPathRule5.word?,
    stageWords_atGeometry i g full r s read]
/-- Transport an actual frozen site reader by the inverse occurrence equivalence. -/
def readerAtGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (r : Reader i) : Reader (moved i g full) :=
  fun q => r ((sameMoleculeOccurrenceEquiv (by rfl) _).symm q)

@[simp] theorem readerAtGeometry_site (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (r : Reader i) (q : Site i) :
    readerAtGeometry i g full r (site i g full q) = r q := by
  exact congrArg r ((sameMoleculeOccurrenceEquiv (by rfl) _).left_inv q)

theorem key_recoordinate (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (r : Reader i) (rev : Bool) (q : Arm i) :
    RingFullPathEligibility.key? (moved i g full) (readerAtGeometry i g full r) rev
      (cursor i g full q) = RingFullPathEligibility.key? i r rev q :=
  key_atGeometry i g full r _ (readerAtGeometry_site i g full r) rev q

theorem marked_arm_recoordinate (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (r : Reader i) (atom : Nat) (q : Arm i) :
    RingGroupedMark.arm? (moved i g full) (readerAtGeometry i g full r) atom
      (cursor i g full q) = RingGroupedMark.arm? i r atom q :=
  marked_arm_atGeometry i g full r _ (readerAtGeometry_site i g full r) atom q
end TetraStereo.Engine.RingStereoKeyCoordinates

assert_kernel_only TetraStereo.Engine.RingStereoKeyCoordinates.key_atGeometry
assert_kernel_only TetraStereo.Engine.RingStereoKeyCoordinates.marked_arm_atGeometry
assert_kernel_only TetraStereo.Engine.RingStereoKeyCoordinates.rule5_score_atGeometry

assert_kernel_only TetraStereo.Engine.RingStereoKeyCoordinates.key_recoordinate
assert_kernel_only TetraStereo.Engine.RingStereoKeyCoordinates.marked_arm_recoordinate
