import TetraStereo.Engine.RingGlobalComparison
import TetraStereo.Engine.RingRootTwinDecision
import TetraStereo.Engine.RingCoordinateReportTransport
import TetraStereo.Engine.RingHydrogenPlacementExact

/-! Reduce coordinate comparison to the frames that can affect the requested roots.
A terminal twin pair gives the same refusal on both coordinate tables even if
their local determinants have opposite signs. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingTwinCoordinateTransport
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingSpatialTransport (size atGeometry reindexSite)
open RingFrameTransport (stateG SiteAgree)
open RingWrittenPHReadings (geometry)
open RingActiveDistanceSchedule (height distance)

variable (i : Input) (x : SpatialConfiguration) (full : x.positions.length = size i)
local notation "J" => atGeometry i x full
local notation "E" => reindexSite i x full

private theorem reindex_direct (q : Site i) (hit : RingRootTwinDecision.direct i q = some (some none)) :
    RingRootTwinDecision.direct J (E q) = some (some none) := by
  unfold RingRootTwinDecision.direct at hit ⊢
  rw [RingSpatialTransport.recognized_center]
  cases hc : i.certified.localizedOccurrenceDescriptorCenter? q with
  | none => simp [hc] at hit
  | some c =>
    rw [hc] at hit
    obtain ⟨p,found,_⟩ := Option.map_eq_some_iff.mp hit
    obtain ⟨center,offU,offV⟩ := RingRootTwinDecision.detected_sound i q.val.root c p found
    let z : RingHydrogenSpelling.TwinPair J := ⟨p.c,p.u,p.v,p.distinct,p.records,p.lu,p.lv⟩
    obtain ⟨_,found'⟩ := Option.isSome_iff_exists.mp
      ((RingRootTwinDecision.detected_iff J (E q).val.root c).mpr ⟨z,center,offU,offV⟩)
    simp [found']

/-- A root-relative condition on raw ligand geometry and graph-only twin detection. -/
def ResidualAgreement (root : i.certified.Atom) : Prop :=
  ∀ q : Site i, q.val.root = root → RingRootTwinDecision.direct i q ≠ some (some none) →
    SiteAgree i (geometry i.spatial) (geometry x) q

private theorem state_on (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (moved : LocalizedChemicalRing.coordinatesAdmitted J = true)
    {P : Site i → Prop} (deeper : ∀ u v, P u → RingActiveDistanceSchedule.Visible u v → P v)
    (agree : ∀ u, P u → RingRootTwinDecision.direct i u ≠ some (some none) →
      SiteAgree i (geometry i.spatial) (geometry x) u) (q : Site i) (on : P q) :
    RingChemicalGraphProof.state i q = RingChemicalGraphProof.state J (E q) := by
  have a (u : Site i) : stateG i (geometry i.spatial) u = RingChemicalGraphProof.state i u := by
    rw [←RingWrittenPHReadings.inputGeometry_eq, RingFrameTransport.stateG_input admitted]
  have b (u : Site i) : stateG i (geometry x) u = RingChemicalGraphProof.state J (E u) := by
    rw [←RingSpatialTransport.stateG_reindex i x full]
    change stateG J (geometry (J).spatial) _ = _
    rw [←RingWrittenPHReadings.inputGeometry_eq, RingFrameTransport.stateG_input moved]
  rw [←a,←b]
  suffices h : ∀ n (u : Site i), P u → height i - distance u = n →
      stateG i (geometry i.spatial) u = stateG i (geometry x) u from h _ q on rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u within depth
    by_cases hit : RingRootTwinDecision.direct i u = some (some none)
    · rw [a,b,RingRootTwinDecision.sound i u admitted _ hit,
        RingRootTwinDecision.sound J (E u) moved _ (reindex_direct i x full u hit)]
    · rw [RingFrameTransport.stateG_eq, RingFrameTransport.stateG_eq (g := geometry x)]
      have same := RingFrameTransport.frozen_congr (s := stateG i (geometry i.spatial))
        (t := stateG i (geometry x)) u (fun v visible =>
          ih _ (by have upper := RingActiveDistanceSchedule.distance_bound v
                   have down := visible.2.1
                   omega) v (deeper u v within visible) rfl)
      rw [same]
      exact RingFrameTransport.publishG_congr (agree u within hit) _

theorem state (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (moved : LocalizedChemicalRing.coordinatesAdmitted J = true)
    {root : i.certified.Atom} (agree : ResidualAgreement i x root) (q : Site i) (on : q.val.root = root) :
    RingChemicalGraphProof.state i q = RingChemicalGraphProof.state J (E q) :=
  state_on i x full admitted moved (fun _ _ within vis => vis.1.trans within) agree q on

/-- Root priority reads need no geometric hypothesis at the original center.
Changing its hand may change its final letter while all its ligand priorities survive. -/
def AuxiliaryAgreement (root : i.certified.Atom) : Prop :=
  ∀ u : Site i, u.val.root = root → u.val.node.current? ≠ some root →
    RingRootTwinDecision.direct i u ≠ some (some none) →
    SiteAgree i (geometry i.spatial) (geometry x) u

private abbrev lastPrior (j : Input) (a : j.certified.Atom) :=
  RingGlobalComparison.prior j a (height j + 1)

theorem prior (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (moved : LocalizedChemicalRing.coordinatesAdmitted J = true) {root : i.certified.Atom}
    (agree : AuxiliaryAgreement i x root) (q : Site i) :
    lastPrior J root (E q) = lastPrior i root q := by
  have called (j : Input) (a : j.certified.Atom) :
      RingGlobalComparison.Called j a (height j + 1) (RingGroupedReport.origin j a) := Or.inr ⟨rfl,rfl⟩
  unfold lastPrior
  rw [RingGlobalComparison.prior_exact (called i root),RingGlobalComparison.prior_exact (called J root),
    ←RingSpatialTransport.reindex_origin i x full,RingSpatialTransport.reindex_frozen]
  unfold RingActiveDistanceSchedule.frozen
  split_ifs with off visible
  · rfl
  · have on : q.val.root = root := of_not_not off
    apply Eq.symm
    exact state_on i x full admitted moved
      (P := fun u => u.val.root = root ∧ u.val.node.current? ≠ some root)
      (fun _ _ h v => ⟨v.1.trans h.1,fun same => v.2.2 (h.1.symm ▸ same)⟩)
      (fun u h => agree u h.1 h.2) q ⟨on,visible.2⟩
  · rfl

/-- Ordinary priority, nominated-atom word, and signed Rule 5 comparison on the
actual last public store across a change of geometry. Includes ties and lookup failures. -/
theorem priorities (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (moved : LocalizedChemicalRing.coordinatesAdmitted J = true) {root : i.certified.Atom}
    (agree : AuxiliaryAgreement i x root) (rev : Bool) (atom : Nat) (a b : RingActivePairs.Arm i) :
    let mapArm := RingStereoKeyCoordinates.cursor i x full
    let before := lastPrior i root
    let after := lastPrior J root
    RingFullPathEligibility.key? J after rev (mapArm a) = RingFullPathEligibility.key? i before rev a ∧
    RingGroupedMark.arm? J after atom (mapArm a) = RingGroupedMark.arm? i before atom a ∧
    RingFullPathRule5.score? J after rev (mapArm a) (mapArm b) = RingFullPathRule5.score? i before rev a b := by
  have reads := prior i x full admitted moved agree
  exact ⟨RingStereoKeyCoordinates.key_atGeometry i x full _ _ reads rev a,
    RingStereoKeyCoordinates.marked_arm_atGeometry i x full _ _ reads atom a,
    RingStereoKeyCoordinates.rule5_score_atGeometry i x full _ _ reads rev a b⟩

open private reindexed_height from TetraStereo.Engine.RingHydrogenSpelling

/-- The actual addressed cell, including an unwritten address, agrees after every sphere. -/
theorem sphere (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (moved : LocalizedChemicalRing.coordinatesAdmitted J = true)
    {root : i.certified.Atom} (agree : ResidualAgreement i x root) (k : Nat)
    (bound : k ≤ height i + 1) (q : Site i) :
    RingHydrogenSpelling.sphereEntry i root k q = RingHydrogenSpelling.sphereEntry J root k (E q) := by
  rw [RingHydrogenSpelling.sphereEntry_exact _ _ _ bound,
    RingHydrogenSpelling.sphereEntry_exact _ _ _ (by rw [reindexed_height]; exact bound),reindexed_height]
  by_cases on : q.val.root = root
  · rw [state i x full admitted moved agree q on]
    rfl
  · have off : ¬ RingEligibleGraph.candidate (RingPyramidalPublication.eligible i) root q :=
      fun h => on h.1
    have far : ¬ RingEligibleGraph.candidate (RingPyramidalPublication.eligible J) root (E q) :=
      fun h => on h.1
    simp [off,far]

/-- For any requested list on a hydrogen-complete graph, raw labels and refusals
are independent of the orientation at every graph-certified terminal-twin frame. -/
theorem raw (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (moved : LocalizedChemicalRing.coordinatesAdmitted J = true)
    (closed : RingHydrogenCompletion.plan i.molecule = []) (atoms : List i.certified.Atom)
    (agree : ∀ a ∈ atoms, ResidualAgreement i x a) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial (atoms.map Fin.val) =
      RingHydrogenReport.fromRaw? i.molecule x (atoms.map Fin.val) := by
  rw [RingWrittenPHReadings.fromRaw_closed_report i closed admitted atoms]
  change _ = RingHydrogenReport.fromRaw? (J).molecule (J).spatial (atoms.map Fin.val)
  refine Eq.trans (b := RingChemicalReport.report? J atoms) ?_
    (RingWrittenPHReadings.fromRaw_closed_report J closed moved atoms).symm
  apply RingFrameTransport.mapM_congr_mem
  intro a ha
  apply congrArg (Option.map fun v => (a.val,v))
  have roots (j : Input) (b : j.certified.Atom) :
      RingChemicalGraphProof.root j b = RingChemicalGraphProof.state j (RingGroupedReport.origin j b) :=
    RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips j) b
  exact (roots i a).trans ((state i x full admitted moved (agree a ha) (RingGroupedReport.origin i a) rfl).trans
    ((congrArg (RingChemicalGraphProof.state J) (RingSpatialTransport.reindex_origin i x full a)).trans
      (roots J a).symm))

end TetraStereo.Engine.RingTwinCoordinateTransport
assert_kernel_only TetraStereo.Engine.RingTwinCoordinateTransport.state
assert_kernel_only TetraStereo.Engine.RingTwinCoordinateTransport.prior
assert_kernel_only TetraStereo.Engine.RingTwinCoordinateTransport.priorities
assert_kernel_only TetraStereo.Engine.RingTwinCoordinateTransport.sphere
assert_kernel_only TetraStereo.Engine.RingTwinCoordinateTransport.raw
