import TetraStereo.Engine.RingCycleRealization
import TetraStereo.Engine.RingForestLigandOrder
import TetraStereo.Engine.RingOriginSeparation

/-! Exact graph conditions for a common complete molecular duplicate origin. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingCommonOriginCriterion
open OneCenter CertifiedLocalizedCIPInput SimpleGraph
open LocalizedChemicalRing (Input)
open RingSingleCycleComparison (CommonOrigin)
open RingActivePairs (Arm)

/-- A feedback vertex reached by exactly one simple path from the molecular root. -/
def GraphCriterion (i : Input) (r : i.certified.Atom) : Prop :=
  ∃ a, ∃ p : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r a,
    p.IsPath ∧ (i.certified.moleculeGraph.underlyingSimpleGraph.induce {x | x ≠ a}).IsAcyclic ∧
      ∀ q : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r a, q.IsPath → q = p

private theorem realize_access {i : Input} {r c a : i.certified.Atom}
    (cycle : i.certified.moleculeGraph.underlyingSimpleGraph.Walk c c) (hc : cycle.IsCycle)
    (p : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r a) (hp : p.IsPath)
    (ha : a ∈ cycle.support)
    (meet : ∀ x ∈ p.support, x ∈ cycle.support → x = a) :
    ∃ q : RingActivePairs.Site i, q.val.root = r ∧
      q.val.node.provenance = .ringDuplicate p.length ∧
      RingSingleCycleOrigin.originPath q.val.node p.length = p.support := by
  apply RingCycleRealization.realize_cycle p (cycle.rotate ha) hp (hc.rotate ha)
  intro x hx there
  exact meet x hx ((cycle.mem_support_rotate_iff ha).mp there)

/-- Actual retained duplicates detect every simple cycle access, so equality
of their entire origin histories forces the graph criterion. -/
theorem necessary {i : Input} {r c : i.certified.Atom}
    (connected : i.certified.moleculeGraph.underlyingSimpleGraph.Connected)
    (cycle : i.certified.moleculeGraph.underlyingSimpleGraph.Walk c c) (hc : cycle.IsCycle)
    (common : CommonOrigin i r) : GraphCriterion i r := by
  obtain ⟨a,p,hp,ha,meet⟩ := RingFeedbackRoot.exists_cycle_access (connected r c) cycle
  obtain ⟨reference,rr,rd,rh⟩ := realize_access cycle hc p hp ha meet
  have same : ∀ {c b : i.certified.Atom}
      (cyc : i.certified.moleculeGraph.underlyingSimpleGraph.Walk c c), cyc.IsCycle →
      ∀ q : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r b, q.IsPath →
        b ∈ cyc.support → (∀ x ∈ q.support, x ∈ cyc.support → x = b) →
        q.support = p.support := by
    intro c b cyc hcyc q hq hb intersection
    obtain ⟨other,orr,od,oh⟩ := realize_access cyc hcyc q hq hb intersection
    have histories := (common (⟨other,none⟩ : Arm i) (⟨reference,none⟩ : Arm i)
      q.length p.length orr rr od rd).1
    exact oh.symm.trans (histories.trans rh)
  obtain ⟨forest,unique⟩ := RingFeedbackRoot.forest_and_path_unique_of_access_support
    connected.preconnected p same cycle hc
  exact ⟨a,p,hp,forest,unique⟩

/-- A unique simple access to a feedback vertex fixes the complete origin of
every actual ring duplicate. -/
theorem sufficient {i : Input} {r : i.certified.Atom}
    (criterion : GraphCriterion i r) : CommonOrigin i r := by
  obtain ⟨a,p,hp,forest,unique⟩ := criterion
  exact RingForestLigandOrder.common_of_unique_path p unique
    (RingFeedbackRoot.of_induce_acyclic forest)

/-- For a connected molecular graph containing a cycle, common actual duplicate
origin is equivalent to a unique simple access to a feedback vertex. -/
theorem commonOrigin_iff {i : Input} {r c : i.certified.Atom}
    (connected : i.certified.moleculeGraph.underlyingSimpleGraph.Connected)
    (cycle : i.certified.moleculeGraph.underlyingSimpleGraph.Walk c c) (hc : cycle.IsCycle) :
    CommonOrigin i r ↔ GraphCriterion i r :=
  ⟨necessary connected cycle hc, sufficient⟩

/-- Every pair of actual ring duplicates preserves its original depth
comparison after moving the focus to any real occurrence under the same root. -/
def AllRealFocusComparisons (i : Input) (r : i.certified.Atom) : Prop :=
  ∀ (x y : RingActivePairs.Site i) (u v : Nat),
    x.val.root = r → y.val.root = r →
    x.val.node.provenance = .ringDuplicate u → y.val.node.provenance = .ringDuplicate v →
    ∀ f : RingActivePairs.Site i, f.val.root = r → f.val.node.provenance = .realAtom →
      compare u v = compare
        (RingSingleCycleOrigin.pathDistance f.val.node.history.reverse
          (RingSingleCycleOrigin.originPath x.val.node u))
        (RingSingleCycleOrigin.pathDistance f.val.node.history.reverse
          (RingSingleCycleOrigin.originPath y.val.node v))

/-- The graph criterion is sharp for preserving depth comparisons at every
real focus, over all actual duplicate leaves. -/
theorem all_foci_iff {i : Input} {r c : i.certified.Atom}
    (connected : i.certified.moleculeGraph.underlyingSimpleGraph.Connected)
    (cycle : i.certified.moleculeGraph.underlyingSimpleGraph.Walk c c) (hc : cycle.IsCycle) :
    GraphCriterion i r ↔ AllRealFocusComparisons i r := by
  constructor
  · intro criterion x y u v xr yr xd yd
    have same := (sufficient criterion (⟨x,none⟩ : Arm i) (⟨y,none⟩ : Arm i)
      u v xr yr xd yd).1
    intro f fr real
    exact (RingOriginSeparation.all_real_foci_iff x y (xr.trans yr.symm) xd yd).mpr
      same f (fr.trans xr.symm) real
  · intro all
    apply (commonOrigin_iff connected cycle hc).mp
    intro x y u v xr yr xd yd
    have same := (RingOriginSeparation.all_real_foci_iff x.occurrence y.occurrence
      (xr.trans yr.symm) xd yd).mp (by
        intro f fr real
        exact all x.occurrence y.occurrence u v xr yr xd yd f (fr.trans xr) real)
    obtain ⟨_,_,_,_,lx⟩ := RingOriginSeparation.origin_real x.occurrence xd
    obtain ⟨_,_,_,_,ly⟩ := RingOriginSeparation.origin_real y.occurrence yd
    refine ⟨same, ?_⟩
    rw [same] at lx
    omega

private theorem feedback_of_common_on_cycle {i : Input} {x c : i.certified.Atom}
    (connected : i.certified.moleculeGraph.underlyingSimpleGraph.Connected)
    (cycle : i.certified.moleculeGraph.underlyingSimpleGraph.Walk c c) (hc : cycle.IsCycle)
    (hx : x ∈ cycle.support) (common : CommonOrigin i x) :
    RingFeedbackRoot.FeedbackRoot i.certified.moleculeGraph.underlyingSimpleGraph x := by
  let nil : i.certified.moleculeGraph.underlyingSimpleGraph.Walk x x := .nil
  obtain ⟨reference,rr,rd,rh⟩ := realize_access cycle hc nil Walk.IsPath.nil hx (by
    intro z hz _
    simpa [nil] using hz)
  apply RingFeedbackRoot.feedbackRoot_of_access_support connected.preconnected nil
  intro c b cyc hcyc q hq hb intersection
  obtain ⟨other,orr,od,oh⟩ := realize_access cyc hcyc q hq hb intersection
  have histories := (common (⟨other,none⟩ : Arm i) (⟨reference,none⟩ : Arm i)
    q.length nil.length orr rr od rd).1
  exact oh.symm.trans (histories.trans rh)

/-- A common origin at every molecular root is exactly uniqueness of simple
cycle support. This distinguishes the all-root property from the more general
fixed-root feedback-vertex criterion. -/
theorem all_roots_iff {i : Input} {c : i.certified.Atom}
    (connected : i.certified.moleculeGraph.underlyingSimpleGraph.Connected)
    (cycle : i.certified.moleculeGraph.underlyingSimpleGraph.Walk c c) (hc : cycle.IsCycle) :
    (∀ r : i.certified.Atom, CommonOrigin i r) ↔ RingCycleEntry.UniqueCycleSupport cycle := by
  constructor
  · intro all b other ho x
    constructor
    · intro hx
      exact feedback_of_common_on_cycle connected other ho hx (all x) cycle hc
    · intro hx
      exact feedback_of_common_on_cycle connected cycle hc hx (all x) other ho
  · intro unique r q p d e qr pr qd pd
    exact RingSingleCycleOrigin.common_origin cycle unique q.occurrence p.occurrence
      (qr.trans pr.symm) qd pd

/-- In a forest there are no ring duplicates, hence common origin holds vacuously. -/
theorem common_of_acyclic {i : Input} (r : i.certified.Atom)
    (forest : i.certified.moleculeGraph.underlyingSimpleGraph.IsAcyclic) : CommonOrigin i r := by
  intro q p d e qr pr qd pd
  obtain ⟨a,access,cycle,ha,hc,rest⟩ := RingSingleCycleOrigin.closure_access
    (i.certified.carrierOccurrence_legitimate i.single q.occurrence) qd
  exact False.elim (forest cycle hc)

end TetraStereo.Engine.RingCommonOriginCriterion
assert_kernel_only TetraStereo.Engine.RingCommonOriginCriterion.necessary
assert_kernel_only TetraStereo.Engine.RingCommonOriginCriterion.common_of_acyclic
assert_kernel_only TetraStereo.Engine.RingCommonOriginCriterion.commonOrigin_iff
assert_kernel_only TetraStereo.Engine.RingCommonOriginCriterion.all_foci_iff
assert_kernel_only TetraStereo.Engine.RingCommonOriginCriterion.all_roots_iff
