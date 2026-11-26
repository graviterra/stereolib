import TetraStereo.Engine.RingSingleCycleOrigin
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! A root meeting every simple cycle forces every ring duplicate's origin to
be the root occurrence, without bounding the number of cycles. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingFeedbackRoot
open OneCenter CertifiedLocalizedCIPInput SimpleGraph
open LocalizedChemicalRing (Input)
open RingSingleCycleOrigin (originPath)

/-- A single vertex that meets every simple cycle. -/
def FeedbackRoot {V : Type*} (G : SimpleGraph V) (r : V) : Prop :=
  ∀ ⦃c : V⦄ (cycle : G.Walk c c), cycle.IsCycle → r ∈ cycle.support

/-- Deleting a feedback root leaves a forest. This sufficient condition needs
neither connectedness nor a bound on the number of cycles. -/
theorem of_induce_acyclic {V : Type*} {G : SimpleGraph V} {r : V}
    (forest : (G.induce {x | x ≠ r}).IsAcyclic) : FeedbackRoot G r := by
  intro c cycle hc
  by_contra absent
  have avoids : ∀ x ∈ cycle.support, x ∈ {x | x ≠ r} := by
    intro x hx eqn
    exact absent (eqn ▸ hx)
  let lifted := cycle.induce {x | x ≠ r} avoids
  apply forest lifted
  apply (SimpleGraph.Walk.map_isCycle_iff_of_injective
    (f := (SimpleGraph.Embedding.induce {x | x ≠ r}).toHom)
    Subtype.val_injective).mp
  change ((cycle.induce {x | x ≠ r} avoids).map
    (SimpleGraph.Embedding.induce {x | x ≠ r}).toHom).IsCycle
  rw [SimpleGraph.Walk.map_induce]
  exact hc

/-- The cycle condition is equivalent to the standard deleted-vertex forest criterion. -/
theorem induce_acyclic {V : Type*} {G : SimpleGraph V} {r : V}
    (feedback : FeedbackRoot G r) : (G.induce {x | x ≠ r}).IsAcyclic := by
  intro c cycle hc
  have hit := feedback (cycle.map (SimpleGraph.Embedding.induce {x | x ≠ r}).toHom)
    (hc.map Subtype.val_injective)
  simp only [SimpleGraph.Walk.support_map, List.mem_map] at hit
  obtain ⟨x, _, eqn⟩ := hit
  exact x.property eqn

theorem feedbackRoot_iff_induce_acyclic {V : Type*} {G : SimpleGraph V} {r : V} :
    FeedbackRoot G r ↔ (G.induce {x | x ≠ r}).IsAcyclic :=
  ⟨induce_acyclic, of_induce_acyclic⟩

/-- Every reachable cycle admits a simple access walk meeting it only at
its endpoint. No finiteness assumption on the graph is required. -/
theorem exists_cycle_access {V : Type*} {G : SimpleGraph V} {r c : V}
    (reachable : G.Reachable r c) (cycle : G.Walk c c) :
    ∃ a, ∃ p : G.Walk r a, p.IsPath ∧ a ∈ cycle.support ∧
      ∀ x ∈ p.support, x ∈ cycle.support → x = a := by
  classical
  obtain ⟨q, hq⟩ := reachable.exists_isPath
  obtain ⟨a, ha, hqa, meet⟩ := q.exists_mem_support_forall_mem_support_imp_eq
    cycle.support.toFinset (by
      exact ⟨c, by simp [cycle.start_mem_support, q.end_mem_support]⟩)
  refine ⟨a, q.takeUntil a hqa, hq.takeUntil hqa, by simpa using ha, ?_⟩
  intro x hx hc
  exact meet x (by simpa using hc) hx

/-- If every simple cycle access has the support of a fixed walk ending at
`a`, then `a` meets every cycle. The reference walk can in particular be any
one of those accesses. -/
theorem feedbackRoot_of_access_support {V : Type*} {G : SimpleGraph V} {r a : V}
    (connected : G.Preconnected) (reference : G.Walk r a)
    (same : ∀ {c b : V} (cycle : G.Walk c c), cycle.IsCycle →
      ∀ p : G.Walk r b, p.IsPath → b ∈ cycle.support →
        (∀ x ∈ p.support, x ∈ cycle.support → x = b) →
        p.support = reference.support) : FeedbackRoot G a := by
  intro c cycle hc
  obtain ⟨b,p,hp,hb,meet⟩ := exists_cycle_access (connected r c) cycle
  have support := same cycle hc p hp hb meet
  have endpoint : b = a := by
    have eqn := congrArg List.getLast? support
    simpa only [List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil _),
      Walk.getLast_support, Option.some.injEq] using eqn
  exact endpoint ▸ hb

/-- The endpoint of the common access history is a feedback vertex, so its
removal leaves a forest even when there are arbitrarily many cycles. -/
theorem forest_of_access_support {V : Type*} {G : SimpleGraph V} {r a : V}
    (connected : G.Preconnected) (reference : G.Walk r a)
    (same : ∀ {c b : V} (cycle : G.Walk c c), cycle.IsCycle →
      ∀ p : G.Walk r b, p.IsPath → b ∈ cycle.support →
        (∀ x ∈ p.support, x ∈ cycle.support → x = b) →
        p.support = reference.support) : (G.induce {x | x ≠ a}).IsAcyclic :=
  induce_acyclic (feedbackRoot_of_access_support connected reference same)

/-- With at least one cycle, the common access endpoint also has exactly
one simple path from the original root. Together these are necessary graph
conditions for a common complete origin history. -/
theorem forest_and_path_unique_of_access_support {V : Type*} {G : SimpleGraph V}
    {r a c : V} (connected : G.Preconnected) (reference : G.Walk r a)
    (same : ∀ {c b : V} (cycle : G.Walk c c), cycle.IsCycle →
      ∀ p : G.Walk r b, p.IsPath → b ∈ cycle.support →
        (∀ x ∈ p.support, x ∈ cycle.support → x = b) →
        p.support = reference.support)
    (cycle : G.Walk c c) (hc : cycle.IsCycle) :
    (G.induce {x | x ≠ a}).IsAcyclic ∧
      ∀ q : G.Walk r a, q.IsPath → q = reference := by
  classical
  have feedback := feedbackRoot_of_access_support connected reference same
  refine ⟨induce_acyclic feedback, ?_⟩
  intro q hq
  obtain ⟨b, hb, hqb, meet⟩ := q.exists_mem_support_forall_mem_support_imp_eq
    cycle.support.toFinset (by
      exact ⟨a, by simp [feedback cycle hc, q.end_mem_support]⟩)
  have hb' : b ∈ cycle.support := by simpa using hb
  have meet' : ∀ x ∈ (q.takeUntil b hqb).support, x ∈ cycle.support → x = b := by
    intro x hx there
    exact meet x (by simpa using there) hx
  have support := same cycle hc (q.takeUntil b hqb) (hq.takeUntil hqb) hb' meet'
  have endpoint : b = a := by
    have eqn := congrArg List.getLast? support
    simpa only [List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil _),
      Walk.getLast_support, Option.some.injEq] using eqn
  subst b
  have dropNil : q.dropUntil a hqb = .nil :=
    (Walk.isPath_iff_eq_nil _).mp (hq.dropUntil hqb)
  have whole : q.takeUntil a hqb = q := by
    have split := q.take_spec hqb
    simpa [dropNil] using split
  apply Walk.support_injective
  rwa [whole] at support

/-- Every legitimate ring duplicate originates at depth zero and carries the
singleton root history. -/
theorem legitimate_origin {i : Input} {r : i.certified.Atom}
    (feedback : FeedbackRoot i.certified.moleculeGraph.underlyingSimpleGraph r)
    {node addr} (leg : LegitimateOccurrence i.certified r node addr) {d : Nat}
    (duplicate : node.provenance = .ringDuplicate d) :
    originPath node d = [r] ∧ d = 0 := by
  obtain ⟨w,p,cycle,hp,hc,meet,path,depth⟩ :=
    RingSingleCycleOrigin.closure_access leg duplicate
  have eqn : r = w := meet r p.start_mem_support (feedback cycle hc)
  subst w
  have nil : p = .nil := (SimpleGraph.Walk.isPath_iff_eq_nil p).mp hp
  exact ⟨by simpa [nil] using path, by simpa [nil] using depth⟩

/-- Carrier-level form, valid at every retained fuel. -/
theorem carrier_origin {i : Input} {r : i.certified.Atom}
    (feedback : FeedbackRoot i.certified.moleculeGraph.underlyingSimpleGraph r)
    {fuel : Nat} (x : i.certified.LocalizedCIPOccurrence fuel)
    (root : x.val.root = r) {d : Nat}
    (duplicate : x.val.node.provenance = .ringDuplicate d) :
    originPath x.val.node d = [r] ∧ d = 0 := by
  have leg := i.certified.carrierOccurrence_legitimate i.single x
  rw [root] at leg
  exact legitimate_origin feedback leg duplicate

end TetraStereo.Engine.RingFeedbackRoot
assert_kernel_only TetraStereo.Engine.RingFeedbackRoot.forest_and_path_unique_of_access_support
assert_kernel_only TetraStereo.Engine.RingFeedbackRoot.of_induce_acyclic
assert_kernel_only TetraStereo.Engine.RingFeedbackRoot.legitimate_origin
assert_kernel_only TetraStereo.Engine.RingFeedbackRoot.carrier_origin
