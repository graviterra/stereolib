import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
namespace TetraStereo.OneCenter.FiniteGraphReachability

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- One breadth-first closure step, retaining already reached vertices. -/
def expand (vertices : Finset V) : Finset V :=
  vertices ∪ Finset.univ.filter fun v => ∃ u ∈ vertices, G.Adj u v

def steps : Nat → Finset V → Finset V
  | 0, vertices => vertices
  | n + 1, vertices => expand G (steps n vertices)

theorem subset_expand (vertices : Finset V) : vertices ⊆ expand G vertices :=
  Finset.subset_union_left

theorem expand_mono {left right : Finset V} (subset : left ⊆ right) :
    expand G left ⊆ expand G right := by
  intro v member
  simp only [expand, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at *
  rcases member with member | ⟨u, member, edge⟩
  · exact Or.inl (subset member)
  · exact Or.inr ⟨u, subset member, edge⟩

theorem steps_mono (n : Nat) {left right : Finset V} (subset : left ⊆ right) :
    steps G n left ⊆ steps G n right := by
  induction n with
  | zero => exact subset
  | succ n ih => exact expand_mono G ih

theorem steps_time_mono (vertices : Finset V) : Monotone (fun n => steps G n vertices) := by
  apply monotone_nat_of_le_succ
  intro n
  exact subset_expand G _

theorem steps_succ (n : Nat) (vertices : Finset V) :
    steps G (n + 1) vertices = steps G n (expand G vertices) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [steps] using congrArg (expand G) ih

theorem steps_reachable (n : Nat) (start : V) (vertices : Finset V)
    (initial : ∀ v ∈ vertices, G.Reachable start v) :
    ∀ v ∈ steps G n vertices, G.Reachable start v := by
  induction n with
  | zero => exact initial
  | succ n ih =>
      intro v member
      simp only [steps, expand, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and] at member
      rcases member with member | ⟨u, member, edge⟩
      · exact ih v member
      · exact (ih u member).trans edge.reachable

theorem walk_endpoint_mem {u v : V} (walk : G.Walk u v) :
    v ∈ steps G walk.length {u} := by
  induction walk with
  | nil => simp [steps]
  | @cons u w v edge tail ih =>
      have start : ({w} : Finset V) ⊆ expand G {u} := by
        intro x member
        have eq : x = w := Finset.mem_singleton.mp member
        subst x
        simp only [expand, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr ⟨u, by simp, edge⟩
      simpa only [SimpleGraph.Walk.length_cons, steps_succ] using
        (steps_mono G tail.length start ih)

/-- At most `card V` rounds suffice, even if the graph has cycles. -/
def vertices (start : V) : Finset V := steps G (Fintype.card V) {start}

theorem mem_vertices_iff (start finish : V) :
    finish ∈ vertices G start ↔ G.Reachable start finish := by
  constructor
  · apply steps_reachable G (Fintype.card V) start {start}
    intro v member
    have eq : v = start := Finset.mem_singleton.mp member
    subst v
    exact SimpleGraph.Reachable.refl start
  · intro reachable
    apply reachable.elim_path
    intro path
    exact steps_time_mono G {start} (Nat.le_of_lt path.property.length_lt)
      (walk_endpoint_mem G path.val)

def reachableDecidable (start finish : V) : Decidable (G.Reachable start finish) :=
  decidable_of_iff (finish ∈ vertices G start) (mem_vertices_iff G start finish)

end TetraStereo.OneCenter.FiniteGraphReachability
