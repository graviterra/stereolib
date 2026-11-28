import Mathlib.Combinatorics.SimpleGraph.Maps
import TetraStereo.KernelOnly

/-! Reflection of a cycle with two antipodal marked vertices, and its action on
binary choices of one of the two incident ring arms at each vertex. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingAntipodalParity

abbrev Vertex (n : Nat) := Fin (2*n)

/-- Consecutive indices are joined, including the edge from the last to zero. -/
def cycle (n : Nat) (_hn : 2 ≤ n) : SimpleGraph (Vertex n) where
  Adj u v := u.val + 1 = v.val ∨ v.val + 1 = u.val ∨
    (u.val = 0 ∧ v.val + 1 = 2*n) ∨ (v.val = 0 ∧ u.val + 1 = 2*n)
  symm := by intro u v; dsimp; omega
  loopless := ⟨fun _ => by omega⟩

/-- Fix index zero and reverse the cyclic indexing. -/
def reflect {n : Nat} (v : Vertex n) : Vertex n :=
  ⟨if v.val = 0 then 0 else 2*n-v.val, by split <;> have := v.isLt <;> omega⟩

@[simp] theorem reflect_reflect {n : Nat} (v : Vertex n) : reflect (reflect v) = v := by
  apply Fin.ext
  have := v.isLt
  simp only [reflect]
  split_ifs <;> omega

theorem reflect_adj {n : Nat} (hn : 2 ≤ n) (u v : Vertex n) :
    (cycle n hn).Adj (reflect u) (reflect v) ↔ (cycle n hn).Adj u v := by
  have hu : u.val < 2*n := u.isLt
  have hv : v.val < 2*n := v.isLt
  dsimp only [cycle,reflect]
  split_ifs <;> constructor <;> rintro (eqn|eqn|⟨h,k⟩|⟨h,k⟩) <;> first | contradiction | omega

def marked (n : Nat) (hn : 2 ≤ n) (opposite : Bool) : Vertex n :=
  ⟨if opposite then n else 0, by split <;> omega⟩

theorem fixed_iff {n : Nat} (hn : 2 ≤ n) (v : Vertex n) :
    reflect v = v ↔ v = marked n hn false ∨ v = marked n hn true := by
  have := v.isLt
  simp only [Fin.ext_iff,reflect,marked,Bool.false_eq_true,if_false,if_true]
  split_ifs <;> omega

/-- The positive cyclic direction has bit true at either marked site. -/
def arm (n : Nat) (hn : 2 ≤ n) (opposite positive : Bool) : Vertex n :=
  ⟨if opposite then (if positive then n+1 else n-1) else (if positive then 1 else 2*n-1),
    by cases opposite <;> cases positive <;> simp <;> omega⟩

theorem arms_distinct {n : Nat} (hn : 2 ≤ n) (s : Bool) :
    arm n hn s false ≠ arm n hn s true := by
  cases s <;> simp [arm,Fin.ext_iff]; omega

theorem adjacent_marked_iff {n : Nat} (hn : 2 ≤ n) (s : Bool) (v : Vertex n) :
    (cycle n hn).Adj (marked n hn s) v ↔ v = arm n hn s false ∨ v = arm n hn s true := by
  cases s <;> simp [cycle,marked,arm,Fin.ext_iff] <;> omega

theorem reflect_arm {n : Nat} (hn : 2 ≤ n) (s b : Bool) :
    reflect (arm n hn s b) = arm n hn s (!b) := by
  cases s <;> cases b <;> apply Fin.ext <;> simp [arm,reflect] <;> (try split_ifs) <;> omega

abbrev Assignment := Bool × Bool

def arms {n : Nat} (hn : 2 ≤ n) (a : Assignment) : Vertex n × Vertex n :=
  (arm n hn false a.1, arm n hn true a.2)

def flip (a : Assignment) : Assignment := (!a.1,!a.2)

theorem reflected_assignment {n : Nat} (hn : 2 ≤ n) (a : Assignment) :
    (reflect (arms hn a).1, reflect (arms hn a).2) = arms hn (flip a) := by
  simp [arms,flip,reflect_arm]

/-- Relative binary orientations with respect to the same cyclic direction. -/
inductive Relative where
  | cis | trans
  deriving Repr, DecidableEq

def relative (a : Assignment) : Relative := if a.1 = a.2 then .cis else .trans

/-- Equality of relative orientations is exactly the orbit relation under
the simultaneous arm swap, including both choices of representative. -/
theorem orbit_iff (a b : Assignment) :
    (b = a ∨ b = flip a) ↔ relative a = relative b := by
  obtain ⟨(_|_),(_|_)⟩ := a <;> obtain ⟨(_|_),(_|_)⟩ := b <;> decide

private theorem arms_injective {n : Nat} (hn : 2 ≤ n) : Function.Injective (arms hn) := by
  have one (s b d : Bool) (h : arm n hn s b = arm n hn s d) : b = d := by
    cases b <;> cases d <;> first | rfl | exact (arms_distinct hn s h).elim | exact (arms_distinct hn s h.symm).elim
  intro a b e
  exact Prod.ext (one false _ _ (congrArg Prod.fst e)) (one true _ _ (congrArg Prod.snd e))

/-- Two actual pairs of incident arms are identical or related by the graph
reflection exactly when their relative orientations agree. -/
theorem graph_orbit_iff {n : Nat} (hn : 2 ≤ n) (a b : Assignment) :
    (arms hn b = arms hn a ∨ arms hn b = (reflect (arms hn a).1,reflect (arms hn a).2)) ↔
      relative a = relative b := by
  rw [reflected_assignment,← orbit_iff,(arms_injective hn).eq_iff,(arms_injective hn).eq_iff]

theorem two_classes (r : Relative) :
    ∃ a : Assignment, relative a = r ∧ a ≠ flip a ∧
      ∀ b, relative b = r ↔ b = a ∨ b = flip a := by
  cases r with
  | cis =>
    exact ⟨(false,false),rfl,by decide,fun b => by
      simpa [eq_comm (a := relative b)] using (orbit_iff (false,false) b).symm⟩
  | trans =>
    exact ⟨(false,true),rfl,by decide,fun b => by
      simpa [eq_comm (a := relative b)] using (orbit_iff (false,true) b).symm⟩

def reflection {n : Nat} (hn : 2 ≤ n) : cycle n hn ≃g cycle n hn where
  toFun := reflect
  invFun := reflect
  left_inv := reflect_reflect
  right_inv := reflect_reflect
  map_rel_iff' := reflect_adj hn _ _

/-- Starting at 0 and 1, each next vertex is the neighbor different from the
previous vertex. The argument also covers the four-cycle. -/
private theorem fixed_edge {n : Nat} (hn : 2 ≤ n) (f : cycle n hn ≃g cycle n hn)
    (zero : f (marked n hn false) = marked n hn false)
    (one : f (arm n hn false true) = arm n hn false true) : ∀ v, f v = v := by
  have all (k : Nat) (hk : k < 2*n) : f ⟨k,hk⟩ = ⟨k,hk⟩ := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      match k with
      | 0 => exact zero
      | 1 => exact one
      | k+2 =>
        let a : Vertex n := ⟨k,by omega⟩
        let b : Vertex n := ⟨k+1,by omega⟩
        let v : Vertex n := ⟨k+2,hk⟩
        have fa : f a = a := ih k (by omega) _
        have fb : f b = b := ih (k+1) (by omega) _
        have adj : (cycle n hn).Adj b (f v) := fb ▸ f.map_adj_iff.mpr (show (cycle n hn).Adj b v from Or.inl rfl)
        have different : f v ≠ a := by
          rw [← fa]
          exact fun eqn => (by have h := congrArg Fin.val (f.injective eqn); dsimp [v,a] at h; omega)
        change f v = v
        apply Fin.ext
        rw [ne_eq,Fin.ext_iff] at different
        dsimp [cycle,b,a,v] at adj different ⊢
        omega
  exact fun v => all v.val v.isLt

/-- Fixing the first marked vertex alone forces the entire automorphism to be
the identity or index reflection. In particular it fixes the antipode. -/
theorem stabilizer {n : Nat} (hn : 2 ≤ n) (f : cycle n hn ≃g cycle n hn)
    (fixed : f (marked n hn false) = marked n hn false) :
    (∀ v, f v = v) ∨ (∀ v, f v = reflect v) := by
  let a := arm n hn false true
  have edge : (cycle n hn).Adj (marked n hn false) (f a) := by
    rw [← fixed]
    exact f.map_adj_iff.mpr ((adjacent_marked_iff hn false a).mpr (Or.inr rfl))
  rcases (adjacent_marked_iff hn false _).mp edge with back | front
  · right
    let g := f.trans (reflection hn)
    have zero : g (marked n hn false) = marked n hn false := by
      change reflect (f _) = _
      rw [fixed]
      exact (fixed_iff hn _).mpr (Or.inl rfl)
    have one : g a = a := by
      change reflect (f a) = a
      rw [back,reflect_arm]
      rfl
    intro v
    have h : reflect (f v) = v := fixed_edge hn g zero one v
    simpa using congrArg reflect h
  · exact Or.inl (fixed_edge hn f fixed front)

/-- Exact orbits for all graph automorphisms fixing both named sites. -/
theorem stabilizer_orbit_iff {n : Nat} (hn : 2 ≤ n) (a b : Assignment) :
    (∃ f : cycle n hn ≃g cycle n hn, (∀ s, f (marked n hn s) = marked n hn s) ∧
      arms hn b = (f (arms hn a).1,f (arms hn a).2)) ↔ relative a = relative b := by
  rw [← graph_orbit_iff hn]
  constructor
  · rintro ⟨f,fixed,e⟩
    rcases stabilizer hn f (fixed false) with same | swapped
    · exact Or.inl (by simpa only [same] using e)
    · exact Or.inr (by simpa only [swapped] using e)
  · rintro (e|e)
    · exact ⟨SimpleGraph.Iso.refl,fun _ => rfl,e⟩
    · refine ⟨reflection hn,?_,e⟩
      intro s
      apply (fixed_iff hn _).mpr
      cases s <;> simp

end TetraStereo.Engine.RingAntipodalParity
assert_kernel_only TetraStereo.Engine.RingAntipodalParity.reflect_adj
assert_kernel_only TetraStereo.Engine.RingAntipodalParity.fixed_iff
assert_kernel_only TetraStereo.Engine.RingAntipodalParity.adjacent_marked_iff
assert_kernel_only TetraStereo.Engine.RingAntipodalParity.reflected_assignment
assert_kernel_only TetraStereo.Engine.RingAntipodalParity.two_classes
assert_kernel_only TetraStereo.Engine.RingAntipodalParity.graph_orbit_iff
assert_kernel_only TetraStereo.Engine.RingAntipodalParity.stabilizer_orbit_iff
