import TetraStereo.Engine.LocalizedChemicalRingPublic

/-! Short bridged ring systems in the single-bond graph. Three paths with
disjoint interiors connect nonadjacent bridgeheads. Two cycles sharing one
of those paths have at most seven atoms each. This is a structural test,
independent of element, ligand ranking, coordinates and atom numbering. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingBridgeheadNitrogen
open OneCenter
open LocalizedChemicalRing (Input)

def anyVertex {V : Type} [Fintype V] (p : V → Bool) : Bool :=
  decide (∃ v, p v = true)

private theorem anyVertex_equiv {V W : Type} [Fintype V] [Fintype W]
    (e : V ≃ W) (p : V → Bool) (q : W → Bool) (same : ∀ v, q (e v) = p v) :
    anyVertex q = anyVertex p := by
  unfold anyVertex
  apply Bool.decide_congr
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨v, rfl⟩ := e.surjective w
    exact ⟨v, (same v).symm.trans hw⟩
  · rintro ⟨v, hv⟩
    exact ⟨e v, (same v).trans hv⟩

/-- Extend a simple path by at least one internal atom, then try to close
it at the other bridgehead. The continuation receives the internal atoms. -/
def route {V : Type} [Fintype V] [DecidableEq V] (edge : V → V → Bool)
    (target : V) (blocked : List V) (accept : List V → Bool) :
    Nat → V → List V → Bool
  | 0, _, _ => false
  | fuel + 1, curr, used => anyVertex fun v =>
    edge curr v && decide (v ∉ blocked) && decide (v ∉ used) &&
      ((edge v target && accept (v :: used)) ||
        route edge target blocked accept fuel v (v :: used))

/-- The common path and each of the two other paths have at least one internal
atom. A length-five path is the longest one possible on a qualifying cycle. -/
def test {V : Type} [Fintype V] [DecidableEq V] (edge : V → V → Bool) (a : V) : Bool :=
  anyVertex fun b => decide (a ≠ b) && !edge a b &&
    route edge b [a,b] (fun p =>
      route edge b (p ++ [a,b]) (fun q =>
        decide (p.length + q.length + 2 ≤ 7) &&
        route edge b (p ++ q ++ [a,b]) (fun r => decide (p.length + r.length + 2 ≤ 7)) 4 a [])
        4 a []) 4 a []

private theorem route_equiv {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (e : V ≃ W) (g : V → V → Bool) (h : W → W → Bool) (adj : ∀ a b, h (e a) (e b) = g a b)
    (b : V) (blocked : List V) (p : List V → Bool) (q : List W → Bool)
    (accept : ∀ xs, q (xs.map e) = p xs) (k : Nat) (v : V) (used : List V) :
    route h (e b) (blocked.map e) q k (e v) (used.map e) = route g b blocked p k v used := by
  induction k generalizing v used with
  | zero => rfl
  | succ k ih =>
    simp only [route]
    apply anyVertex_equiv e
    intro x
    have mem (xs : List V) : (e x ∈ xs.map e) ↔ x ∈ xs := by simp
    simp only [adj, mem]
    rw [← List.map_cons, accept, List.map_cons, ← List.map_cons, ih]

theorem test_equiv {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (e : V ≃ W) (g : V → V → Bool) (h : W → W → Bool) (adj : ∀ a b, h (e a) (e b) = g a b)
    (a : V) : test h (e a) = test g a := by
  unfold test
  apply anyVertex_equiv e
  intro b
  have neq : decide (e a ≠ e b) = decide (a ≠ b) := Bool.decide_congr (not_congr e.injective.eq_iff)
  rw [neq, adj]
  congr 1
  refine route_equiv e g h adj b [a,b] _ _ ?_ 4 a []
  intro p
  have block (xs : List V) : (xs ++ [a,b]).map e = xs.map e ++ [e a,e b] := by simp
  rw [← block]
  refine route_equiv e g h adj b (p ++ [a,b]) _ _ ?_ 4 a []
  intro q
  simp only [List.length_map]
  congr 1
  rw [← List.map_append, ← block]
  refine route_equiv e g h adj b (p ++ q ++ [a,b]) _ _ ?_ 4 a []
  intro r
  simp

def constrainedRaw (m : RawMolecule) (n : Nat) : Bool :=
  if ha : n < m.atomCount then
    test (fun (u v : Fin m.atomCount) => decide (0 < m.bondOrder u.val v.val)) ⟨n, ha⟩
  else false

def constrained (i : Input) (a : i.certified.Atom) : Bool :=
  constrainedRaw i.molecule a.val
end TetraStereo.Engine.RingBridgeheadNitrogen
assert_kernel_only TetraStereo.Engine.RingBridgeheadNitrogen.test_equiv
