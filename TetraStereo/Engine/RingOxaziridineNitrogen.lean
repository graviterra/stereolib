import TetraStereo.Engine.RingBridgeheadNitrogen

/-! A narrow constitutional N-alkyl oxaziridine class. The nitrogen has exactly
the two ring neighbors and one external carbon; oxygen is genuinely divalent.
Both carbon atoms have only single incident bonds. Carbon hydrogens may still
be implicit; no coordinate, descriptor or written parity is consulted. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOxaziridineNitrogen
open OneCenter
open LocalizedChemicalRing (Input)

def atomIs (m : RawMolecule) (n : Nat) (element : Element) : Bool :=
  (m.atoms[n]?).any fun a => a.element == element && a.charge == 0 && !a.aromatic

def Pattern {V : Type} (good : V → Element → Bool) (bond : V → V → Nat) (n : V) : Prop :=
  good n .N = true ∧
  ∃ o, n ≠ o ∧ good o .O = true ∧ bond n o = 1 ∧
  ∃ c, n ≠ c ∧ o ≠ c ∧ good c .C = true ∧ bond n c = 1 ∧ bond o c = 1 ∧
  ∃ k, n ≠ k ∧ o ≠ k ∧ c ≠ k ∧ good k .C = true ∧ bond n k = 1 ∧
    (∀ v, 0 < bond n v ↔ v = o ∨ v = c ∨ v = k) ∧
    (∀ v, 0 < bond o v ↔ v = n ∨ v = c) ∧
    (∀ v, bond c v ≤ 1) ∧ (∀ v, bond k v ≤ 1) ∧
    (∀ v, 0 < bond k v → v = n ∨ good v .C = true ∨ good v .H = true)

set_option synthInstance.maxSize 2048 in
instance {V : Type} [Fintype V] [DecidableEq V] (good : V → Element → Bool)
    (bond : V → V → Nat) (n : V) : Decidable (Pattern good bond n) := by
  unfold Pattern
  infer_instance

def test {V : Type} [Fintype V] [DecidableEq V]
    (good : V → Element → Bool) (bond : V → V → Nat) (n : V) : Bool :=
  decide (Pattern good bond n)

theorem pattern_equiv {V W : Type} (e : V ≃ W)
    (g : V → Element → Bool) (h : W → Element → Bool)
    (b : V → V → Nat) (d : W → W → Nat)
    (records : ∀ v z, h (e v) z = g v z) (edges : ∀ u v, d (e u) (e v) = b u v) (n : V) :
    Pattern h d (e n) ↔ Pattern g b n := by
  unfold Pattern
  simp only [e.symm.exists_congr_left,e.symm.forall_congr_left,Equiv.symm_symm,records,edges,ne_eq,e.injective.eq_iff]

theorem test_equiv {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (e : V ≃ W) (g : V → Element → Bool) (h : W → Element → Bool)
    (b : V → V → Nat) (d : W → W → Nat)
    (records : ∀ v z, h (e v) z = g v z) (edges : ∀ u v, d (e u) (e v) = b u v) (n : V) :
    test h d (e n) = test g b n :=
  Bool.decide_congr (pattern_equiv e g h b d records edges n)

def constrainedRaw (m : RawMolecule) (n : Nat) : Bool :=
  if bound : n < m.atomCount then
    test (fun a z => atomIs m a.val z)
      (fun (a b : Fin m.atomCount) => m.bondOrder a.val b.val) ⟨n,bound⟩
  else false

def constrained (i : Input) (a : i.certified.Atom) : Bool := constrainedRaw i.molecule a.val
end TetraStereo.Engine.RingOxaziridineNitrogen

namespace TetraStereo.Engine.RingPyramidalNitrogen
open OneCenter
open LocalizedChemicalRing (Input)
def constrainedRaw (m : RawMolecule) (n : Nat) : Bool :=
  RingOxaziridineNitrogen.constrainedRaw m n || RingBridgeheadNitrogen.constrainedRaw m n
def constrained (i : Input) (a : i.certified.Atom) : Bool := constrainedRaw i.molecule a.val
end TetraStereo.Engine.RingPyramidalNitrogen
assert_kernel_only TetraStereo.Engine.RingOxaziridineNitrogen.pattern_equiv
assert_kernel_only TetraStereo.Engine.RingOxaziridineNitrogen.test_equiv
