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

namespace TetraStereo.Engine.RingChloroaziridineNitrogen
open OneCenter
open LocalizedChemicalRing (Input)
open RingOxaziridineNitrogen (atomIs)

/-- Neutral 1-chloro-2-methyl- and 1-chloro-2,2-dimethylaziridine.
The two methyl witnesses coincide in the monomethyl case. Carbon hydrogens
may be materialized. The bonded heavy-atom neighborhoods are exact.
Brois, JACS 1968, DOI 10.1021/ja01004a062; Reich, Trapp and Schurig,
PMID 11045506 (1-chloro-2,2-dimethylaziridine). -/
def Pattern {V : Type} (good : V → Element → Bool) (bond : V → V → Nat) (n : V) : Prop :=
  good n .N = true ∧
  ∃ cl, good cl .Cl = true ∧ bond n cl = 1 ∧ (∀ v, 0 < bond cl v → v = n) ∧
  ∃ c, good c .C = true ∧ bond n c = 1 ∧
  ∃ d, good d .C = true ∧ c ≠ d ∧ bond n d = 1 ∧ bond c d = 1 ∧
    (∀ v, 0 < bond n v → v = cl ∨ v = c ∨ v = d) ∧
    (∀ v, 0 < bond d v → v = n ∨ v = c ∨ good v .H = true) ∧
  ∃ x, good x .C = true ∧ x ≠ d ∧ bond c x = 1 ∧
  ∃ y, good y .C = true ∧ y ≠ d ∧ bond c y = 1 ∧
    (∀ v, 0 < bond c v → v = n ∨ v = d ∨ v = x ∨ v = y ∨ good v .H = true) ∧
    (∀ v, 0 < bond x v → v = c ∨ good v .H = true) ∧
    (∀ v, 0 < bond y v → v = c ∨ good v .H = true)

set_option synthInstance.maxSize 4096 in
instance {V : Type} [Fintype V] [DecidableEq V] (good : V → Element → Bool)
    (bond : V → V → Nat) (n : V) : Decidable (Pattern good bond n) := by
  unfold Pattern
  infer_instance

def test {V : Type} [Fintype V] [DecidableEq V] (good : V → Element → Bool)
    (bond : V → V → Nat) (n : V) : Bool := decide (Pattern good bond n)

theorem test_equiv {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (g : V → Element → Bool) (h : W → Element → Bool)
    (b : V → V → Nat) (d : W → W → Nat)
    (records : ∀ v z, h (e v) z = g v z) (edges : ∀ u v, d (e u) (e v) = b u v) (n : V) :
    test h d (e n) = test g b n := by
  apply Bool.decide_congr
  unfold Pattern
  simp only [e.symm.exists_congr_left,e.symm.forall_congr_left,Equiv.symm_symm,records,edges,
    ne_eq,e.injective.eq_iff]

def constrainedRaw (m : RawMolecule) (n : Nat) : Bool :=
  if bound : n < m.atomCount then
    test (fun a z => atomIs m a.val z)
      (fun (a b : Fin m.atomCount) => m.bondOrder a.val b.val) ⟨n,bound⟩
  else false

def constrained (i : Input) (a : i.certified.Atom) : Bool := constrainedRaw i.molecule a.val
end TetraStereo.Engine.RingChloroaziridineNitrogen

namespace TetraStereo.Engine.RingDialkyldiaziridine
open OneCenter
open LocalizedChemicalRing (Input)
open RingOxaziridineNitrogen (atomIs)

/-- Every continuation of an alkyl C–C edge must terminate within the finite
atom supply. A cyclic carbon walk can continue without immediate reversal until
fuel is exhausted; a terminal carbon succeeds with only its incoming edge or H. -/
def CarbonTail {V : Type} (good : V → Element → Bool) (bond : V → V → Nat) :
    Nat → V → V → Prop
  | 0,_,_ => False
  | k+1,p,a => ∀ v, 0 < bond a v → bond a v = 1 ∧
      (v = p ∨ (good v .H = true ∧ ∀ w, 0 < bond v w → w = a) ∨
        (good v .C = true ∧ CarbonTail good bond k a v))

instance tailDec {V : Type} [Fintype V] [DecidableEq V]
    (good : V → Element → Bool) (bond : V → V → Nat) (k : Nat) (p a : V) :
    Decidable (CarbonTail good bond k p a) := by
  induction k generalizing p a with
  | zero => exact isFalse id
  | succ k ih =>
    unfold CarbonTail
    letI (x y : V) := ih x y
    infer_instance

/-- A saturated acyclic hydrocarbon substituent on nitrogen. The immediate
neighbor projection is available separately from certification of its descendants. -/
def Alkyl {V : Type} [Fintype V] (good : V → Element → Bool) (bond : V → V → Nat) (n a : V) : Prop :=
  good a .C = true ∧ bond n a = 1 ∧ ∀ v, 0 < bond a v →
    (bond a v = 1 ∧ (good v .H = true → ∀ w, 0 < bond v w → w = a)) ∧
    (v = n ∨ good v .H = true ∨ (good v .C = true ∧ CarbonTail good bond (Fintype.card V) a v))

private theorem tail_equiv {V W : Type} (e : V ≃ W) (g : V → Element → Bool)
    (h : W → Element → Bool) (b : V → V → Nat) (d : W → W → Nat)
    (records : ∀ v z, h (e v) z = g v z) (edges : ∀ u v, d (e u) (e v) = b u v)
    (k : Nat) (p a : V) : CarbonTail h d k (e p) (e a) ↔ CarbonTail g b k p a := by
  induction k generalizing p a with
  | zero => rfl
  | succ k ih =>
    simp only [CarbonTail,e.symm.forall_congr_left,Equiv.symm_symm,e.injective.eq_iff,records,edges,ih]

/-- An N,N′-dialkyldiaziridine with H or saturated alkyl groups on the common
ring carbon. This is a graph test for candidate N atoms. Experimental inversion and
separation data include DOI 10.1002/chir.22131 and 10.1002/chem.200305494. -/
def Pattern {V : Type} [Fintype V] (good : V → Element → Bool) (bond : V → V → Nat) (n : V) : Prop :=
  good n .N = true ∧ ∃ m, good m .N = true ∧ n ≠ m ∧ bond n m = 1 ∧
    ∃ c, good c .C = true ∧ bond n c = 1 ∧ bond m c = 1 ∧
      (∀ v, 0 < bond c v → bond c v = 1 ∧ (v = n ∨ v = m ∨
        (good v .H = true ∧ ∀ w, 0 < bond v w → w = c) ∨ Alkyl good bond c v)) ∧
    ∃ a, a ≠ c ∧ bond n a = 1 ∧ Alkyl good bond n a ∧
      (∀ v, 0 < bond n v → v = m ∨ v = c ∨ v = a) ∧
    ∃ b, b ≠ c ∧ b ≠ a ∧ bond m b = 1 ∧ Alkyl good bond m b ∧
      (∀ v, 0 < bond m v → v = n ∨ v = c ∨ v = b)

set_option synthInstance.maxSize 4096 in
instance {V : Type} [Fintype V] [DecidableEq V] (good : V → Element → Bool)
    (bond : V → V → Nat) (n : V) : Decidable (Pattern good bond n) := by
  unfold Pattern Alkyl
  infer_instance

def test {V : Type} [Fintype V] [DecidableEq V] (good : V → Element → Bool)
    (bond : V → V → Nat) (n : V) : Bool := decide (Pattern good bond n)

theorem test_equiv {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (g : V → Element → Bool) (h : W → Element → Bool)
    (b : V → V → Nat) (d : W → W → Nat)
    (records : ∀ v z, h (e v) z = g v z) (edges : ∀ u v, d (e u) (e v) = b u v) (n : V) :
    test h d (e n) = test g b n := by
  apply Bool.decide_congr
  unfold Pattern Alkyl
  simp only [e.symm.exists_congr_left,e.symm.forall_congr_left,Equiv.symm_symm,records,edges,
    ne_eq,e.injective.eq_iff,← Fintype.card_congr e,tail_equiv e g h b d records edges]

def constrainedRaw (m : RawMolecule) (n : Nat) : Bool :=
  if bound : n < m.atomCount then
    test (fun a z => atomIs m a.val z)
      (fun (a b : Fin m.atomCount) => m.bondOrder a.val b.val) ⟨n,bound⟩
  else false

def constrained (i : Input) (a : i.certified.Atom) := constrainedRaw i.molecule a.val
end TetraStereo.Engine.RingDialkyldiaziridine

namespace TetraStereo.Engine.RingAlkoxyaziridineNitrogen
open OneCenter
open LocalizedChemicalRing (Input)
open RingOxaziridineNitrogen (atomIs)

/-- A methyl terminus, independent of the number of hydrogens already written. -/
def Methyl {V : Type} (good : V → Element → Bool) (bond : V → V → Nat) (p x : V) : Prop :=
  good x .C = true ∧ bond p x = 1 ∧ ∀ v, 0 < bond x v → v = p ∨ good v .H = true

/-- Oxygen bears methyl, ethyl or isopropyl. The two witnesses bound the
number of terminal methyl groups; they can coincide or be unused. -/
def Alkoxy {V : Type} (good : V → Element → Bool) (bond : V → V → Nat) (n o : V) : Prop :=
  ∃ k, good k .C = true ∧ bond o k = 1 ∧
    (∀ v, 0 < bond o v → v = n ∨ v = k) ∧
    ∃ u v, ∀ w, 0 < bond k w → w = o ∨ good w .H = true ∨
      ((w = u ∨ w = v) ∧ Methyl good bond k w)

/-- The ring skeleton of the separable nitrogen invertomers studied by Ioffe
and Koroleva, DOI 10.1007/BF00471872. The gem-dimethyl and methyl-bearing
carbons have exact heavy-atom neighborhoods. -/
def Pattern {V : Type} (good : V → Element → Bool) (bond : V → V → Nat) (n : V) : Prop :=
  good n .N = true ∧
  ∃ o, good o .O = true ∧ bond n o = 1 ∧
  ∃ c, good c .C = true ∧ bond n c = 1 ∧
  ∃ d, good d .C = true ∧ c ≠ d ∧ bond n d = 1 ∧ bond c d = 1 ∧
    (∀ v, 0 < bond n v → v = o ∨ v = c ∨ v = d) ∧
  ∃ x y, x ≠ y ∧ x ≠ d ∧ y ≠ d ∧ Methyl good bond c x ∧ Methyl good bond c y ∧
    (∀ v, 0 < bond c v → v = n ∨ v = d ∨ v = x ∨ v = y) ∧
  ∃ z, z ≠ c ∧ Methyl good bond d z ∧
    (∀ v, 0 < bond d v → v = n ∨ v = c ∨ v = z ∨ good v .H = true) ∧ Alkoxy good bond n o

instance methylDec {V : Type} [Fintype V] [DecidableEq V] (g : V → Element → Bool)
    (b : V → V → Nat) (p x : V) : Decidable (Methyl g b p x) := by unfold Methyl; infer_instance

instance alkoxyDec {V : Type} [Fintype V] [DecidableEq V] (g : V → Element → Bool)
    (b : V → V → Nat) (n o : V) : Decidable (Alkoxy g b n o) := by unfold Alkoxy; infer_instance

set_option synthInstance.maxSize 8192 in
instance {V : Type} [Fintype V] [DecidableEq V] (g : V → Element → Bool)
    (b : V → V → Nat) (n : V) : Decidable (Pattern g b n) := by unfold Pattern; infer_instance

def test {V : Type} [Fintype V] [DecidableEq V] (g : V → Element → Bool)
    (b : V → V → Nat) (n : V) := decide (Pattern g b n)

theorem test_equiv {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (g : V → Element → Bool) (h : W → Element → Bool)
    (b : V → V → Nat) (d : W → W → Nat)
    (records : ∀ v z, h (e v) z = g v z) (edges : ∀ u v, d (e u) (e v) = b u v) (n : V) :
    test h d (e n) = test g b n := by
  apply Bool.decide_congr
  unfold Pattern Alkoxy Methyl
  simp only [e.symm.exists_congr_left,e.symm.forall_congr_left,Equiv.symm_symm,records,edges,ne_eq,e.injective.eq_iff]

def constrainedRaw (m : RawMolecule) (n : Nat) : Bool :=
  if bound : n < m.atomCount then
    test (fun a z => atomIs m a.val z)
      (fun (a b : Fin m.atomCount) => m.bondOrder a.val b.val) ⟨n,bound⟩
  else false

def constrained (i : Input) (a : i.certified.Atom) := constrainedRaw i.molecule a.val
end TetraStereo.Engine.RingAlkoxyaziridineNitrogen

namespace TetraStereo.Engine.RingPyramidalNitrogen
open OneCenter
open LocalizedChemicalRing (Input)
def constrainedRaw (m : RawMolecule) (n : Nat) : Bool :=
  RingOxaziridineNitrogen.constrainedRaw m n || RingBridgeheadNitrogen.constrainedRaw m n ||
    RingChloroaziridineNitrogen.constrainedRaw m n || RingDialkyldiaziridine.constrainedRaw m n ||
    RingAlkoxyaziridineNitrogen.constrainedRaw m n
def constrained (i : Input) (a : i.certified.Atom) : Bool := constrainedRaw i.molecule a.val
end TetraStereo.Engine.RingPyramidalNitrogen
assert_kernel_only TetraStereo.Engine.RingOxaziridineNitrogen.pattern_equiv
assert_kernel_only TetraStereo.Engine.RingOxaziridineNitrogen.test_equiv
assert_kernel_only TetraStereo.Engine.RingDialkyldiaziridine.test_equiv
assert_kernel_only TetraStereo.Engine.RingAlkoxyaziridineNitrogen.test_equiv
