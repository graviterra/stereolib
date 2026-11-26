import TetraStereo.Engine.RingOxaziridineRootOrder
import TetraStereo.Engine.RingOxaziridinePublication
import TetraStereo.Engine.RingPyramidalTwoShell

/-! Provenance-sensitive two-shell ordering at oxaziridine occurrences.
A ring closure represents its atom but has no continuing second shell. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOxaziridineAuxOrder
open OneCenter
open LocalizedChemicalRing (Input)
open RingAtomicNeighborOrder (atomicNumber neighbors)
open RingSecondShellDecision (shell signature)
open RingRetainedChemicalPreorder (Site Direction keyFor orderWord)
open RingAllLigandTwoShell (siteAtom physical)
attribute [local instance] lexOrd

/-- The physical prefix retains a second shell exactly at a real endpoint. -/
def projected (m : RawMolecule) (n a : Nat) (real : Bool) : List (List Nat) :=
  [[atomicNumber m a], if real then shell m n a else []]

private theorem nil_lt {xs : List Nat} (ne : xs ≠ []) : ([] : List Nat) < xs := by
  cases xs with
  | nil => contradiction
  | cons => exact List.Lex.nil

/-- Raw C>K signatures imply a nonempty ring-carbon shell even when the
external carbon has no explicit neighbors other than nitrogen. -/
theorem shell_order {m : RawMolecule} {n c k : Nat}
    (zc : atomicNumber m c = 6) (zk : atomicNumber m k = 6)
    (raw : signature m n k < signature m n c) : shell m n k < shell m n c := by
  simpa [signature,zc,zk,List.cons_lt_cons_iff] using raw

/-- Exhaustive projected-prefix classification. A real ring-carbon endpoint
always wins; when it terminates, a continuing nonempty alkyl shell wins.
The remaining case is exactly a projected tie. -/
theorem projected_order {m : RawMolecule} {n o c k : Nat}
    (zo : atomicNumber m o = 8) (zc : atomicNumber m c = 6) (zk : atomicNumber m k = 6)
    (raw : signature m n k < signature m n c) (ro rc rk : Bool) :
    projected m n c rc < projected m n o ro ∧
    projected m n k rk < projected m n o ro ∧
    (rc = true → projected m n k rk < projected m n c rc) ∧
    (rc = false → rk = true → shell m n k ≠ [] →
      projected m n c rc < projected m n k rk) ∧
    (projected m n c rc = projected m n k rk ↔
      rc = false ∧ (rk = false ∨ shell m n k = [])) := by
  have skc := shell_order zc zk raw
  have cn : shell m n c ≠ [] := by
    intro h
    rw [h] at skc
    exact List.not_lt_nil _ skc
  refine ⟨List.Lex.rel (List.Lex.rel (by simp [zo,zc])),
    List.Lex.rel (List.Lex.rel (by simp [zo,zk])),?_,?_,?_⟩
  · intro real
    cases rk <;> simp only [projected,real,Bool.false_eq_true,ite_false,ite_true,zc,zk]
    · exact List.Lex.cons (List.Lex.rel (nil_lt cn))
    · exact List.Lex.cons (List.Lex.rel skc)
  · intro terminal real nonempty
    simp only [projected,terminal,real,Bool.false_eq_true,ite_false,ite_true,zc,zk]
    exact List.Lex.cons (List.Lex.rel (nil_lt nonempty))
  · have distinct : shell m n c ≠ shell m n k := ne_of_gt skc
    cases rc <;> cases rk
    · simp [projected,zc,zk]
    · simp [projected,zc,zk]
    · simp [projected,zc,zk,cn]
    · simp [projected,zc,zk,distinct]

private theorem atomic_of_good (m : RawMolecule) (a : Nat) (z : Element)
    (good : RingOxaziridineNitrogen.atomIs m a z = true) : atomicNumber m a = z.atomicNumber := by
  cases h : m.atoms[a]? with
  | none => simp [RingOxaziridineNitrogen.atomIs,h] at good
  | some atom =>
    have facts : (atom.element = z ∧ atom.charge = 0) ∧ (!atom.aromatic) = true := by
      simpa only [RingOxaziridineNitrogen.atomIs,h,Option.any_some,Bool.and_eq_true,beq_iff_eq] using good
    simp [atomicNumber,h,facts.1.1]

/-- Recognition supplies the three physical IDs and every projected ordering
case without caller-supplied rankings. -/
theorem recognized_projected_order (m : RawMolecule) (n : Nat)
    (recognized : RingOxaziridineNitrogen.constrainedRaw m n = true) :
    ∃ o c k : Nat, (neighbors m n).Perm [o,c,k] ∧
      ∀ ro rc rk : Bool,
        projected m n c rc < projected m n o ro ∧
        projected m n k rk < projected m n o ro ∧
        (rc = true → projected m n k rk < projected m n c rc) ∧
        (rc = false → rk = true → shell m n k ≠ [] → projected m n c rc < projected m n k rk) ∧
        (projected m n c rc = projected m n k rk ↔
          rc = false ∧ (rk = false ∨ shell m n k = [])) := by
  obtain ⟨o,c,k,perm,strict,go,gc,gk,bond⟩ :=
    RingOxaziridineRootOrder.descending_row_with_roles_of_constrained m n recognized
  have ranked : (signature m n c < signature m n o ∧ signature m n k < signature m n o) ∧
      signature m n k < signature m n c := by
    simpa [List.pairwise_cons] using strict
  exact ⟨o,c,k,perm,projected_order (atomic_of_good m o .O go)
    (atomic_of_good m c .C gc) (atomic_of_good m k .C gk) ranked.2⟩

/-- The projection is exactly the proved physical two-shell prefix at every
actual direction, including retained inward directions and closure leaves. -/
theorem projected_physical (i : Input) (f : Site i) (a : Direction i f) :
    projected i.molecule (siteAtom i f).val (siteAtom i a.val).val
      (decide (a.val.val.node.provenance = .realAtom)) = physical i f a := by
  rw [← RingSecondShellDecision.prefixFor_physical]
  simp [projected,RingSecondShellDecision.prefixFor]

open RingPyramidalSource (Directions slots atomId)
open RingPyramidalTwoShell (score)
open private direction_rank from TetraStereo.Engine.RingPyramidalConstitution

/-- Actual incoming and outgoing directions use exactly the provenance-aware
physical projection, without reconstructing a molecular comparison key. -/
theorem score_projected {i : Input} {q : RingActivePairs.Site i} {a : i.certified.Atom}
    (current : q.val.node.current? = some a) (d : Directions i q) (s : Fin 3) :
    score d s = projected i.molecule a.val (atomId d s)
      (decide ((d.arm s).occurrence.val.node.provenance = .realAtom)) := by
  simp [score,RingSecondShellDecision.prefixFor,RingPyramidalTwoShell.direction,
    siteAtom,current,d.real,projected,atomId]

private theorem projected_collision {m : RawMolecule} {n o c k u v : Nat}
    (zo : atomicNumber m o = 8) (zc : atomicNumber m c = 6) (zk : atomicNumber m k = 6)
    (raw : signature m n k < signature m n c)
    (hu : u = o ∨ u = c ∨ u = k) (hv : v = o ∨ v = c ∨ v = k)
    (different : u ≠ v) (ru rv : Bool)
    (same : projected m n u ru = projected m n v rv) :
    (projected m n u ru)[1]? = some [] ∧ (ru = false ∨ rv = false) := by
  have first := congrArg (fun (w : List (List Nat)) => w.head?) same
  simp only [projected,List.head?_cons,Option.some.injEq,List.cons.injEq,and_true] at first
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact (different rfl).elim
  · simp [zo,zc] at first
  · simp [zo,zk] at first
  · simp [zc,zo] at first
  · exact (different rfl).elim
  · have tie := ((projected_order zo zc zk raw false ru rv).2.2.2.2).mp same
    exact ⟨by simp [projected,tie.1],Or.inl tie.1⟩
  · simp [zk,zo] at first
  · have tie := ((projected_order zo zc zk raw false rv ru).2.2.2.2).mp same.symm
    exact ⟨by rw [same]; simp [projected,tie.1],Or.inr tie.1⟩
  · exact (different rfl).elim

/-- Every equal two-shell score at a real occurrence of the recognized motif
is a residual carbon collision: its second row is empty, at least one endpoint
is nonreal, and the two directions represent distinct physical atoms. -/
theorem collision {i : Input} {q : RingActivePairs.Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingOxaziridineNitrogen.constrained i a = true)
    (d : Directions i q) (s t : Fin 3) (different : s ≠ t) (same : score d s = score d t) :
    (score d s)[1]? = some [] ∧
      ((d.arm s).occurrence.val.node.provenance ≠ .realAtom ∨
        (d.arm t).occurrence.val.node.provenance ≠ .realAtom) ∧ d.atom s ≠ d.atom t := by
  have selected := RingOxaziridinePublication.motif_focus real current motif
  have degree := (RingOxaziridinePublication.motif_gates a motif).2
  have size := (RingAtomicNeighborOrder.degree_eq i a).symm.trans degree
  let enum := RingAtomicNeighborOrder.enumeration i a size
  obtain ⟨e,matched⟩ := direction_rank d selected enum
  have injective : Function.Injective d.atom := by
    intro x y eq
    apply e.injective
    apply enum.injective
    apply Subtype.ext
    simpa only [← matched] using eq
  have distinct : atomId d s ≠ atomId d t := by
    intro eq
    exact different (injective (Fin.ext eq))
  obtain ⟨o,c,k,perm,strict,go,gc,gk,bond⟩ :=
    RingOxaziridineRootOrder.descending_row_with_roles_of_constrained i.molecule a.val motif
  have ids : (slots.map (atomId d)).Perm [o,c,k] := by
    have p := (Equiv.Perm.map_finRange_perm e).map (fun x => (enum x).val.val)
    rw [List.map_map] at p
    have keyEq : atomId d = fun x => (enum (e x)).val.val :=
      funext fun x => congrArg Fin.val (matched x)
    rw [keyEq]
    exact p.trans ((RingAtomicNeighborOrder.enumeration_ids i a size) ▸ perm)
  have roles (x : Fin 3) : atomId d x = o ∨ atomId d x = c ∨ atomId d x = k := by
    have mem := ids.mem_iff.mp (List.mem_map.mpr ⟨x,by fin_cases x <;> decide,rfl⟩)
    simpa using mem
  have ranked : (signature i.molecule a.val c < signature i.molecule a.val o ∧
      signature i.molecule a.val k < signature i.molecule a.val o) ∧
      signature i.molecule a.val k < signature i.molecule a.val c := by
    simpa [List.pairwise_cons] using strict
  rw [score_projected current d s,score_projected current d t] at same
  have result := projected_collision (atomic_of_good _ _ .O go) (atomic_of_good _ _ .C gc)
    (atomic_of_good _ _ .C gk) ranked.2 (roles s) (roles t) distinct _ _ same
  refine ⟨by simpa only [score_projected current d s] using result.1,?_,injective.ne different⟩
  simpa only [decide_eq_false_iff_not] using result.2

/-- A strict projected order fixes the complete constitutional order of
actual directions, including every remaining atomic, duplicate and mass row. -/
theorem constitution_of_projected {i : Input} {f : Site i} (a b : Direction i f)
    (strict : projected i.molecule (siteAtom i f).val (siteAtom i a.val).val
        (decide (a.val.val.node.provenance = .realAtom)) <
      projected i.molecule (siteAtom i f).val (siteAtom i b.val).val
        (decide (b.val.val.node.provenance = .realAtom))) :
    orderWord (keyFor a) < orderWord (keyFor b) := by
  apply RingAllLigandTwoShell.word_lt_of_prefix a b
  simpa only [projected_physical] using strict

/-- The executable three-ligand score has the same strict-order consequence. -/
theorem constitution_of_score {i : Input} {q : RingActivePairs.Site i}
    (d : Directions i q) (s t : Fin 3) (strict : score d s < score d t) :
    orderWord (keyFor (RingPyramidalTwoShell.direction d s)) <
      orderWord (keyFor (RingPyramidalTwoShell.direction d t)) := by
  apply RingAllLigandTwoShell.word_lt_of_prefix
  simpa only [score,RingSecondShellDecision.prefixFor_physical] using strict

end TetraStereo.Engine.RingOxaziridineAuxOrder
assert_kernel_only TetraStereo.Engine.RingOxaziridineAuxOrder.recognized_projected_order
assert_kernel_only TetraStereo.Engine.RingOxaziridineAuxOrder.projected_physical

assert_kernel_only TetraStereo.Engine.RingOxaziridineAuxOrder.collision
