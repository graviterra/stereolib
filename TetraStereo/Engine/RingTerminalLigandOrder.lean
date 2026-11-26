import TetraStereo.Engine.RingPyramidalTwoShell
import TetraStereo.Engine.RingPyramidalPathProvenance

/-! An empty second atomic row exhausts a ligand's Rule 1a tree. At equal
atomic rows such ligands can be compared immediately by their Rule 1b origins. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingTerminalLigandOrder
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingRetainedChemicalTrace
open RingRetainedChemicalPreorder (Direction keyFor orderWord read_key)
open private source_children from TetraStereo.Engine.RingChildKeyRecovery
open private makeColumn byDescending from TetraStereo.Engine.RingRetainedChemicalTrace
attribute [local instance] lexOrd

def duplicate (count : Nat) : OfficialCIPNodeProvenance → Nat
  | .ringDuplicate atRoot => count + 1 - atRoot
  | _ => 0

private theorem observed {i : Input} {q : RingActivePairs.Arm i} {term : Bool} {o : Observation}
    (h : observation? i q term = some o) :
    o.duplicate = duplicate i.molecule.atomCount q.occurrence.val.node.provenance ∧
    (∀ d, q.occurrence.val.node.provenance = .ringDuplicate d → d ≤ i.molecule.atomCount) := by
  cases prov : q.occurrence.val.node.provenance with
  | realAtom => exact ⟨(real_source prov h).1, by simp⟩
  | ringDuplicate d =>
    unfold observation? at h
    obtain ⟨a,_,tail⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨z,_,tail⟩ := Option.bind_eq_some_iff.mp tail
    obtain ⟨_,_,tail⟩ := Option.bind_eq_some_iff.mp tail
    simp only [prov] at tail
    obtain ⟨_,guarded,tail⟩ := Option.bind_eq_some_iff.mp tail
    obtain ⟨mass,_,out⟩ := Option.bind_eq_some_iff.mp tail
    obtain rfl := Option.some.inj out
    refine ⟨rfl,?_⟩
    intro x ex
    obtain rfl := OfficialCIPNodeProvenance.ringDuplicate.inj ex
    by_contra! bad
    simp [guard,Nat.not_le.mpr bad] at guarded
  | _ =>
    simp [observation?,prov] at h

theorem origin_value {i : Input} {q : RingActivePairs.Arm i} {k : Key}
    (h : key? i q = some k) :
    k.root.duplicate = duplicate i.molecule.atomCount q.occurrence.val.node.provenance ∧
    (∀ d, q.occurrence.val.node.provenance = .ringDuplicate d → d ≤ i.molecule.atomCount) := by
  cases key_source h with
  | node _ obs _ _ _ => exact observed obs

private theorem empty_key {i : Input} {q : RingActivePairs.Arm i} {k : Key}
    (h : key? i q = some k) (empty : k.atomic.word[1]? = some []) : k = assemble k.root [] := by
  obtain ⟨o,hk,_,_⟩ := source_children h
  rw [hk] at empty ⊢
  change _ = assemble o []
  congr 1
  have length := congrArg (Option.map List.length) empty
  simpa [assemble,makeColumn,Observation.atStage,byDescending] using length

/-- On two exhausted arms, these three scalar comparisons recover the full
constitutional comparator, including equality of the complete words. -/
theorem compare_exhausted {i : Input} {u v : RingActivePairs.Arm i} {a b : Key}
    (ha : key? i u = some a) (hb : key? i v = some b)
    (ea : a.atomic.word[1]? = some []) (eb : b.atomic.word[1]? = some []) :
    compare (orderWord a) (orderWord b) =
      (compare a.root.atomic b.root.atomic).then
        ((compare (duplicate i.molecule.atomCount u.occurrence.val.node.provenance)
          (duplicate i.molecule.atomCount v.occurrence.val.node.provenance)).then
        (compare a.root.mass b.root.mass)) := by
  rw [←(origin_value ha).1,←(origin_value hb).1]
  conv_lhs => rw [empty_key ha ea,empty_key hb eb]
  simp only [orderWord,assemble,makeColumn,byDescending,List.mergeSort_nil,List.map_nil,List.foldr_nil,
    List.flatten_cons,List.flatten_nil,List.append_nil,Observation.atStage,List.compare_cons_cons]
  cases compare a.root.atomic b.root.atomic <;> cases compare a.root.duplicate b.root.duplicate <;>
    cases compare a.root.mass b.root.mass <;> rfl

theorem leaf_lt {i : Input} {u v : RingActivePairs.Arm i} {a b : Key}
    (ha : key? i u = some a) (hb : key? i v = some b)
    (ea : a.atomic.word[1]? = some []) (eb : b.atomic.word[1]? = some [])
    (z : a.root.atomic = b.root.atomic)
    (lt : duplicate i.molecule.atomCount u.occurrence.val.node.provenance <
      duplicate i.molecule.atomCount v.occurrence.val.node.provenance) : orderWord a < orderWord b := by
  have ord := lt
  rw [←(origin_value ha).1,←(origin_value hb).1] at ord
  conv_lhs => rw [empty_key ha ea]
  conv_rhs => rw [empty_key hb eb]
  simp only [orderWord,assemble,makeColumn,byDescending,List.mergeSort_nil,List.map_nil,List.foldr_nil,List.flatten_cons,List.flatten_nil,List.append_nil,Observation.atStage]
  change [[ [a.root.atomic],[],[] ], [[a.root.duplicate],[],[]], _] <
    [[ [b.root.atomic],[],[] ], [[b.root.duplicate],[],[]], _]
  rw [z]
  exact List.Lex.cons (List.Lex.rel (List.Lex.rel (List.Lex.rel ord)))

def twoRows {i : Input} {f : Site i} (a : Direction i f) := RingSecondShellDecision.prefixFor i f a

def bonus {i : Input} {f : Site i} (a : Direction i f) : Nat :=
  if (twoRows a)[1]? = some [] then duplicate i.molecule.atomCount a.val.val.node.provenance else 0

def rank {i : Input} {f : Site i} (a : Direction i f) : List Word := [twoRows a,[[bonus a]]]

theorem rank_lt {i : Input} {f : Site i} (a b : Direction i f) (h : rank a < rank b) :
    orderWord (keyFor a) < orderWord (keyFor b) := by
  by_cases eqn : twoRows a = twoRows b
  · have lt : bonus a < bonus b := by
      have small : [[[bonus a]]] < [[[bonus b]]] := by simpa [rank,eqn] using h
      exact (List.lex_singleton_iff ..).mp ((List.lex_singleton_iff ..).mp ((List.lex_singleton_iff ..).mp small))
    by_cases empty : (twoRows b)[1]? = some []
    · have aempty : (twoRows a)[1]? = some [] := eqn ▸ empty
      have get (x : Direction i f) :
          (keyFor x).atomic.word[1]? = (twoRows x)[1]? := by
        conv_lhs => rw [RingAllLigandTwoShell.atomic_decomposition x]
        rw [twoRows,RingSecondShellDecision.prefixFor_physical]
        rfl
      apply leaf_lt (read_key a) (read_key b) ((get a).trans aempty) ((get b).trans empty)
      · have z (x : Direction i f) : (keyFor x).root.atomic =
            RingAtomicNeighborOrder.atomicNumber i.molecule (RingAllLigandTwoShell.siteAtom i x.val).val := by
          rw [RingPyramidalConstitution.key_atomic (RingAllLigandTwoShell.site_current i x.val)
            (RingAtomicNeighborOrder.written i _) (read_key x)]
          simp [RingAtomicNeighborOrder.atomicNumber,RingAtomicNeighborOrder.written]
        rw [z,z]
        exact List.singleton_inj.mp (List.cons.inj eqn).1
      · simpa [bonus,aempty,empty] using lt
    · simp [bonus,eqn,empty] at lt
  · apply RingAllLigandTwoShell.word_lt_of_prefix
    rw [←RingSecondShellDecision.prefixFor_physical,←RingSecondShellDecision.prefixFor_physical]
    rcases List.cons_lex_cons_iff.mp h with first | same
    · exact first
    · exact (eqn same.1).elim

/-- Among two distinct physical arms of the same real occurrence, a closure
always has a different duplicate value from its opponent, including a second
closure. Both original distances index the same history. -/
theorem duplicate_ne {i : Input} {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (d : RingPyramidalSource.Directions i q) (s t : Fin 3) (different : d.atom s ≠ d.atom t)
    (closure : (d.arm s).occurrence.val.node.provenance ≠ .realAtom ∨
      (d.arm t).occurrence.val.node.provenance ≠ .realAtom) :
    duplicate i.molecule.atomCount (d.arm s).occurrence.val.node.provenance ≠
      duplicate i.molecule.atomCount (d.arm t).occurrence.val.node.provenance := by
  let node := q.val.node
  have closed (u : Fin 3) (off : (d.arm u).occurrence.val.node.provenance ≠ .realAtom) :
      d.atom u ∈ node.history ∧
      (d.arm u).occurrence.val.node.provenance = .ringDuplicate (node.duplicateRootDistance (d.atom u)) ∧
      node.duplicateRootDistance (d.atom u) ≤ i.molecule.atomCount := by
    obtain ⟨classify,mark⟩ := RingPyramidalPathProvenance.arm_endpoint
      q a (d.atom u) real current (d.arm u) (d.mem u) (d.real u)
    have visited : d.atom u ∈ node.history := by
      by_contra absent
      exact off (classify.mpr (Or.inr absent))
    have dup := (mark (fun back => off (classify.mpr (Or.inl back))) visited).1
    obtain ⟨k,hk⟩ := RingRetainedChemicalCoverage.key_total i
      (RingRetainedChemicalCoverage.admitted_atoms i) _ (d.valid u)
    exact ⟨visited,dup,(origin_value hk).2 _ dup⟩
  by_cases sr : (d.arm s).occurrence.val.node.provenance = .realAtom
  · obtain ⟨_,dup,bound⟩ := closed t (closure.resolve_left (not_not_intro sr))
    simp only [sr,dup,duplicate]
    omega
  · obtain ⟨sv,sd,sb⟩ := closed s sr
    by_cases tr : (d.arm t).occurrence.val.node.provenance = .realAtom
    · simp only [sd,tr,duplicate]
      omega
    · obtain ⟨tv,td,tb⟩ := closed t tr
      intro same
      simp only [sd,td,duplicate] at same
      exact different (RingPyramidalPathProvenance.duplicate_distance_injective node sv tv (by omega))

end TetraStereo.Engine.RingTerminalLigandOrder
assert_kernel_only TetraStereo.Engine.RingTerminalLigandOrder.leaf_lt
assert_kernel_only TetraStereo.Engine.RingTerminalLigandOrder.rank_lt
assert_kernel_only TetraStereo.Engine.RingTerminalLigandOrder.duplicate_ne
assert_kernel_only TetraStereo.Engine.RingTerminalLigandOrder.compare_exhausted
