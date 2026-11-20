import TetraStereo.OneCenter.LocalizedChemicalRingRelabel
import TetraStereo.OneCenter.LocalizedMarkedCyclicDiscardedReference
import TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantEvaluator
import TetraStereo.OneCenter.LocalizedMarkedGeneratedFactUniqueness
import TetraStereo.OneCenter.LocalizedMarkedConfigurationTransport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Symmetry transport of recursively generated marked readings

For a molecular symmetry `σ` (`LocalizedChemicalRingRelabel.StructuralSymmetry`) and an operations record
whose empty-state orders and generated-state marked rankings are relabel-covariant on reached
occurrences (`Covariant`), the recursively generated auxiliary facts at the `σ`-image occurrence
are, up to order, the relabelled facts of the source occurrence evaluated under the pulled-back
geometry `geom ∘ σ` (`factsWith_map`). The recursion is parameterized by its one-occurrence step,
so the statement covers both the existing evaluator (`LocalizedMarkedOperationEvaluator`) and the
distant-reference successor (`LocalizedPhysicalMarkedDistantEvaluator`).

At a centre fixed by `σ` whose frame is exchanged by a single transposition, two consequences
follow for every recursion depth, every geometry and both evaluators:

* `root_refuses`: if the pulled-back geometry reads like the original at every occurrence below
  the centre (a common **proper** sense of `σ` on the reached branches), the centre is refused;
* `root_not_chiral`: if it reads like the **reflected** geometry there (a common **mirror**
  sense), the centre never receives an uppercase descriptor.

These are soundness statements for the generated readings: refusal under a proper branch
symmetry and absence of a chiral letter under a mirror branch symmetry. No desired label,
sorting success, branch equivalence or final correctness is supplied. The covariance of the
actual retained/sparse operations and the completeness direction (distinct readings for
physically distinguishable branches) are separate obligations and are not claimed here.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport

open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? readback? atomsAt? rankedAtoms?
  consistent strict eligibleOf consensus appendFacts? caseFromMirror? factOf mirror
  readback_mirror flatMap_congr_mem structuralDepth)
open LocalizedMarkedOperationEvaluator (Operations tiedChildren underWith markedReading?
  mem_tiedChildren_actual)
open LocalizedMarkedReachableConfigurations (Reached reached_root reached_child)
open LocalizedMarkedReachedFrameNeighbors (SingleBonded reached_atom_valid)
open LocalizedMarkedCyclicDiscardedReference (consensus_some readback_length readback_nodup
  rankedAtoms_subset)
open LocalizedMarkedTerminalGaugeSwap (swapAtom readback_swapAtom mapM_getElem?_forall₂
  forall₂_mem_right)
open LocalizedMarkedConfigurationTransport (frame_length)
open LocalizedChemicalRingRelabel
open DeclarativeCIP.ProductionOccurrenceRules456 (appendInputFact?)

abbrev Node := RawMolecule.CanonicalBranchNode

/-! ## The recursion, parameterized by its one-occurrence step -/

/-- One-occurrence raw step of a recursive marked evaluator. -/
abbrev Step := RawMolecule → Operations → Geometry → OccurrenceAuxState → Option Nat → Node →
  (Nat → OccurrenceAuxState) → Option RS

/-- The shared occurrence recursion of both evaluators. -/
def factsWith (step : Step) (mol : RawMolecule) (ops : Operations) :
    Nat → Geometry → OccurrenceAuxState → Option Nat → Node → OccurrenceAuxState
  | 0, _, _, _, _ => []
  | depth + 1, geom, state, ctx, node =>
      (caseFromMirror?
        (step mol ops geom state ctx node
          (underWith mol ops geom state node (factsWith step mol ops depth)))
        (step mol ops (mirror geom) state ctx node
          (underWith mol ops (mirror geom) state node (factsWith step mol ops depth)))).toList.map
            (factOf node) ++
        (mol.canonicalChildren node).flatMap (factsWith step mol ops depth geom state ctx)

/-- The cased descriptor of an occurrence whose descendants are evaluated at `depth`. -/
def descriptorWith (step : Step) (mol : RawMolecule) (ops : Operations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  caseFromMirror?
    (step mol ops geom state ctx node
      (underWith mol ops geom state node (factsWith step mol ops depth)))
    (step mol ops (mirror geom) state ctx node
      (underWith mol ops (mirror geom) state node (factsWith step mol ops depth)))

theorem factsWith_succ (step : Step) (mol : RawMolecule) (ops : Operations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node) :
    factsWith step mol ops (depth + 1) geom state ctx node =
      (descriptorWith step mol ops depth geom state ctx node).toList.map (factOf node) ++
        (mol.canonicalChildren node).flatMap (factsWith step mol ops depth geom state ctx) := rfl

/-- The existing evaluator is the recursion at its own step. -/
theorem facts_eq_factsWith (mol : RawMolecule) (ops : Operations) :
    ∀ depth, LocalizedMarkedOperationEvaluator.facts mol ops depth =
      factsWith LocalizedMarkedOperationEvaluator.rawStep? mol ops depth := by
  intro depth
  induction depth with
  | zero => rfl
  | succ depth ih =>
      funext geom state ctx node
      rw [LocalizedMarkedOperationEvaluator.facts_succ, factsWith_succ]
      unfold LocalizedMarkedOperationEvaluator.descriptor?
        LocalizedMarkedOperationEvaluator.descriptorWith?
        LocalizedMarkedOperationEvaluator.rawWith? descriptorWith
      rw [ih]

theorem descriptor_eq_descriptorWith (mol : RawMolecule) (ops : Operations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node) :
    LocalizedMarkedOperationEvaluator.descriptor? mol ops depth geom state ctx node =
      descriptorWith LocalizedMarkedOperationEvaluator.rawStep? mol ops depth geom state ctx node := by
  unfold LocalizedMarkedOperationEvaluator.descriptor?
    LocalizedMarkedOperationEvaluator.descriptorWith? LocalizedMarkedOperationEvaluator.rawWith?
    descriptorWith
  rw [facts_eq_factsWith]

/-- The distant-reference successor is the recursion at its own step. -/
theorem distant_facts_eq_factsWith (mol : RawMolecule) (ops : Operations) :
    ∀ depth, LocalizedPhysicalMarkedDistantEvaluator.facts mol ops depth =
      factsWith LocalizedPhysicalMarkedDistantReference.rawStep? mol ops depth := by
  intro depth
  induction depth with
  | zero => rfl
  | succ depth ih =>
      funext geom state ctx node
      rw [LocalizedPhysicalMarkedDistantEvaluator.facts_succ, factsWith_succ]
      unfold LocalizedPhysicalMarkedDistantEvaluator.descriptor?
        LocalizedPhysicalMarkedDistantEvaluator.descriptorWith?
        LocalizedPhysicalMarkedDistantEvaluator.rawWith? descriptorWith
      rw [ih]

theorem distant_descriptor_eq_descriptorWith (mol : RawMolecule) (ops : Operations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node) :
    LocalizedPhysicalMarkedDistantEvaluator.descriptor? mol ops depth geom state ctx node =
      descriptorWith LocalizedPhysicalMarkedDistantReference.rawStep? mol ops depth geom state ctx
        node := by
  unfold LocalizedPhysicalMarkedDistantEvaluator.descriptor?
    LocalizedPhysicalMarkedDistantEvaluator.descriptorWith?
    LocalizedPhysicalMarkedDistantEvaluator.rawWith? descriptorWith
  rw [distant_facts_eq_factsWith]

/-! ## Elementary facts about consensus, fact extension and readback -/

theorem consensus_cons_cons (x y : Option RS) (rest : List (Option RS)) :
    consensus (x :: y :: rest) =
      match x, consensus (y :: rest) with
      | some a, some b => if a = b then some a else none
      | _, _ => none := rfl

theorem consensus_eq_some_iff : ∀ (l : List (Option RS)) (v : RS),
    consensus l = some v ↔ l ≠ [] ∧ ∀ e ∈ l, e = some v
  | [], v => by simp [consensus]
  | [x], v => by simp [consensus]
  | x :: y :: rest, v => by
      rw [consensus_cons_cons]
      constructor
      · intro h
        rcases x with _ | a
        · simp at h
        · cases hc : consensus (y :: rest) with
          | none => rw [hc] at h; simp at h
          | some b =>
              rw [hc] at h
              simp only at h
              split_ifs at h with hab
              have hav : a = v := Option.some.inj h
              have tail := (consensus_eq_some_iff (y :: rest) v).mp (by rw [hc, ← hab, hav])
              refine ⟨by simp, ?_⟩
              intro e he
              rcases List.mem_cons.mp he with rfl | later
              · rw [hav]
              · exact tail.2 e later
      · rintro ⟨_, all⟩
        have hx := all x List.mem_cons_self
        have tail : consensus (y :: rest) = some v :=
          (consensus_eq_some_iff (y :: rest) v).mpr
            ⟨by simp, fun e he => all e (List.mem_cons_of_mem x he)⟩
        rw [hx, tail]
        simp

/-- Consensus is insensitive to the order of the readings. -/
theorem consensus_perm {l l' : List (Option RS)} (perm : l.Perm l') : consensus l = consensus l' := by
  cases h : consensus l with
  | some v =>
      rw [consensus_eq_some_iff] at h
      symm
      rw [consensus_eq_some_iff]
      refine ⟨fun nil => h.1 (List.perm_nil.mp (nil ▸ perm)), fun e he => h.2 e (perm.mem_iff.mpr he)⟩
  | none =>
      cases h' : consensus l' with
      | none => rfl
      | some v =>
          exfalso
          rw [consensus_eq_some_iff] at h'
          have := (consensus_eq_some_iff l v).mpr
            ⟨fun nil => h'.1 (List.perm_nil.mp (nil ▸ perm.symm)),
              fun e he => h'.2 e (perm.mem_iff.mp he)⟩
          rw [h] at this
          cases this

/-- Fact extension from a duplicate-free state succeeds exactly when the combined keys are
duplicate-free, and then appends. -/
theorem appendFacts_eq_ite : ∀ (added state : OccurrenceAuxState), (state.map (·.key)).Nodup →
    appendFacts? state added =
      if ((state ++ added).map (·.key)).Nodup then some (state ++ added) else none
  | [], state, nodup => by simp [appendFacts?, nodup]
  | fact :: rest, state, nodup => by
      simp only [appendFacts?, appendInputFact?]
      by_cases clash : ∃ old ∈ state, old.key = fact.key
      · have anyTrue : (state.any fun existing => existing.key == fact.key) = true := by
          rw [List.any_eq_true]
          obtain ⟨old, member, eq⟩ := clash
          exact ⟨old, member, by simp [eq]⟩
        rw [if_pos anyTrue]
        have notNodup : ¬ ((state ++ fact :: rest).map (·.key)).Nodup := by
          intro h
          rw [List.map_append, List.nodup_append] at h
          obtain ⟨old, member, eq⟩ := clash
          exact h.2.2 old.key (List.mem_map_of_mem member) fact.key (by simp) eq
        simp only [Option.bind_eq_bind, Option.bind_none]
        rw [if_neg notNodup]
      · have anyFalse : (state.any fun existing => existing.key == fact.key) = false := by
          rw [List.any_eq_false]
          intro old member eq
          exact clash ⟨old, member, by simpa using eq⟩
        rw [if_neg (by simp [anyFalse])]
        simp only [Option.bind_eq_bind, Option.bind_some]
        have nodup' : ((state ++ [fact]).map (·.key)).Nodup := by
          rw [List.map_append, List.nodup_append]
          refine ⟨nodup, List.nodup_singleton _, ?_⟩
          intro k hk k' hk' eq
          rw [List.mem_map] at hk
          obtain ⟨old, member, rfl⟩ := hk
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hk'
          exact clash ⟨old, member, eq.trans hk'⟩
        rw [appendFacts_eq_ite rest (state ++ [fact]) nodup', List.append_assoc,
          List.singleton_append]

theorem appendFacts_nil_eq (added : OccurrenceAuxState) :
    appendFacts? [] added = if (added.map (·.key)).Nodup then some added else none := by
  rw [appendFacts_eq_ite added [] List.nodup_nil, List.nil_append]

/-- Relabelled keys. -/
def mapKey (σ : Nat → Nat) (key : CanonicalOccurrenceKey) : CanonicalOccurrenceKey :=
  ⟨key.history.map σ, key.provenance⟩

theorem mapFact_key_eq (σ : Nat → Nat) (fact : OccurrenceAuxFact) :
    (mapFact σ fact).key = mapKey σ fact.key := rfl

theorem mapKey_injective {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ) :
    Function.Injective (mapKey σ) := by
  intro k k' eq
  have hist : k.history.map σ = k'.history.map σ := by
    have h := congrArg CanonicalOccurrenceKey.history eq
    exact h
  have prov : k.provenance = k'.provenance := by
    have h := congrArg CanonicalOccurrenceKey.provenance eq
    exact h
  have hist' : k.history = k'.history := sym.injective.list_map hist
  calc k = ⟨k.history, k.provenance⟩ := rfl
    _ = ⟨k'.history, k'.provenance⟩ := by rw [hist', prov]
    _ = k' := rfl

theorem keys_nodup_iff {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ)
    {state state' : OccurrenceAuxState} (perm : state'.Perm (state.map (mapFact σ))) :
    (state'.map (·.key)).Nodup ↔ (state.map (·.key)).Nodup := by
  rw [(perm.map (·.key)).nodup_iff, List.map_map]
  have : ((fun fact : OccurrenceAuxFact => fact.key) ∘ mapFact σ) =
      mapKey σ ∘ (fun fact : OccurrenceAuxFact => fact.key) := by
    funext fact
    rfl
  rw [this, ← List.map_map]
  exact ⟨List.Nodup.of_map _, fun h => h.map (mapKey_injective sym)⟩

theorem readback_nodup' (geom : Geometry) (l : List Nat) (v : RS) (h : readback? geom l = some v) :
    l.Nodup := by
  match l, readback_length geom l v h with
  | [a, b, c, d], _ => exact readback_nodup geom a b c d v h

theorem atomsAt_subset (atoms positions ranked : List Nat) (h : atomsAt? atoms positions = some ranked) :
    ∀ x ∈ ranked, x ∈ atoms := by
  intro x member
  obtain ⟨p, _, hp⟩ := forall₂_mem_right (mapM_getElem?_forall₂ atoms positions ranked h) x member
  exact List.mem_of_getElem? hp

/-- A frame transposition complements every reading built from the frame, including degenerate
and refused readings (which stay refused). -/
theorem readback_transposition (geom : Geometry) (atoms : List Nat) (four : atoms.length = 4)
    (a b : Nat) (ne : a ≠ b) (ha : a ∈ atoms) (hb : b ∈ atoms) (σ : Nat → Nat)
    (hσ : ∀ x ∈ atoms, σ x = swapAtom a b x) (ranked : List Nat)
    (sub : ∀ x ∈ ranked, x ∈ atoms) :
    readback? geom (ranked.map σ) = (readback? geom ranked).map RS.swap := by
  rw [List.map_congr_left (fun x hx => hσ x (sub x hx))]
  by_cases good : ranked.length = 4 ∧ ranked.Nodup
  · have perm : ranked.Perm atoms :=
      (good.2.subperm sub).perm_of_length_le (by rw [good.1, four])
    exact readback_swapAtom geom a b ne ranked good.2 good.1 (perm.mem_iff.mpr ha)
      (perm.mem_iff.mpr hb)
  · have right : readback? geom ranked = none := by
      cases h : readback? geom ranked with
      | none => rfl
      | some v => exact absurd ⟨readback_length geom ranked v h, readback_nodup' geom ranked v h⟩ good
    rw [right, Option.map_none]
    cases h : readback? geom (ranked.map (swapAtom a b)) with
    | none => rfl
    | some v =>
        exfalso
        apply good
        refine ⟨?_, List.Nodup.of_map _ (readback_nodup' geom _ v h)⟩
        have := readback_length geom _ v h
        simpa using this

theorem markedReading_mirror (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (mark : Nat) :
    markedReading? mol ops (mirror geom) state node mark =
      (markedReading? mol ops geom state node mark).map RS.swap := by
  unfold markedReading?
  cases frameAtoms? mol node with
  | none => rfl
  | some atoms =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases ops.marked state node mark with
      | none => rfl
      | some ranking =>
          simp only [Option.bind_some]
          cases rankedAtoms? atoms ranking with
          | none => rfl
          | some ranked => simp [readback_mirror]

theorem caseFromMirror_congr {a a' b b' : Option RS} (ha : a = a') (hb : b = b') :
    caseFromMirror? a b = caseFromMirror? a' b' := by rw [ha, hb]

/-! ## Relabel covariance of the operations -/

/-- Relation between the empty-state orders at the relabelled and the original occurrence. -/
def OrdinaryRel (σ : Nat → Nat) (atoms atoms' : List Nat) :
    Option (List Nat × List (Option Ordering)) → Option (List Nat × List (Option Ordering)) → Prop
  | none, none => True
  | some (sorted', adjacent'), some (sorted, adjacent) =>
      consistent adjacent' = consistent adjacent ∧ strict adjacent' = strict adjacent ∧
        (strict adjacent = true →
          atomsAt? atoms' sorted' = (atomsAt? atoms sorted).map (List.map σ)) ∧
        (eligibleOf atoms' sorted' adjacent').Perm ((eligibleOf atoms sorted adjacent).map σ)
  | _, _ => False

theorem ordinaryRel_none_none (σ : Nat → Nat) (atoms atoms' : List Nat) :
    OrdinaryRel σ atoms atoms' none none = True := rfl
theorem ordinaryRel_none_some (σ : Nat → Nat) (atoms atoms' : List Nat)
    (result : List Nat × List (Option Ordering)) :
    OrdinaryRel σ atoms atoms' none (some result) = False := by
  obtain ⟨_, _⟩ := result; rfl
theorem ordinaryRel_some_none (σ : Nat → Nat) (atoms atoms' : List Nat)
    (result : List Nat × List (Option Ordering)) :
    OrdinaryRel σ atoms atoms' (some result) none = False := by
  obtain ⟨_, _⟩ := result; rfl
theorem ordinaryRel_some_some (σ : Nat → Nat) (atoms atoms' sorted sorted' : List Nat)
    (adjacent adjacent' : List (Option Ordering)) :
    OrdinaryRel σ atoms atoms' (some (sorted', adjacent')) (some (sorted, adjacent)) =
      (consistent adjacent' = consistent adjacent ∧ strict adjacent' = strict adjacent ∧
        (strict adjacent = true →
          atomsAt? atoms' sorted' = (atomsAt? atoms sorted).map (List.map σ)) ∧
        (eligibleOf atoms' sorted' adjacent').Perm ((eligibleOf atoms sorted adjacent).map σ)) := rfl

/-- **Relabel covariance of an operations record** on reached occurrences: empty-state ordinary
orders correspond (strictness and consistency flags; the full atom order only when strict; the
tied-reference population up to order), and marked rankings under relabelled generated states
with duplicate-free keys and relabelled references return the relabelled priority atom lists.
Nothing is required at fabricated histories, tied full orders or duplicate-key states. -/
structure Covariant (mol : RawMolecule) (ops : Operations) (σ : Nat → Nat) : Prop where
  ordinary : ∀ node, Reached mol node → ∀ atoms atoms', frameAtoms? mol node = some atoms →
    frameAtoms? mol (mapNode σ node) = some atoms' →
      OrdinaryRel σ atoms atoms' (ops.ordinary [] (mapNode σ node)) (ops.ordinary [] node)
  marked : ∀ node, Reached mol node → ∀ atoms atoms', frameAtoms? mol node = some atoms →
    frameAtoms? mol (mapNode σ node) = some atoms' →
      ∀ state state', state'.Perm (state.map (mapFact σ)) → (state.map (·.key)).Nodup → ∀ r,
        (ops.marked state' (mapNode σ node) (σ r)).bind (rankedAtoms? atoms') =
          ((ops.marked state node r).bind (rankedAtoms? atoms)).map (List.map σ)

section Transport

variable {mol : RawMolecule} {ops : Operations} {σ : Nat → Nat}

theorem contains_perm_map (sym : StructuralSymmetry mol σ) {l l' : List Nat} (perm : l'.Perm (l.map σ))
    (x : Nat) : l'.contains (σ x) = l.contains x := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem, List.contains_iff_mem, perm.mem_iff, List.mem_map]
  constructor
  · rintro ⟨y, member, eq⟩
    rw [sym.injective eq] at member
    exact member
  · intro member
    exact ⟨x, member, rfl⟩

theorem mem_perm_map (sym : StructuralSymmetry mol σ) {l l' : List Nat} (perm : l'.Perm (l.map σ))
    (x : Nat) : σ x ∈ l' ↔ x ∈ l := by
  have := contains_perm_map sym perm x
  rw [← List.contains_iff_mem, ← List.contains_iff_mem, this]

/-- The marked reading at the relabelled occurrence with the relabelled reference and relabelled
state is the reading at the original occurrence under the pulled-back geometry. -/
theorem markedReading_map (cov : Covariant mol ops σ) (node : Node) (reached : Reached mol node)
    (atoms atoms' : List Nat) (frame : frameAtoms? mol node = some atoms)
    (frame' : frameAtoms? mol (mapNode σ node) = some atoms') (state state' : OccurrenceAuxState)
    (perm : state'.Perm (state.map (mapFact σ))) (nodup : (state.map (·.key)).Nodup) (r : Nat)
    (geom : Geometry) :
    markedReading? mol ops geom state' (mapNode σ node) (σ r) =
      markedReading? mol ops (pullback σ geom) state node r := by
  have h := cov.marked node reached atoms atoms' frame frame' state state' perm nodup r
  unfold markedReading?
  rw [frame, frame']
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases hm' : ops.marked state' (mapNode σ node) (σ r) with
  | none =>
      rw [hm', Option.bind_none] at h
      cases hm : ops.marked state node r with
      | none => rfl
      | some ranking =>
          rw [hm, Option.bind_some] at h
          simp only [Option.bind_none, Option.bind_some]
          cases hr : rankedAtoms? atoms ranking with
          | none => rfl
          | some ranked => rw [hr] at h; cases h
  | some ranking' =>
      rw [hm', Option.bind_some] at h
      cases hm : ops.marked state node r with
      | none =>
          rw [hm, Option.bind_none, Option.map_none] at h
          simp only [Option.bind_some, Option.bind_none, h]
      | some ranking =>
          rw [hm, Option.bind_some] at h
          simp only [Option.bind_some]
          cases hr : rankedAtoms? atoms ranking with
          | none => rw [hr, Option.map_none] at h; rw [h]; rfl
          | some ranked =>
              rw [hr, Option.map_some] at h
              rw [h]
              simp [readback_map]

/-- One reference evaluation, with fact extension, transports the same way. -/
theorem evaluate_map (sym : StructuralSymmetry mol σ) (cov : Covariant mol ops σ) (node : Node)
    (reached : Reached mol node) (atoms atoms' : List Nat) (frame : frameAtoms? mol node = some atoms)
    (frame' : frameAtoms? mol (mapNode σ node) = some atoms') (state state' : OccurrenceAuxState)
    (perm : state'.Perm (state.map (mapFact σ))) (r : Nat) (geom : Geometry) :
    ((appendFacts? [] state').bind fun temp =>
        markedReading? mol ops geom temp (mapNode σ node) (σ r)) =
      ((appendFacts? [] state).bind fun temp =>
        markedReading? mol ops (pullback σ geom) temp node r) := by
  rw [appendFacts_nil_eq, appendFacts_nil_eq]
  by_cases nodup : (state.map (·.key)).Nodup
  · rw [if_pos ((keys_nodup_iff sym perm).mpr nodup), if_pos nodup, Option.bind_some,
      Option.bind_some]
    exact markedReading_map cov node reached atoms atoms' frame frame' state state' perm nodup r geom
  · rw [if_neg (fun h => nodup ((keys_nodup_iff sym perm).mp h)), if_neg nodup]
    rfl

/-- Tied children are covariant up to order. -/
theorem tiedChildren_map (sym : StructuralSymmetry mol σ) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (single : SingleBonded mol) (cov : Covariant mol ops σ)
    (node : Node) (reached : Reached mol node) :
    (tiedChildren mol ops [] (mapNode σ node)).Perm
      ((tiedChildren mol ops [] node).map (mapNode σ)) := by
  cases frame : frameAtoms? mol node with
  | none =>
      have frame' := frameAtoms_map_none sym wellFormed unique single node frame
        (reached_atom_valid mol wellFormed node reached)
      simp [tiedChildren, frame, frame']
  | some atoms =>
      obtain ⟨atoms', frame', _⟩ := frameAtoms_map_some sym wellFormed unique single node atoms frame
        (reached_atom_valid mol wellFormed node reached)
      have rel := cov.ordinary node reached atoms atoms' frame frame'
      cases hord : ops.ordinary [] node with
      | none =>
          rw [hord] at rel
          cases hord' : ops.ordinary [] (mapNode σ node) with
          | none => simp [tiedChildren, frame, frame', hord, hord']
          | some result' => rw [hord', ordinaryRel_some_none] at rel; exact rel.elim
      | some result =>
          obtain ⟨sorted, adjacent⟩ := result
          rw [hord] at rel
          cases hord' : ops.ordinary [] (mapNode σ node) with
          | none => rw [hord', ordinaryRel_none_some] at rel; exact rel.elim
          | some result' =>
              obtain ⟨sorted', adjacent'⟩ := result'
              rw [hord', ordinaryRel_some_some] at rel
              obtain ⟨_, _, _, eligiblePerm⟩ := rel
              simp only [tiedChildren, frame, frame', hord, hord']
              refine ((children_map sym wellFormed unique single node).filter _).trans ?_
              rw [List.filter_map]
              apply List.Perm.of_eq
              congr 1
              apply List.filter_congr
              intro child _
              simp only [Function.comp_apply, mapNode_atom]
              exact contains_perm_map sym eligiblePerm child.atom

/-- Covariance of a one-occurrence step under relabelled generated child data. -/
def StepMap (step : Step) (mol : RawMolecule) (ops : Operations) (σ : Nat → Nat) : Prop :=
  ∀ node, Reached mol node → ∀ (geom : Geometry) (ctx : Option Nat)
    (under under' : Nat → OccurrenceAuxState),
    (∀ r, (under' (σ r)).Perm ((under r).map (mapFact σ))) →
      step mol ops geom [] (ctx.map σ) (mapNode σ node) under' =
        step mol ops (pullback σ geom) [] ctx node under

/-- **Generated facts transport along the symmetry.** Facts generated at the relabelled
occurrence (with relabelled inherited context) are, up to order, the relabelled facts generated
at the original occurrence under the pulled-back geometry, at every depth. -/
theorem factsWith_map (step : Step) (sym : StructuralSymmetry mol σ) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (single : SingleBonded mol) (cov : Covariant mol ops σ)
    (stepMap : StepMap step mol ops σ) :
    ∀ depth (geom : Geometry) (ctx : Option Nat) (node : Node), Reached mol node →
      (factsWith step mol ops depth geom [] (ctx.map σ) (mapNode σ node)).Perm
        ((factsWith step mol ops depth (pullback σ geom) [] ctx node).map (mapFact σ)) := by
  intro depth
  induction depth with
  | zero => intros; exact List.Perm.refl _
  | succ depth ih =>
      intro geom ctx node reached
      have under : ∀ (g : Geometry) r,
          (underWith mol ops g [] (mapNode σ node) (factsWith step mol ops depth) (σ r)).Perm
            ((underWith mol ops (pullback σ g) [] node (factsWith step mol ops depth) r).map
              (mapFact σ)) := by
        intro g r
        unfold underWith
        rw [List.map_flatMap]
        refine ((tiedChildren_map sym wellFormed unique single cov node reached).flatMap_right
          _).trans ?_
        rw [List.flatMap_map]
        apply List.Perm.flatMap_left
        intro child member
        exact ih g (some r) child (reached_child mol node child reached
          (mem_tiedChildren_actual mol ops [] node child member))
      have head : descriptorWith step mol ops depth geom [] (ctx.map σ) (mapNode σ node) =
          descriptorWith step mol ops depth (pullback σ geom) [] ctx node := by
        unfold descriptorWith
        exact caseFromMirror_congr (stepMap node reached geom ctx _ _ (under geom))
          (stepMap node reached (mirror geom) ctx _ _ (under (mirror geom)))
      rw [factsWith_succ, factsWith_succ, List.map_append, head]
      refine List.Perm.append (List.Perm.of_eq ?_) ?_
      · rw [List.map_map]
        apply List.map_congr_left
        intro d _
        exact factOf_map σ node d
      · rw [List.map_flatMap]
        refine ((children_map sym wellFormed unique single node).flatMap_right _).trans ?_
        rw [List.flatMap_map]
        apply List.Perm.flatMap_left
        intro child member
        exact ih geom ctx child (reached_child mol node child reached member)

/-- The generated child data of one reference transport along the symmetry. -/
theorem underWith_map (step : Step) (sym : StructuralSymmetry mol σ) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (single : SingleBonded mol) (cov : Covariant mol ops σ)
    (stepMap : StepMap step mol ops σ) (depth : Nat) (geom : Geometry) (node : Node)
    (reached : Reached mol node) (r : Nat) :
    (underWith mol ops geom [] (mapNode σ node) (factsWith step mol ops depth) (σ r)).Perm
      ((underWith mol ops (pullback σ geom) [] node (factsWith step mol ops depth) r).map
        (mapFact σ)) := by
  unfold underWith
  rw [List.map_flatMap]
  refine ((tiedChildren_map sym wellFormed unique single cov node reached).flatMap_right _).trans ?_
  rw [List.flatMap_map]
  apply List.Perm.flatMap_left
  intro child member
  exact factsWith_map step sym wellFormed unique single cov stepMap depth geom (some r) child
    (reached_child mol node child reached (mem_tiedChildren_actual mol ops [] node child member))

/-! ## The two steps are covariant -/

theorem rawStep_map (sym : StructuralSymmetry mol σ) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (single : SingleBonded mol) (cov : Covariant mol ops σ) :
    StepMap LocalizedMarkedOperationEvaluator.rawStep? mol ops σ := by
  intro node reached geom ctx under under' hu
  cases frame : frameAtoms? mol node with
  | none =>
      have frame' := frameAtoms_map_none sym wellFormed unique single node frame
        (reached_atom_valid mol wellFormed node reached)
      simp [LocalizedMarkedOperationEvaluator.rawStep?, frame, frame']
  | some atoms =>
      obtain ⟨atoms', frame', perm⟩ := frameAtoms_map_some sym wellFormed unique single node atoms frame
        (reached_atom_valid mol wellFormed node reached)
      have evaluate : ∀ r, ((appendFacts? [] (under' (σ r))).bind fun temp =>
          markedReading? mol ops geom temp (mapNode σ node) (σ r)) =
            ((appendFacts? [] (under r)).bind fun temp =>
              markedReading? mol ops (pullback σ geom) temp node r) :=
        fun r => evaluate_map sym cov node reached atoms atoms' frame frame' (under r) (under' (σ r))
          (hu r) r geom
      have nodupIff : atoms'.Nodup ↔ atoms.Nodup :=
        perm.nodup_iff.trans ⟨List.Nodup.of_map σ, fun h => h.map sym.injective⟩
      have rel := cov.ordinary node reached atoms atoms' frame frame'
      unfold LocalizedMarkedOperationEvaluator.rawStep?
      rw [frame, frame']
      cases hord : ops.ordinary [] node with
      | none =>
          rw [hord] at rel
          cases hord' : ops.ordinary [] (mapNode σ node) with
          | none => rfl
          | some result' => rw [hord', ordinaryRel_some_none] at rel; exact rel.elim
      | some result =>
          obtain ⟨sorted, adjacent⟩ := result
          rw [hord] at rel
          cases hord' : ops.ordinary [] (mapNode σ node) with
          | none => rw [hord', ordinaryRel_none_some] at rel; exact rel.elim
          | some result' =>
              obtain ⟨sorted', adjacent'⟩ := result'
              rw [hord', ordinaryRel_some_some] at rel
              obtain ⟨consistentEq, strictEq, atomsAtEq, eligiblePerm⟩ := rel
              simp only [Option.bind_eq_bind, Option.bind_some]
              by_cases bad : ¬ atoms.Nodup ∨ consistent adjacent = false
              · have bad' : ¬ atoms'.Nodup ∨ consistent adjacent' = false := by
                  rw [nodupIff, consistentEq]; exact bad
                rw [if_pos bad', if_pos bad]
              · have bad' : ¬ (¬ atoms'.Nodup ∨ consistent adjacent' = false) := by
                  rw [nodupIff, consistentEq]; exact bad
                rw [if_neg bad', if_neg bad]
                by_cases strictH : strict adjacent = true
                · have strictH' : strict adjacent' = true := by rw [strictEq]; exact strictH
                  rw [if_pos strictH', if_pos strictH, atomsAtEq strictH]
                  cases atomsAt? atoms sorted with
                  | none => rfl
                  | some ranked => simp [readback_map]
                · have strictH' : ¬ strict adjacent' = true := by rw [strictEq]; exact strictH
                  rw [if_neg strictH', if_neg strictH]
                  have consensusEq : consensus ((eligibleOf atoms' sorted' adjacent').map
                      fun r => (appendFacts? [] (under' r)).bind fun temp =>
                        markedReading? mol ops geom temp (mapNode σ node) r) =
                      consensus ((eligibleOf atoms sorted adjacent).map
                        fun r => (appendFacts? [] (under r)).bind fun temp =>
                          markedReading? mol ops (pullback σ geom) temp node r) := by
                    rw [consensus_perm (eligiblePerm.map _), List.map_map]
                    congr 1
                    apply List.map_congr_left
                    intro r _
                    exact evaluate r
                  cases ctx with
                  | none => exact consensusEq
                  | some r =>
                      simp only [Option.map_some, contains_perm_map sym perm r]
                      by_cases present : atoms.contains r = true
                      · rw [if_pos present, if_pos present]
                        exact evaluate r
                      · rw [if_neg present, if_neg present]
                        exact consensusEq

theorem distantStep_map (sym : StructuralSymmetry mol σ) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (single : SingleBonded mol) (cov : Covariant mol ops σ) :
    StepMap LocalizedPhysicalMarkedDistantReference.rawStep? mol ops σ := by
  intro node reached geom ctx under under' hu
  cases frame : frameAtoms? mol node with
  | none =>
      have frame' := frameAtoms_map_none sym wellFormed unique single node frame
        (reached_atom_valid mol wellFormed node reached)
      simp [LocalizedPhysicalMarkedDistantReference.rawStep?, frame, frame']
  | some atoms =>
      obtain ⟨atoms', frame', perm⟩ := frameAtoms_map_some sym wellFormed unique single node atoms frame
        (reached_atom_valid mol wellFormed node reached)
      have reading : ∀ r, LocalizedPhysicalMarkedDistantReference.inheritedRead? mol ops geom []
          (mapNode σ node) under' (σ r) =
            LocalizedPhysicalMarkedDistantReference.inheritedRead? mol ops (pullback σ geom) []
              node under r :=
        fun r => evaluate_map sym cov node reached atoms atoms' frame frame' (under r) (under' (σ r))
          (hu r) r geom
      have nodupIff : atoms'.Nodup ↔ atoms.Nodup :=
        perm.nodup_iff.trans ⟨List.Nodup.of_map σ, fun h => h.map sym.injective⟩
      have rel := cov.ordinary node reached atoms atoms' frame frame'
      unfold LocalizedPhysicalMarkedDistantReference.rawStep?
      rw [frame, frame']
      cases hord : ops.ordinary [] node with
      | none =>
          rw [hord] at rel
          cases hord' : ops.ordinary [] (mapNode σ node) with
          | none => rfl
          | some result' => rw [hord', ordinaryRel_some_none] at rel; exact rel.elim
      | some result =>
          obtain ⟨sorted, adjacent⟩ := result
          rw [hord] at rel
          cases hord' : ops.ordinary [] (mapNode σ node) with
          | none => rw [hord', ordinaryRel_none_some] at rel; exact rel.elim
          | some result' =>
              obtain ⟨sorted', adjacent'⟩ := result'
              rw [hord', ordinaryRel_some_some] at rel
              obtain ⟨consistentEq, strictEq, atomsAtEq, eligiblePerm⟩ := rel
              simp only [Option.bind_eq_bind, Option.bind_some]
              by_cases bad : ¬ atoms.Nodup ∨ consistent adjacent = false
              · have bad' : ¬ atoms'.Nodup ∨ consistent adjacent' = false := by
                  rw [nodupIff, consistentEq]; exact bad
                rw [if_pos bad', if_pos bad]
              · have bad' : ¬ (¬ atoms'.Nodup ∨ consistent adjacent' = false) := by
                  rw [nodupIff, consistentEq]; exact bad
                rw [if_neg bad', if_neg bad]
                by_cases strictH : strict adjacent = true
                · have strictH' : strict adjacent' = true := by rw [strictEq]; exact strictH
                  rw [if_pos strictH', if_pos strictH, atomsAtEq strictH]
                  cases atomsAt? atoms sorted with
                  | none => rfl
                  | some ranked => simp [readback_map]
                · have strictH' : ¬ strict adjacent' = true := by rw [strictEq]; exact strictH
                  rw [if_neg strictH', if_neg strictH]
                  have fallbackEq : consensus ((eligibleOf atoms' sorted' adjacent').map
                      (LocalizedPhysicalMarkedDistantReference.inheritedRead? mol ops geom []
                        (mapNode σ node) under')) =
                      consensus ((eligibleOf atoms sorted adjacent).map
                        (LocalizedPhysicalMarkedDistantReference.inheritedRead? mol ops
                          (pullback σ geom) [] node under)) := by
                    rw [consensus_perm (eligiblePerm.map _), List.map_map]
                    congr 1
                    apply List.map_congr_left
                    intro r _
                    exact reading r
                  cases ctx with
                  | none => simpa using fallbackEq
                  | some r =>
                      simp only [Option.map_some, LocalizedPhysicalMarkedDistantReference.chooseInherited]
                      by_cases present : r ∈ atoms
                      · rw [if_pos ((mem_perm_map sym perm r).mpr present), if_pos present]
                        exact reading r
                      · rw [if_neg (fun h => present ((mem_perm_map sym perm r).mp h)),
                          if_neg present, reading r]
                        cases LocalizedPhysicalMarkedDistantReference.inheritedRead? mol ops
                            (pullback σ geom) [] node under r with
                        | none => simpa using fallbackEq
                        | some value => rfl

/-! ## Geometry congruence below a node -/

/-- Readback agreement of two geometries on every list built from a frame of a node in `P`. -/
def AgreeOn (P : Node → Prop) (mol : RawMolecule) (first second : Geometry) : Prop :=
  ∀ node, P node → ∀ atoms, frameAtoms? mol node = some atoms →
    ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) → readback? first L = readback? second L

theorem AgreeOn.mirror {P : Node → Prop} {first second : Geometry}
    (agree : AgreeOn P mol first second) : AgreeOn P mol (mirror first) (mirror second) := by
  intro node hP atoms frame L sub
  rw [readback_mirror, readback_mirror, agree node hP atoms frame L sub]

/-- A step depends on the geometry only through readings of lists drawn from the frame. -/
def StepCongr (step : Step) (mol : RawMolecule) (ops : Operations) : Prop :=
  ∀ (first second : Geometry) (node : Node),
    (∀ atoms, frameAtoms? mol node = some atoms →
      ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) → readback? first L = readback? second L) →
    ∀ state ctx under, step mol ops first state ctx node under = step mol ops second state ctx node under

theorem factsWith_congr (step : Step) (P : Node → Prop)
    (closed : ∀ parent child, P parent → child ∈ mol.canonicalChildren parent → P child)
    (stepCongr : StepCongr step mol ops) :
    ∀ depth (first second : Geometry), AgreeOn P mol first second →
      ∀ (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node), P node →
        factsWith step mol ops depth first state ctx node =
          factsWith step mol ops depth second state ctx node := by
  intro depth
  induction depth with
  | zero => intros; rfl
  | succ depth ih =>
      intro first second agree state ctx node hP
      have under : ∀ (f s : Geometry), AgreeOn P mol f s →
          underWith mol ops f state node (factsWith step mol ops depth) =
            underWith mol ops s state node (factsWith step mol ops depth) := by
        intro f s agreeFS
        funext r
        unfold underWith
        exact flatMap_congr_mem _ _ _ fun child member =>
          ih f s agreeFS state (some r) child
            (closed node child hP (mem_tiedChildren_actual mol ops state node child member))
      have head : descriptorWith step mol ops depth first state ctx node =
          descriptorWith step mol ops depth second state ctx node := by
        unfold descriptorWith
        rw [under first second agree, under (mirror first) (mirror second) agree.mirror,
          stepCongr first second node (agree node hP) state ctx,
          stepCongr (mirror first) (mirror second) node (agree.mirror node hP) state ctx]
      rw [factsWith_succ, factsWith_succ, head]
      congr 1
      exact flatMap_congr_mem _ _ _ fun child member =>
        ih first second agree state ctx child (closed node child hP member)

theorem markedReading_congr_geom (first second : Geometry) (node : Node) (atoms : List Nat)
    (frame : frameAtoms? mol node = some atoms)
    (key : ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) → readback? first L = readback? second L)
    (state : OccurrenceAuxState) (r : Nat) :
    markedReading? mol ops first state node r = markedReading? mol ops second state node r := by
  unfold markedReading?
  rw [frame]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases ops.marked state node r with
  | none => rfl
  | some ranking =>
      simp only [Option.bind_some]
      cases h : rankedAtoms? atoms ranking with
      | none => rfl
      | some ranked => exact key ranked (rankedAtoms_subset atoms ranking ranked h)

theorem rawStep_congr_geom : StepCongr LocalizedMarkedOperationEvaluator.rawStep? mol ops := by
  intro first second node agree state ctx under
  cases frame : frameAtoms? mol node with
  | none => simp [LocalizedMarkedOperationEvaluator.rawStep?, frame]
  | some atoms =>
      have key := agree atoms frame
      have marked : ∀ temp r, markedReading? mol ops first temp node r =
          markedReading? mol ops second temp node r :=
        fun temp r => markedReading_congr_geom first second node atoms frame key temp r
      unfold LocalizedMarkedOperationEvaluator.rawStep?
      rw [frame]
      cases ops.ordinary state node with
      | none => rfl
      | some result =>
          obtain ⟨sorted, adjacent⟩ := result
          simp only [Option.bind_eq_bind, Option.bind_some]
          split_ifs
          · rfl
          · cases h : atomsAt? atoms sorted with
            | none => rfl
            | some ranked =>
                simp only [Option.bind_some]
                exact key ranked (atomsAt_subset atoms sorted ranked h)
          · simp only [marked]

theorem distantStep_congr_geom :
    StepCongr LocalizedPhysicalMarkedDistantReference.rawStep? mol ops := by
  intro first second node agree state ctx under
  cases frame : frameAtoms? mol node with
  | none => simp [LocalizedPhysicalMarkedDistantReference.rawStep?, frame]
  | some atoms =>
      have key := agree atoms frame
      have marked : ∀ temp r, markedReading? mol ops first temp node r =
          markedReading? mol ops second temp node r :=
        fun temp r => markedReading_congr_geom first second node atoms frame key temp r
      have reading : LocalizedPhysicalMarkedDistantReference.inheritedRead? mol ops first state
          node under = LocalizedPhysicalMarkedDistantReference.inheritedRead? mol ops second state
            node under := by
        funext r
        unfold LocalizedPhysicalMarkedDistantReference.inheritedRead?
        simp only [marked]
      unfold LocalizedPhysicalMarkedDistantReference.rawStep?
      rw [frame]
      cases ops.ordinary state node with
      | none => rfl
      | some result =>
          obtain ⟨sorted, adjacent⟩ := result
          simp only [Option.bind_eq_bind, Option.bind_some]
          split_ifs
          · rfl
          · cases h : atomsAt? atoms sorted with
            | none => rfl
            | some ranked =>
                simp only [Option.bind_some]
                exact key ranked (atomsAt_subset atoms sorted ranked h)
          · rw [reading]

/-! ## Consequences at a fixed centre with an exchanged frame pair -/

/-- Occurrences strictly below a root occurrence. -/
def Below (mol : RawMolecule) (root node : Node) : Prop :=
  ∃ child ∈ mol.canonicalChildren root,
    Relation.ReflTransGen (fun parent child => child ∈ mol.canonicalChildren parent) child node

theorem below_child (root parent child : Node) (h : Below mol root parent)
    (edge : child ∈ mol.canonicalChildren parent) : Below mol root child := by
  obtain ⟨c, hc, path⟩ := h
  exact ⟨c, hc, path.tail edge⟩

theorem below_of_child (root child : Node) (edge : child ∈ mol.canonicalChildren root) :
    Below mol root child := ⟨child, edge, .refl⟩

/-- Data of a centre fixed by the symmetry whose frame is exchanged by one transposition. -/
structure ExchangedCentre (mol : RawMolecule) (σ : Nat → Nat) (center : Nat) (atoms : List Nat)
    (a b : Nat) : Prop where
  valid : center < mol.atomCount
  fixed : σ center = center
  frame : frameAtoms? mol (canonicalCenterRoot center) = some atoms
  ne : a ≠ b
  left : a ∈ atoms
  right : b ∈ atoms
  swap : ∀ x ∈ atoms, σ x = swapAtom a b x

section Root

variable (step : Step) (sym : StructuralSymmetry mol σ) (wellFormed : mol.WellFormed)
  (unique : mol.BondRecordsUnique) (single : SingleBonded mol) (cov : Covariant mol ops σ)
  (stepMap : StepMap step mol ops σ) (stepCongr : StepCongr step mol ops)
  {center : Nat} {atoms : List Nat} {a b : Nat} (centre : ExchangedCentre mol σ center atoms a b)

include cov centre in
/-- At the fixed centre the strict ordinary order cannot read: it would have to equal its own
relabelling, which moves a frame atom. -/
theorem root_strict_none (sorted : List Nat) (adjacent : List (Option Ordering))
    (ordered : ops.ordinary [] (canonicalCenterRoot center) = some (sorted, adjacent))
    (strictH : strict adjacent = true) (geom : Geometry) :
    (atomsAt? atoms sorted).bind (readback? geom) = none := by
  have rootFixed : mapNode σ (canonicalCenterRoot center) = canonicalCenterRoot center := by
    rw [mapNode_canonicalCenterRoot, centre.fixed]
  have rel := cov.ordinary (canonicalCenterRoot center) (reached_root mol center centre.valid)
    atoms atoms centre.frame (by rw [rootFixed]; exact centre.frame)
  rw [rootFixed, ordered, ordinaryRel_some_some] at rel
  obtain ⟨_, _, atomsAtEq, _⟩ := rel
  have atomsAtEq := atomsAtEq strictH
  have four := frame_length mol _ atoms centre.frame
  cases h : atomsAt? atoms sorted with
  | none => rfl
  | some ranked =>
      rw [h, Option.map_some, Option.some.injEq] at atomsAtEq
      rw [Option.bind_some]
      have complement := readback_transposition geom atoms four a b centre.ne centre.left
        centre.right σ centre.swap ranked (atomsAt_subset atoms sorted ranked h)
      rw [← atomsAtEq] at complement
      cases hr : readback? geom ranked with
      | none => rfl
      | some v =>
          rw [hr] at complement
          cases v <;> simp [RS.swap] at complement

include sym wellFormed unique single cov stepMap stepCongr centre

/-- The reference evaluation at the fixed centre under the exchanged reference is the complement
of the evaluation under the original reference, with the child data taken under any geometry
`g'` that reads like the pulled-back geometry below the centre. -/
theorem root_evaluate (geom g' : Geometry)
    (agree : AgreeOn (Below mol (canonicalCenterRoot center)) mol (pullback σ geom) g')
    (depth : Nat) (r : Nat) :
    ((appendFacts? [] (underWith mol ops geom [] (canonicalCenterRoot center)
        (factsWith step mol ops depth) (σ r))).bind fun temp =>
          markedReading? mol ops geom temp (canonicalCenterRoot center) (σ r)) =
      (((appendFacts? [] (underWith mol ops g' [] (canonicalCenterRoot center)
        (factsWith step mol ops depth) r)).bind fun temp =>
          markedReading? mol ops geom temp (canonicalCenterRoot center) r)).map RS.swap := by
  have rootFixed : mapNode σ (canonicalCenterRoot center) = canonicalCenterRoot center := by
    rw [mapNode_canonicalCenterRoot, centre.fixed]
  have reachedRoot := reached_root mol center centre.valid
  have underPerm : (underWith mol ops geom [] (canonicalCenterRoot center)
      (factsWith step mol ops depth) (σ r)).Perm
        ((underWith mol ops g' [] (canonicalCenterRoot center) (factsWith step mol ops depth) r).map
          (mapFact σ)) := by
    have transport := underWith_map step sym wellFormed unique single cov stepMap depth geom
      (canonicalCenterRoot center) reachedRoot r
    rw [rootFixed] at transport
    refine transport.trans (List.Perm.of_eq ?_)
    congr 1
    unfold underWith
    exact flatMap_congr_mem _ _ _ fun child member =>
      factsWith_congr step (Below mol (canonicalCenterRoot center))
        (below_child (canonicalCenterRoot center)) stepCongr depth _ _ agree [] (some r) child
        (below_of_child (canonicalCenterRoot center) child
          (mem_tiedChildren_actual mol ops [] _ child member))
  have four := frame_length mol _ atoms centre.frame
  rw [appendFacts_nil_eq, appendFacts_nil_eq]
  by_cases nodup : ((underWith mol ops g' [] (canonicalCenterRoot center)
      (factsWith step mol ops depth) r).map (·.key)).Nodup
  · rw [if_pos ((keys_nodup_iff sym underPerm).mpr nodup), if_pos nodup, Option.bind_some,
      Option.bind_some]
    have h := cov.marked (canonicalCenterRoot center) reachedRoot atoms atoms centre.frame
      (by rw [rootFixed]; exact centre.frame) _ _ underPerm nodup r
    rw [rootFixed] at h
    unfold markedReading?
    rw [centre.frame]
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases hm' : ops.marked (underWith mol ops geom [] (canonicalCenterRoot center)
        (factsWith step mol ops depth) (σ r)) (canonicalCenterRoot center) (σ r) with
    | none =>
        rw [hm', Option.bind_none] at h
        cases hm : ops.marked (underWith mol ops g' [] (canonicalCenterRoot center)
            (factsWith step mol ops depth) r) (canonicalCenterRoot center) r with
        | none => rfl
        | some ranking =>
            rw [hm, Option.bind_some] at h
            simp only [Option.bind_none, Option.bind_some]
            cases hr : rankedAtoms? atoms ranking with
            | none => rfl
            | some ranked => rw [hr] at h; cases h
    | some ranking' =>
        rw [hm', Option.bind_some] at h
        cases hm : ops.marked (underWith mol ops g' [] (canonicalCenterRoot center)
            (factsWith step mol ops depth) r) (canonicalCenterRoot center) r with
        | none =>
            rw [hm, Option.bind_none, Option.map_none] at h
            simp only [Option.bind_some, Option.bind_none, Option.map_none, h]
        | some ranking =>
            rw [hm, Option.bind_some] at h
            simp only [Option.bind_some]
            cases hr : rankedAtoms? atoms ranking with
            | none => rw [hr, Option.map_none] at h; rw [h]; rfl
            | some ranked =>
                rw [hr, Option.map_some] at h
                rw [h, Option.bind_some, Option.bind_some]
                exact readback_transposition geom atoms four a b centre.ne centre.left centre.right
                  σ centre.swap ranked (rankedAtoms_subset atoms ranking ranked hr)
  · rw [if_neg (fun h => nodup ((keys_nodup_iff sym underPerm).mp h)), if_neg nodup]
    rfl

/-- **Refusal under a proper branch symmetry.** -/
theorem root_refuses (geom : Geometry)
    (agree : AgreeOn (Below mol (canonicalCenterRoot center)) mol (pullback σ geom) geom)
    (rootStep : ∀ (g : Geometry) under, step mol ops g [] none (canonicalCenterRoot center) under =
      LocalizedMarkedOperationEvaluator.rawStep? mol ops g [] none (canonicalCenterRoot center) under)
    (depth : Nat) :
    descriptorWith step mol ops depth geom [] none (canonicalCenterRoot center) = none := by
  have rootFixed : mapNode σ (canonicalCenterRoot center) = canonicalCenterRoot center := by
    rw [mapNode_canonicalCenterRoot, centre.fixed]
  unfold descriptorWith
  suffices raw : step mol ops geom [] none (canonicalCenterRoot center)
      (underWith mol ops geom [] (canonicalCenterRoot center) (factsWith step mol ops depth)) =
        none by
    rw [raw]
    rfl
  rw [rootStep]
  unfold LocalizedMarkedOperationEvaluator.rawStep?
  rw [centre.frame]
  cases hord : ops.ordinary [] (canonicalCenterRoot center) with
  | none => rfl
  | some result =>
      obtain ⟨sorted, adjacent⟩ := result
      have rel := cov.ordinary (canonicalCenterRoot center) (reached_root mol center centre.valid)
        atoms atoms centre.frame (by rw [rootFixed]; exact centre.frame)
      rw [rootFixed, hord, ordinaryRel_some_some] at rel
      obtain ⟨_, _, _, eligiblePerm⟩ := rel
      simp only [Option.bind_eq_bind, Option.bind_some]
      split_ifs with bad strictH
      · rfl
      · exact root_strict_none cov centre sorted adjacent hord strictH geom
      · cases hc : consensus ((eligibleOf atoms sorted adjacent).map fun r =>
            (appendFacts? [] (underWith mol ops geom [] (canonicalCenterRoot center)
              (factsWith step mol ops depth) r)).bind fun temp =>
                markedReading? mol ops geom temp (canonicalCenterRoot center) r) with
        | none => rfl
        | some v =>
            exfalso
            have all := consensus_some hc
            cases heq : eligibleOf atoms sorted adjacent with
            | nil => rw [heq] at hc; simp [consensus] at hc
            | cons r rest =>
                have hr : r ∈ eligibleOf atoms sorted adjacent := by rw [heq]; exact List.mem_cons_self
                have hσr : σ r ∈ eligibleOf atoms sorted adjacent :=
                  eligiblePerm.mem_iff.mpr (List.mem_map_of_mem hr)
                have readR := all _ (List.mem_map_of_mem hr)
                have readSr := all _ (List.mem_map_of_mem hσr)
                have complement := root_evaluate step sym wellFormed unique single cov stepMap
                  stepCongr centre geom geom agree depth r
                simp only at readR readSr
                rw [readSr, readR] at complement
                cases v <;> simp [RS.swap] at complement

/-- **Reading invariance under a mirror branch symmetry**: the raw reading equals the raw reading
on the reflected geometry. -/
theorem root_mirror_invariant (geom : Geometry)
    (agree : AgreeOn (Below mol (canonicalCenterRoot center)) mol (pullback σ geom) (mirror geom))
    (rootStep : ∀ (g : Geometry) under, step mol ops g [] none (canonicalCenterRoot center) under =
      LocalizedMarkedOperationEvaluator.rawStep? mol ops g [] none (canonicalCenterRoot center) under)
    (depth : Nat) :
    step mol ops geom [] none (canonicalCenterRoot center)
        (underWith mol ops geom [] (canonicalCenterRoot center) (factsWith step mol ops depth)) =
      step mol ops (mirror geom) [] none (canonicalCenterRoot center)
        (underWith mol ops (mirror geom) [] (canonicalCenterRoot center)
          (factsWith step mol ops depth)) := by
  have rootFixed : mapNode σ (canonicalCenterRoot center) = canonicalCenterRoot center := by
    rw [mapNode_canonicalCenterRoot, centre.fixed]
  rw [rootStep, rootStep]
  unfold LocalizedMarkedOperationEvaluator.rawStep?
  rw [centre.frame]
  cases hord : ops.ordinary [] (canonicalCenterRoot center) with
  | none => rfl
  | some result =>
      obtain ⟨sorted, adjacent⟩ := result
      have rel := cov.ordinary (canonicalCenterRoot center) (reached_root mol center centre.valid)
        atoms atoms centre.frame (by rw [rootFixed]; exact centre.frame)
      rw [rootFixed, hord, ordinaryRel_some_some] at rel
      obtain ⟨_, _, _, eligiblePerm⟩ := rel
      simp only [Option.bind_eq_bind, Option.bind_some]
      split_ifs with bad strictH
      · rfl
      · rw [root_strict_none cov centre sorted adjacent hord strictH geom,
          root_strict_none cov centre sorted adjacent hord strictH (mirror geom)]
      · have evaluate : ∀ r,
            ((appendFacts? [] (underWith mol ops geom [] (canonicalCenterRoot center)
              (factsWith step mol ops depth) (σ r))).bind fun temp =>
                markedReading? mol ops geom temp (canonicalCenterRoot center) (σ r)) =
            ((appendFacts? [] (underWith mol ops (mirror geom) [] (canonicalCenterRoot center)
              (factsWith step mol ops depth) r)).bind fun temp =>
                markedReading? mol ops (mirror geom) temp (canonicalCenterRoot center) r) := by
          intro r
          rw [root_evaluate step sym wellFormed unique single cov stepMap stepCongr centre geom
            (mirror geom) agree depth r]
          cases appendFacts? [] (underWith mol ops (mirror geom) [] (canonicalCenterRoot center)
              (factsWith step mol ops depth) r) with
          | none => rfl
          | some temp =>
              rw [Option.bind_some, Option.bind_some, markedReading_mirror]
        rw [consensus_perm (eligiblePerm.map _), List.map_map]
        congr 1
        apply List.map_congr_left
        intro r _
        exact evaluate r

/-- **No uppercase descriptor under a mirror branch symmetry.** -/
theorem root_not_chiral (geom : Geometry)
    (agree : AgreeOn (Below mol (canonicalCenterRoot center)) mol (pullback σ geom) (mirror geom))
    (rootStep : ∀ (g : Geometry) under, step mol ops g [] none (canonicalCenterRoot center) under =
      LocalizedMarkedOperationEvaluator.rawStep? mol ops g [] none (canonicalCenterRoot center) under)
    (depth : Nat) (v : RS) :
    descriptorWith step mol ops depth geom [] none (canonicalCenterRoot center) ≠
      some (.chiral v) := by
  unfold descriptorWith
  rw [root_mirror_invariant step sym wellFormed unique single cov stepMap stepCongr centre geom agree
    rootStep depth]
  cases step mol ops (mirror geom) [] none (canonicalCenterRoot center)
      (underWith mol ops (mirror geom) [] (canonicalCenterRoot center)
        (factsWith step mol ops depth)) with
  | none => simp [caseFromMirror?]
  | some w => simp [caseFromMirror?]

end Root

/-! ## Instances for the two evaluators -/

section Instances

variable (sym : StructuralSymmetry mol σ) (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
  (single : SingleBonded mol) (cov : Covariant mol ops σ)
  {center : Nat} {atoms : List Nat} {a b : Nat} (centre : ExchangedCentre mol σ center atoms a b)
  (geom : Geometry)

include sym wellFormed unique single cov centre

/-- The existing evaluator refuses a centre fixed by a proper branch symmetry exchanging two
frame atoms. -/
theorem assignCenter_none_of_proper
    (agree : AgreeOn (Below mol (canonicalCenterRoot center)) mol (pullback σ geom) geom) :
    LocalizedMarkedOperationEvaluator.assignCenter? mol ops geom center = none := by
  unfold LocalizedMarkedOperationEvaluator.assignCenter?
  rw [descriptor_eq_descriptorWith]
  exact root_refuses _ sym wellFormed unique single cov (rawStep_map sym wellFormed unique single cov)
    rawStep_congr_geom centre geom agree (fun _ _ => rfl) _

/-- The existing evaluator never emits an uppercase descriptor at a centre fixed by a mirror
branch symmetry exchanging two frame atoms. -/
theorem assignCenter_not_chiral_of_mirror
    (agree : AgreeOn (Below mol (canonicalCenterRoot center)) mol (pullback σ geom) (mirror geom))
    (v : RS) :
    LocalizedMarkedOperationEvaluator.assignCenter? mol ops geom center ≠ some (.chiral v) := by
  unfold LocalizedMarkedOperationEvaluator.assignCenter?
  rw [descriptor_eq_descriptorWith]
  exact root_not_chiral _ sym wellFormed unique single cov
    (rawStep_map sym wellFormed unique single cov) rawStep_congr_geom centre geom agree
    (fun _ _ => rfl) _ v

/-- The distant-reference successor refuses the same centres. -/
theorem distant_assignCenter_none_of_proper
    (agree : AgreeOn (Below mol (canonicalCenterRoot center)) mol (pullback σ geom) geom) :
    LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol ops geom center = none := by
  unfold LocalizedPhysicalMarkedDistantEvaluator.assignCenter?
  rw [distant_descriptor_eq_descriptorWith]
  exact root_refuses _ sym wellFormed unique single cov
    (distantStep_map sym wellFormed unique single cov) distantStep_congr_geom centre geom agree
    (fun g under => LocalizedPhysicalMarkedDistantReference.rawStep_none mol ops g [] _ under) _

theorem distant_assignCenter_not_chiral_of_mirror
    (agree : AgreeOn (Below mol (canonicalCenterRoot center)) mol (pullback σ geom) (mirror geom))
    (v : RS) :
    LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol ops geom center ≠ some (.chiral v) := by
  unfold LocalizedPhysicalMarkedDistantEvaluator.assignCenter?
  rw [distant_descriptor_eq_descriptorWith]
  exact root_not_chiral _ sym wellFormed unique single cov
    (distantStep_map sym wellFormed unique single cov) distantStep_congr_geom centre geom agree
    (fun g under => LocalizedPhysicalMarkedDistantReference.rawStep_none mol ops g [] _ under) _ v

end Instances

end Transport

end TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.facts_eq_factsWith
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.distant_facts_eq_factsWith
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.consensus_eq_some_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.consensus_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.appendFacts_eq_ite
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.readback_transposition
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.markedReading_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.tiedChildren_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.factsWith_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.rawStep_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.distantStep_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.factsWith_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.rawStep_congr_geom
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.distantStep_congr_geom
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.root_evaluate
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.root_refuses
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.root_mirror_invariant
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.root_not_chiral
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.assignCenter_none_of_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.assignCenter_not_chiral_of_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.distant_assignCenter_none_of_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport.distant_assignCenter_not_chiral_of_mirror
