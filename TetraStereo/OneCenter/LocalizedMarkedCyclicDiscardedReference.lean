import TetraStereo.OneCenter.LocalizedMarkedOperationEvaluator
import TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeSwap
import TetraStereo.OneCenter.LocalizedMarkedReachableConfigurations
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Discarded inherited references force refusal on the subdivided cage, for every ranker

The marked evaluator carries a reference atom to a descendant occurrence only when that atom is
one of the descendant's four frame atoms (`LocalizedMarkedInheritedReferenceScope`). This module
derives the consequence for **every** operations record that satisfies the constitutional
covariance of priority with no auxiliary facts (`EmptyStateCovariant`): an involutive molecular
automorphism fixing an occurrence maps the tied status of moved frame atoms to itself, and maps
the atom priority order returned for reference `r` to the order returned for reference `σ r`.
This is a necessary property of any priority computed from constitution; geometry is not an input
of the operations, only of the readback.

On a certified tree region (`goodB`), where every framed occurrence has such a frame
transposition and no frame atom of an occurrence reappears in a frame below it, the two references
exchanged by the transposition read complementary letters, every consensus fails, no auxiliary
fact is ever generated and the evaluated centre is refused, for every geometry.

The subdivided cage (each bridge of the accepted hidden-parity cage subdivided once by an oxygen)
is certified at centre `0` (`cage_good`, kernel decision). Hence every covariant ranker refuses
centre `0` under every geometry (`refuses`). The coordinate checks of
`LocalizedMarkedSubdividedCagePhysicalProbe` (executable diagnostics of the verified transport
decision procedure, not kernel proofs) report that cage A and cage B at centre `0` are neither
proper- nor mirror-related for the source coordinates, so centre `0` is physically stereogenic
there. Kernel-checking those physical decisions is open here.

Control: the unsubdivided 15-atom cage is NOT certified (`unsubdivided_not_certified`): its near
bridgehead marks lie in the far bridgehead frames, the route by which the accepted 15-atom
readback recovers the bridgehead parity.

Scope: an obstruction for the current immediate-frame inherited-reference policy, uniformly over
comparators. Whether the experimental retained-promoted operations satisfy `EmptyStateCovariant`
is not proved here. No successor policy is defined or endorsed here.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedCyclicDiscardedReference

open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? readback? strict consistent
  eligibleOf tiedPositions atomsAt rankedAtoms? consensus appendFacts? caseFromMirror? mirror
  structuralDepth)
open LocalizedMarkedOperationEvaluator
open LocalizedMarkedTerminalGaugeSwap (swapAtom readback_swapAtom readback4 mapM_getElem?_forall₂
  forall₂_mem_right)
open LocalizedMarkedReachableConfigurations (Reached reached_root reached_child)

abbrev RawNode := RawMolecule.CanonicalBranchNode

/-! ## Constitutional symmetry and covariance -/

/-- An involutive relabelling of atom identifiers preserving every in-range atom specification
and bond order. -/
def IsAutomorphism (mol : RawMolecule) (σ : Nat → Nat) : Prop :=
  Function.Involutive σ ∧ ∀ x < mol.atomCount, σ x < mol.atomCount ∧
    mol.atomAt? (σ x) = mol.atomAt? x ∧
    ∀ y < mol.atomCount, mol.bondOrder (σ x) (σ y) = mol.bondOrder x y

/-- The relabelling fixes the occurrence: every atom of its history. -/
def Fixes (σ : Nat → Nat) (node : RawNode) : Prop := ∀ x ∈ node.history, σ x = x

/-- **Constitutional covariance with no auxiliary facts**, at occurrences reached from an
in-range centre. For an automorphism fixing such an occurrence: frame atoms moved by it stand in
tied runs of the ordinary order, and the atom priority order returned for reference `σ r` is the
`σ`-image of the order returned for `r`. Nothing is required at fabricated histories. -/
def EmptyStateCovariant (mol : RawMolecule) (ops : Operations) : Prop :=
  ∀ σ, IsAutomorphism mol σ → ∀ (node : RawNode) (atoms : List Nat), Reached mol node →
    Fixes σ node → frameAtoms? mol node = some atoms →
      (∀ sorted adjacent, ops.ordinary [] node = some (sorted, adjacent) →
          consistent adjacent = true →
          ∀ x ∈ atoms, σ x ≠ x → x ∈ eligibleOf atoms sorted adjacent) ∧
      (∀ r ranking ranked, ops.marked [] node r = some ranking →
          rankedAtoms? atoms ranking = some ranked →
          ∃ ranking', ops.marked [] node (σ r) = some ranking' ∧
            rankedAtoms? atoms ranking' = some (ranked.map σ))

/-! ## Generic evaluator facts -/

theorem tiedPositions_of_strict : ∀ (sorted : List Nat) (adjacent : List (Option Ordering)),
    strict adjacent = true → tiedPositions false sorted adjacent = []
  | [], _, _ => by simp [tiedPositions]
  | [_], _, _ => by simp [tiedPositions]
  | _ :: q :: rest, [], _ => by
      simp only [tiedPositions, Bool.false_eq_true, ↓reduceIte, List.nil_append]
      exact tiedPositions_of_strict (q :: rest) [] rfl
  | _ :: q :: rest, d :: ds, h => by
      simp only [strict, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, tail⟩ := h
      have tie : (some Ordering.gt == some Ordering.eq) = false := by decide
      simp only [tiedPositions, tie, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        List.nil_append]
      exact tiedPositions_of_strict (q :: rest) ds tail

theorem eligibleOf_of_strict (atoms sorted : List Nat) (adjacent : List (Option Ordering))
    (h : strict adjacent = true) : eligibleOf atoms sorted adjacent = [] := by
  simp [eligibleOf, tiedPositions_of_strict sorted adjacent h, atomsAt]

private theorem consensus_cons_cons (x y : Option RS) (rest : List (Option RS)) :
    consensus (x :: y :: rest) =
      match x, consensus (y :: rest) with
      | some a, some b => if a = b then some a else none
      | _, _ => none := rfl

theorem consensus_some : ∀ {results : List (Option RS)} {v : RS}, consensus results = some v →
    ∀ e ∈ results, e = some v
  | [], _, h => by simp [consensus] at h
  | [x], _, h => by
      intro e he
      simp only [List.mem_singleton] at he
      rw [he]
      exact h
  | x :: y :: rest, v, h => by
      intro e he
      rw [consensus_cons_cons] at h
      rcases x with _ | a
      · simp at h
      · cases hc : consensus (y :: rest) with
        | none => rw [hc] at h; simp at h
        | some b =>
            rw [hc] at h
            simp only at h
            split_ifs at h with hab
            cases h
            rcases List.mem_cons.mp he with rfl | tail
            · rfl
            · rw [consensus_some hc e tail, hab]

private theorem points_length : ∀ (points : List CartesianPoint3) (v : RS),
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? points = some v →
      points.length = 4
  | [_, _, _, _], _, _ => rfl
  | [], _, h => by simp [CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?] at h
  | [_], _, h => by simp [CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?] at h
  | [_, _], _, h => by simp [CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?] at h
  | [_, _, _], _, h => by simp [CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?] at h
  | _ :: _ :: _ :: _ :: _ :: _, _, h => by
      simp [CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?] at h

private theorem mapM_length (geom : Geometry) : ∀ (l : List Nat) (points : List CartesianPoint3),
    l.mapM geom = some points → l.length = points.length
  | [], points, h => by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h
      rfl
  | x :: xs, points, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨p, _, ps, hps, rfl⟩ := h
      simp [mapM_length geom xs ps hps]

theorem readback_length (geom : Geometry) (l : List Nat) (v : RS)
    (h : readback? geom l = some v) : l.length = 4 := by
  simp only [readback?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨points, hpoints, hv⟩ := h
  rw [mapM_length geom l points hpoints]
  exact points_length points v hv

open CartesianPoint3 in
theorem readback_nodup (geom : Geometry) (a b c d : Nat) (v : RS)
    (h : readback? geom [a, b, c, d] = some v) : [a, b, c, d].Nodup := by
  rw [readback4] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨pa, ha, pb, hb, pc, hc, pd, hd, h⟩ := h
  have nonzero : orientedVolume pa pb pc pd ≠ 0 := by
    intro zero
    rw [zero] at h
    simp [CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?] at h
  have ab : a ≠ b := by
    intro same; subst same; rw [ha] at hb; cases hb
    exact nonzero (by simp only [orientedVolume]; ring)
  have ac : a ≠ c := by
    intro same; subst same; rw [ha] at hc; cases hc
    exact nonzero (by simp only [orientedVolume]; ring)
  have ad : a ≠ d := by
    intro same; subst same; rw [ha] at hd; cases hd
    exact nonzero (by simp only [orientedVolume]; ring)
  have bc : b ≠ c := by
    intro same; subst same; rw [hb] at hc; cases hc
    exact nonzero (by simp only [orientedVolume]; ring)
  have bd : b ≠ d := by
    intro same; subst same; rw [hb] at hd; cases hd
    exact nonzero (by simp only [orientedVolume]; ring)
  have cd : c ≠ d := by
    intro same; subst same; rw [hc] at hd; cases hd
    exact nonzero (by simp only [orientedVolume]; ring)
  simp [ab, ac, ad, bc, bd, cd]

theorem rankedAtoms_subset (atoms : List Nat) (ranking : Rule6TrackedRanking) (ranked : List Nat)
    (h : rankedAtoms? atoms ranking = some ranked) : ∀ x ∈ ranked, x ∈ atoms := by
  intro x member
  unfold rankedAtoms? at h
  split_ifs at h
  obtain ⟨p, _, hp⟩ := forall₂_mem_right (mapM_getElem?_forall₂ atoms _ ranked h) x member
  exact List.mem_of_getElem? hp

/-! ## One frame transposition: complementary readings and a failed consensus -/

section Frame

variable {mol : RawMolecule} {ops : Operations}

/-- Two readings under references exchanged by a frame transposition are complements. -/
theorem marked_pair_complement (cov : EmptyStateCovariant mol ops) (σ : Nat → Nat)
    (aut : IsAutomorphism mol σ) (node : RawNode) (atoms : List Nat) (reached : Reached mol node)
    (fixes : Fixes σ node)
    (frame : frameAtoms? mol node = some atoms) (length : atoms.length = 4)
    (a : Nat) (ha : a ∈ atoms) (moved : σ a ≠ a) (closed : σ a ∈ atoms)
    (only : ∀ x ∈ atoms, σ x ≠ x → x = a ∨ x = σ a)
    (geom : Geometry) (v w : RS)
    (read₁ : markedReading? mol ops geom [] node a = some v)
    (read₂ : markedReading? mol ops geom [] node (σ a) = some w) : w = v.swap := by
  have inv : σ (σ a) = a := aut.1 a
  simp only [markedReading?, frame, Option.bind_eq_bind, Option.bind_some,
    Option.bind_eq_some_iff] at read₁ read₂
  obtain ⟨ranking, hr, ranked, hranked, hread⟩ := read₁
  obtain ⟨ranking', hr', hranked'⟩ := (cov σ aut node atoms reached fixes frame).2 a ranking
    ranked hr hranked
  obtain ⟨r₂, hr₂, ranked₂, hranked₂, hread₂⟩ := read₂
  rw [hr'] at hr₂
  cases hr₂
  rw [hranked'] at hranked₂
  cases hranked₂
  have len : ranked.length = 4 := readback_length geom ranked v hread
  have rankedNodup : ranked.Nodup := by
    match ranked, len with
    | [x₁, x₂, x₃, x₄], _ => exact readback_nodup geom x₁ x₂ x₃ x₄ v hread
  have subset := rankedAtoms_subset atoms ranking ranked hranked
  have perm : ranked.Perm atoms :=
    (rankedNodup.subperm subset).perm_of_length_le (by rw [len, length])
  have aRanked : a ∈ ranked := perm.mem_iff.mpr ha
  have bRanked : σ a ∈ ranked := perm.mem_iff.mpr closed
  have mapEq : ranked.map σ = ranked.map (swapAtom a (σ a)) := by
    apply List.map_congr_left
    intro x member
    by_cases fixed : σ x = x
    · have neA : x ≠ a := fun same => moved (same ▸ fixed)
      have neB : x ≠ σ a := by
        intro same
        apply moved
        calc σ a = x := same.symm
          _ = σ x := fixed.symm
          _ = σ (σ a) := by rw [same]
          _ = a := inv
      simp [swapAtom, neA, neB, fixed]
    · rcases only x (subset x member) fixed with rfl | rfl
      · simp [swapAtom]
      · simp [swapAtom, inv, moved]
  have complement := readback_swapAtom geom a (σ a) (fun same => moved same.symm) ranked
    rankedNodup len aRanked bRanked
  rw [← mapEq, hread₂, hread] at complement
  exact Option.some.inj complement

/-- **One occurrence refuses** when its frame has a covariant transposition, the carried context
(if any) is not a frame atom, and every reference hypothesis contributes no auxiliary fact. -/
theorem rawStep_none (cov : EmptyStateCovariant mol ops) (σ : Nat → Nat)
    (aut : IsAutomorphism mol σ) (node : RawNode) (atoms : List Nat) (reached : Reached mol node)
    (fixes : Fixes σ node)
    (frame : frameAtoms? mol node = some atoms) (length : atoms.length = 4)
    (a : Nat) (ha : a ∈ atoms) (moved : σ a ≠ a) (closed : σ a ∈ atoms)
    (only : ∀ x ∈ atoms, σ x ≠ x → x = a ∨ x = σ a)
    (geom : Geometry) (ctx : Option Nat) (ctxOk : ∀ r, ctx = some r → r ∉ atoms)
    (under : Nat → OccurrenceAuxState) (empty : ∀ r ∈ atoms, under r = []) :
    rawStep? mol ops geom [] ctx node under = none := by
  have inv : σ (σ a) = a := aut.1 a
  have movedB : σ (σ a) ≠ σ a := by rw [inv]; exact fun same => moved same.symm
  have key : ∀ (sorted : List Nat) (adjacent : List (Option Ordering)),
      ops.ordinary [] node = some (sorted, adjacent) → consistent adjacent = true →
      ∀ f : Nat → Option RS, (∀ r ∈ atoms, f r = markedReading? mol ops geom [] node r) →
        consensus ((eligibleOf atoms sorted adjacent).map f) = none := by
    intro sorted adjacent hord hcons f hf
    have tie := (cov σ aut node atoms reached fixes frame).1 sorted adjacent hord hcons
    cases hc : consensus ((eligibleOf atoms sorted adjacent).map f) with
    | none => rfl
    | some v =>
        have all := consensus_some hc
        have readA := all (f a) (List.mem_map_of_mem (tie a ha moved))
        have readB := all (f (σ a)) (List.mem_map_of_mem (tie (σ a) closed movedB))
        rw [hf a ha] at readA
        rw [hf (σ a) closed] at readB
        have := marked_pair_complement cov σ aut node atoms reached fixes frame length a ha moved
          closed only geom v v readA readB
        cases v <;> simp [RS.swap] at this
  unfold rawStep?
  rw [frame]
  cases hord : ops.ordinary [] node with
  | none => rfl
  | some result =>
      obtain ⟨sorted, adjacent⟩ := result
      simp only [Option.bind_eq_bind, Option.bind_some]
      split_ifs with bad strictH
      · rfl
      · have hcons : consistent adjacent = true := by
          simp only [not_or, not_not, Bool.not_eq_false] at bad
          exact bad.2
        have tie := (cov σ aut node atoms reached fixes frame).1 sorted adjacent hord hcons a ha
          moved
        rw [eligibleOf_of_strict atoms sorted adjacent strictH] at tie
        cases tie
      · have hcons : consistent adjacent = true := by
          simp only [not_or, Bool.not_eq_false] at bad
          exact bad.2
        have evaluate : ∀ r ∈ atoms,
            ((appendFacts? [] (under r)).bind fun temp =>
              markedReading? mol ops geom temp node r) = markedReading? mol ops geom [] node r := by
          intro r hr
          rw [empty r hr]
          rfl
        cases ctx with
        | none => exact key sorted adjacent hord hcons _ evaluate
        | some r =>
            have absent : atoms.contains r = false := by
              simpa using ctxOk r rfl
            simp only [absent, Bool.false_eq_true, ↓reduceIte]
            exact key sorted adjacent hord hcons _ evaluate

end Frame

/-! ## A decidable certificate for a whole evaluation region -/

/-- A finite relabelling from a list of transpositions. -/
def apply : List (Nat × Nat) → Nat → Nat
  | [], x => x
  | (p, q) :: rest, x => if x = p then q else if x = q then p else apply rest x

/-- The relabelling is an automorphism of the molecule (checked on the atom range). -/
def autB (mol : RawMolecule) (pairs : List (Nat × Nat)) : Bool :=
  pairs.all (fun pair => decide (pair.1 < mol.atomCount) && decide (pair.2 < mol.atomCount)) &&
    (List.range mol.atomCount).all fun x =>
      decide (apply pairs (apply pairs x) = x) && decide (apply pairs x < mol.atomCount) &&
        decide (mol.atomAt? (apply pairs x) = mol.atomAt? x) &&
        (List.range mol.atomCount).all fun y =>
          decide (mol.bondOrder (apply pairs x) (apply pairs y) = mol.bondOrder x y)

/-- The relabelling fixes the occurrence and exchanges exactly two of its frame atoms. -/
def symmetricB (pairs : List (Nat × Nat)) (node : RawNode) (atoms : List Nat) : Bool :=
  node.history.all (fun x => decide (apply pairs x = x)) &&
    atoms.any fun a => decide (apply pairs a ≠ a) && atoms.contains (apply pairs a) &&
      atoms.all fun x => decide (apply pairs x = x) || decide (x = a) || decide (x = apply pairs a)

/-- `r` is no frame atom of any framed occurrence of the region below `node`. -/
def absentB (mol : RawMolecule) (r : Nat) : Nat → RawNode → Bool
  | 0, _ => true
  | d + 1, node =>
      (match frameAtoms? mol node with
        | some atoms => !atoms.contains r
        | none => true) &&
      (mol.canonicalChildren node).all (absentB mol r d)

/-- Every framed occurrence of the region has a certified frame transposition, and none of its
frame atoms reappears in a frame below it. -/
def goodB (mol : RawMolecule) (swaps : List (List (Nat × Nat))) : Nat → RawNode → Bool
  | 0, _ => true
  | d + 1, node =>
      (match frameAtoms? mol node with
        | some atoms => decide (atoms.length = 4) &&
            swaps.any (fun pairs => symmetricB pairs node atoms) &&
            atoms.all (fun r => (mol.canonicalChildren node).all (absentB mol r d))
        | none => true) &&
      (mol.canonicalChildren node).all (goodB mol swaps d)

theorem apply_out : ∀ (pairs : List (Nat × Nat)) (x : Nat),
    (∀ pair ∈ pairs, pair.1 ≠ x ∧ pair.2 ≠ x) → apply pairs x = x
  | [], _, _ => rfl
  | (p, q) :: rest, x, h => by
      have head := h (p, q) List.mem_cons_self
      have tail := apply_out rest x fun pair member => h pair (List.mem_cons_of_mem _ member)
      simp only [apply, Ne.symm head.1, Ne.symm head.2, ↓reduceIte, tail]

theorem autB_sound (mol : RawMolecule) (pairs : List (Nat × Nat)) (h : autB mol pairs = true) :
    IsAutomorphism mol (apply pairs) := by
  simp only [autB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨inRange, atomsOk⟩ := h
  have outside : ∀ x, mol.atomCount ≤ x → apply pairs x = x := fun x hx =>
    apply_out pairs x fun pair member => by
      have := inRange pair member
      omega
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · by_cases hx : x < mol.atomCount
    · exact (atomsOk x hx).1.1.1
    · rw [outside x (by omega), outside x (by omega)]
  · obtain ⟨⟨⟨_, lt⟩, atomEq⟩, bonds⟩ := atomsOk x hx
    exact ⟨lt, atomEq, fun y hy => bonds y hy⟩

theorem symmetricB_sound (pairs : List (Nat × Nat)) (node : RawNode) (atoms : List Nat)
    (h : symmetricB pairs node atoms = true) :
    Fixes (apply pairs) node ∧ ∃ a ∈ atoms, apply pairs a ≠ a ∧ apply pairs a ∈ atoms ∧
      ∀ x ∈ atoms, apply pairs x ≠ x → x = a ∨ x = apply pairs a := by
  simp only [symmetricB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq, List.contains_iff_mem, Bool.or_eq_true] at h
  obtain ⟨fixes, a, ha, ⟨moved, closed⟩, only⟩ := h
  refine ⟨fixes, a, ha, moved, closed, fun x hx movedX => ?_⟩
  rcases only x hx with (fixed | same) | same
  · exact absurd fixed movedX
  · exact Or.inl same
  · exact Or.inr same

theorem absentB_frame (mol : RawMolecule) (r d : Nat) (node : RawNode) (atoms : List Nat)
    (h : absentB mol r (d + 1) node = true) (frame : frameAtoms? mol node = some atoms) :
    r ∉ atoms := by
  simp only [absentB, frame, Bool.and_eq_true] at h
  simpa using h.1

theorem absentB_child (mol : RawMolecule) (r d : Nat) (node child : RawNode)
    (h : absentB mol r (d + 1) node = true) (member : child ∈ mol.canonicalChildren node) :
    absentB mol r d child = true := by
  simp only [absentB, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 child member

theorem goodB_child {mol : RawMolecule} (swaps : List (List (Nat × Nat))) (d : Nat)
    (node child : RawNode) (h : goodB mol swaps (d + 1) node = true)
    (member : child ∈ mol.canonicalChildren node) : goodB mol swaps d child = true := by
  simp only [goodB, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 child member

section Region

variable {mol : RawMolecule} {ops : Operations}

/-- The descriptor of a certified framed or unframed occurrence is refused once every child below
contributes no fact under every reference. -/
theorem descriptor_none (cov : EmptyStateCovariant mol ops) (swaps : List (List (Nat × Nat)))
    (auts : ∀ pairs ∈ swaps, autB mol pairs = true) (d : Nat) (geom : Geometry)
    (ctx : Option Nat) (node : RawNode) (reached : Reached mol node)
    (good : goodB mol swaps (d + 1) node = true)
    (ctxOk : ∀ r, ctx = some r → absentB mol r (d + 1) node = true)
    (below : ∀ child ∈ mol.canonicalChildren node, ∀ r,
      goodB mol swaps d child = true → absentB mol r d child = true →
        facts mol ops d geom [] (some r) child = []) :
    descriptor? mol ops d geom [] ctx node = none := by
  unfold descriptor? descriptorWith? rawWith?
  suffices raw : rawStep? mol ops geom [] ctx node
      (underWith mol ops geom [] node (facts mol ops d)) = none by
    rw [raw]
    rfl
  cases frame : frameAtoms? mol node with
  | none =>
      unfold rawStep?
      rw [frame]
      rfl
  | some atoms =>
      have clause := good
      simp only [goodB, frame, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
        List.all_eq_true] at clause
      obtain ⟨⟨⟨length, pairs, member, symmetric⟩, absentBelow⟩, _⟩ := clause
      obtain ⟨fixes, a, ha, moved, closed, only⟩ :=
        symmetricB_sound pairs node atoms symmetric
      refine rawStep_none cov (apply pairs) (autB_sound mol pairs (auts pairs member)) node atoms
        reached fixes frame length a ha moved closed only geom ctx
        (fun r hr => absentB_frame mol r d node atoms (ctxOk r hr) frame) _ ?_
      intro r hr
      unfold underWith
      rw [List.flatMap_eq_nil_iff]
      intro child tied
      have actual := mem_tiedChildren_actual mol ops [] node child tied
      exact below child actual r (goodB_child swaps d node child good actual)
        (absentBelow r hr child actual)

/-- **No auxiliary fact is ever generated** on a certified region, for any covariant ranker. -/
theorem facts_vanish (cov : EmptyStateCovariant mol ops) (swaps : List (List (Nat × Nat)))
    (auts : ∀ pairs ∈ swaps, autB mol pairs = true) :
    ∀ (d : Nat) (geom : Geometry) (ctx : Option Nat) (node : RawNode), Reached mol node →
      goodB mol swaps d node = true → (∀ r, ctx = some r → absentB mol r d node = true) →
        facts mol ops d geom [] ctx node = []
  | 0, _, _, _, _, _, _ => rfl
  | d + 1, geom, ctx, node, reached, good, ctxOk => by
      rw [facts_succ, descriptor_none cov swaps auts d geom ctx node reached good ctxOk
        (fun child member r goodChild absentChild =>
          facts_vanish cov swaps auts d geom (some r) child
            (reached_child mol node child reached member) goodChild
            (fun r' same => by cases same; exact absentChild))]
      simp only [Option.toList_none, List.map_nil, List.nil_append]
      rw [List.flatMap_eq_nil_iff]
      intro child member
      exact facts_vanish cov swaps auts d geom ctx child
        (reached_child mol node child reached member)
        (goodB_child swaps d node child good member)
        (fun r same => absentB_child mol r d node child (ctxOk r same) member)

/-- **Refusal of a certified centre, for every geometry and every covariant ranker.** -/
theorem assignCenter_none (cov : EmptyStateCovariant mol ops) (swaps : List (List (Nat × Nat)))
    (auts : ∀ pairs ∈ swaps, autB mol pairs = true) (center : Nat) (valid : center < mol.atomCount)
    (good : goodB mol swaps (structuralDepth mol (canonicalCenterRoot center) + 1)
      (canonicalCenterRoot center) = true) (geom : Geometry) :
    assignCenter? mol ops geom center = none := by
  have root := reached_root mol center valid
  unfold assignCenter?
  exact descriptor_none cov swaps auts _ geom none _ root good (fun _ same => by cases same)
    (fun child member r goodChild absentChild =>
      facts_vanish cov swaps auts _ geom (some r) child
        (reached_child mol _ child root member) goodChild
        (fun r' same => by cases same; exact absentChild))

end Region

/-! ## The subdivided cage -/

private def atom (element : Element) : AtomSpec := AtomSpec.aliphatic element
private def bond (source target : Nat) : RawBond :=
  { source := source, target := target, kind := .single }

/-- The accepted 15-atom cage with each of its six bridges subdivided by one oxygen; the same
literal as `LocalizedMarkedSubdividedCageProbe.mol`. -/
def mol : RawMolecule :=
  { atoms := [.C, .H, .Cl, .C, .H, .O, .O, .O, .C, .C, .H, .O, .O, .O, .C].map atom ++
      List.replicate 6 (atom .O)
    bonds := [bond 0 1, bond 0 2, bond 0 3, bond 0 9,
      bond 3 5, bond 3 6, bond 3 7, bond 4 8,
      bond 5 15, bond 15 8, bond 6 16, bond 16 8, bond 7 17, bond 17 8,
      bond 9 11, bond 9 12, bond 9 13, bond 10 14,
      bond 11 18, bond 18 14, bond 12 19, bond 19 14, bond 13 20, bond 20 14]
    neighborOrder := [[1,2,3,9], [0], [0], [0,5,6,7], [8], [3,15], [3,16], [3,17],
      [4,15,16,17], [0,11,12,13], [14], [9,18], [9,19], [9,20], [10,18,19,20],
      [5,8], [6,8], [7,8], [11,14], [12,14], [13,14]] }

/-- Cage exchange and the bridge exchanges of each cage. -/
def cageSwaps : List (List (Nat × Nat)) :=
  [[(3, 9), (4, 10), (5, 11), (6, 12), (7, 13), (8, 14), (15, 18), (16, 19), (17, 20)],
   [(5, 6), (15, 16)], [(5, 7), (15, 17)], [(6, 7), (16, 17)],
   [(11, 12), (18, 19)], [(11, 13), (18, 20)], [(12, 13), (19, 20)]]

theorem cageSwaps_automorphisms : ∀ pairs ∈ cageSwaps, autB mol pairs = true := by
  decide +kernel

/-- Kernel certificate of the whole evaluation region of centre `0`. -/
theorem cage_good :
    goodB mol cageSwaps (structuralDepth mol (canonicalCenterRoot 0) + 1)
      (canonicalCenterRoot 0) = true := by
  decide +kernel

/-- **Every covariant ranker refuses centre `0` of the subdivided cage, for every geometry.** -/
theorem refuses (ops : Operations) (cov : EmptyStateCovariant mol ops) (geom : Geometry) :
    assignCenter? mol ops geom 0 = none :=
  assignCenter_none cov cageSwaps cageSwaps_automorphisms 0 (by decide) cage_good geom

/-- The whole report omits centre `0`. -/
theorem report_omits (ops : Operations) (cov : EmptyStateCovariant mol ops) (geom : Geometry)
    (d : LocalizedTetrahedralRSPseudoDescriptor) : (0, d) ∉ assign mol ops geom := by
  intro member
  simp only [assign, List.mem_filterMap, List.mem_range] at member
  obtain ⟨center, _, found⟩ := member
  cases hc : assignCenter? mol ops geom center with
  | none => rw [hc] at found; cases found
  | some value =>
      rw [hc] at found
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, -⟩ := found
      rw [refuses ops cov geom] at hc
      cases hc

/-! ## Control: the unsubdivided cage is not certified -/

/-- The accepted 15-atom cage (`LocalizedHiddenParityMarkedProbe.cageRaw`). -/
def cage15 : RawMolecule :=
  { atoms := [.C, .H, .Cl, .C, .H, .O, .O, .O, .C, .C, .H, .O, .O, .O, .C].map atom
    bonds := [bond 0 1, bond 0 2, bond 0 3, bond 0 9,
      bond 3 5, bond 3 6, bond 3 7, bond 4 8, bond 5 8, bond 6 8, bond 7 8,
      bond 9 11, bond 9 12, bond 9 13, bond 10 14, bond 11 14, bond 12 14,
      bond 13 14]
    neighborOrder := [[1, 2, 3, 9], [0], [0], [0, 5, 6, 7], [8], [3, 8], [3, 8], [3, 8],
      [4, 5, 6, 7], [0, 11, 12, 13], [14], [9, 14], [9, 14], [9, 14], [10, 11, 12, 13]] }

def cage15Swaps : List (List (Nat × Nat)) :=
  [[(3, 9), (4, 10), (5, 11), (6, 12), (7, 13), (8, 14)],
   [(5, 6)], [(5, 7)], [(6, 7)], [(11, 12)], [(11, 13)], [(12, 13)]]

/-- Near marks reach the far frames of the unsubdivided cage: the certificate fails there. -/
theorem unsubdivided_not_certified :
    goodB cage15 cage15Swaps (structuralDepth cage15 (canonicalCenterRoot 0) + 1)
      (canonicalCenterRoot 0) = false := by
  decide +kernel

end TetraStereo.OneCenter.LocalizedMarkedCyclicDiscardedReference

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCyclicDiscardedReference.consensus_some
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCyclicDiscardedReference.marked_pair_complement
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCyclicDiscardedReference.rawStep_none
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCyclicDiscardedReference.autB_sound
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCyclicDiscardedReference.descriptor_none
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCyclicDiscardedReference.facts_vanish
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCyclicDiscardedReference.assignCenter_none
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCyclicDiscardedReference.cageSwaps_automorphisms
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCyclicDiscardedReference.cage_good
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCyclicDiscardedReference.refuses
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCyclicDiscardedReference.report_omits
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCyclicDiscardedReference.unsubdivided_not_certified
