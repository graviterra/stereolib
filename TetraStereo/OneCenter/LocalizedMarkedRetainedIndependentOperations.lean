import TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame
import TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedOperations
import TetraStereo.OneCenter.LocalizedMarkedDetectedSnapshotSupport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Generated auxiliary labels from independently specified operations

The recursive marked evaluator (`LocalizedMarkedOperationEvaluator`) generates every temporary
auxiliary fact, every centre's own descriptor and the whole report from two comparison
operations. This module separates what those facts mean from the runtime comparators.

* `facts_congr`: two operation records generate exactly the same facts, at every depth, geometry,
  state and inherited context, on every reached occurrence, whenever they agree at every reached
  occurrence with a raw frame. Marked rankings need agree only on their positions and uniqueness,
  the only fields read by the evaluator.
* `independentOperations`: an operations record with no runtime comparator. Lookup, frame and
  raw-position transport are the structural executables already used by the experimental
  operations. Orders are the descending orders of the independent retained Rules-1–5 keys, and of
  `(retained key, independent canonical marker)` for the marked stage.
* `facts_eq_independent`, `descriptor_eq_independent`, `assign_eq_independent`: for the
  experimental retained-promoted operations every generated fact, every recursive auxiliary
  descriptor and every whole-report entry equals that of the independent operations.

The independent keys are evaluated on the actual compiled arm and stage graphs, as in the accepted
frame-level theorems. The result is an operational identification; it does not establish the
physical meaning of the generated labels.

Domain, all explicit: intake agreement and admission, localized covalent single bonds, and here
no raw atom with exactly three neighbours (`NoThreeCoordinate`; removed in
`LocalizedMarkedRetainedReachDegree`). Branching atoms are arbitrary. Rings, ring duplicates,
arbitrary depth, empty and multiple references and arbitrary geometry are allowed.

This identifies the generated labels with an independent recursive specification that retains the
experimental reference/consensus policy, including its immediate-frame inherited-reference rule.
It does not assert that this policy is official CIP semantics or physically correct.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRetainedIndependentOperations

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedMarkedOperationEvaluator
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedOperations
open LocalizedMarkedRetainedPromotedRanking LocalizedMarkedRetainedPromotedOperations
open LocalizedMarkedRetainedCanonicalMarker LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedSubtreeContext LocalizedCumulativeDecoratedTree
open LocalizedMarkedCarrierLookup LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors LocalizedMarkedCertifiedTerminalRefusal
open LocalizedMarkedDetectedSnapshotSupport LocalizedMarkedOperationSimulation
open LocalizedGenericMarkedRecalculation
  (Geometry frameAtoms? readback? atomsAt? rankedAtoms? consistent strict eligibleOf
    appendFacts? consensus caseFromMirror? factOf flatMap_congr_mem)

abbrev Node := RawMolecule.CanonicalBranchNode

/-! ## Operation congruence -/

section Congruence

variable (mol : RawMolecule)

/-- The fields of a marked ranking read by the evaluator. -/
def shape (ranking : Rule6TrackedRanking) : List Nat × Bool := (ranking.positions, ranking.unique)

/-- Agreement of two operation records at one occurrence. -/
def AgreeAt (first second : Operations) (node : Node) : Prop :=
  (∀ state, first.ordinary state node = second.ordinary state node) ∧
    (∀ state mark, (first.marked state node mark).map shape =
      (second.marked state node mark).map shape)

theorem markedReading_congr (first second : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (mark : Nat)
    (same : (first.marked state node mark).map shape = (second.marked state node mark).map shape) :
    markedReading? mol first geom state node mark = markedReading? mol second geom state node mark := by
  unfold markedReading?
  cases hf : first.marked state node mark <;> cases hs : second.marked state node mark <;>
    simp only [hf, hs, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at same
  · rfl
  · rename_i a b
    have positions : a.positions = b.positions := congrArg Prod.fst same
    have unique : a.unique = b.unique := congrArg Prod.snd same
    simp only [Option.bind_eq_bind, Option.bind_some, rankedAtoms?, positions, unique]

theorem rawStep_congr (first second : Operations) (node : Node)
    (agree : AgreeAt first second node) (geom : Geometry) (state : OccurrenceAuxState)
    (ctx : Option Nat) (under : Nat → OccurrenceAuxState) :
    rawStep? mol first geom state ctx node under = rawStep? mol second geom state ctx node under := by
  have reading : ∀ temp mark, markedReading? mol first geom temp node mark =
      markedReading? mol second geom temp node mark :=
    fun temp mark => markedReading_congr mol first second geom temp node mark (agree.2 temp mark)
  unfold rawStep?
  simp only [agree.1 state, reading]

theorem tiedChildren_congr (first second : Operations) (node : Node)
    (agree : AgreeAt first second node) (state : OccurrenceAuxState) :
    tiedChildren mol first state node = tiedChildren mol second state node := by
  unfold tiedChildren
  rw [agree.1 state]

theorem descriptorWith_congr_ops (first second : Operations) (node : Node)
    (agree : AgreeAt first second node) (geom : Geometry) (state : OccurrenceAuxState)
    (ctx : Option Nat)
    (sub₁ sub₂ : Geometry → OccurrenceAuxState → Option Nat → Node → OccurrenceAuxState)
    (subAgree : ∀ child ∈ mol.canonicalChildren node, ∀ g s x, sub₁ g s x child = sub₂ g s x child) :
    descriptorWith? mol first geom state ctx node sub₁ =
      descriptorWith? mol second geom state ctx node sub₂ := by
  rw [descriptorWith?_congr mol first geom state ctx node sub₁ sub₂ subAgree]
  unfold descriptorWith? rawWith? underWith
  rw [tiedChildren_congr mol first second node agree state,
    rawStep_congr mol first second node agree geom, rawStep_congr mol first second node agree]

/-- **Operation congruence for generated facts.** -/
theorem facts_congr (first second : Operations)
    (agree : ∀ node, Reached mol node → ∀ atoms, frameAtoms? mol node = some atoms →
      AgreeAt first second node) :
    ∀ depth geom state ctx node, Reached mol node →
      facts mol first depth geom state ctx node = facts mol second depth geom state ctx node := by
  intro depth
  induction depth with
  | zero => intros; rfl
  | succ depth ih =>
      intro geom state ctx node reached
      have children : ∀ child ∈ mol.canonicalChildren node, ∀ g s x,
          facts mol first depth g s x child = facts mol second depth g s x child :=
        fun child member g s x => ih g s x child (reached_child mol node child reached member)
      have descriptor : descriptor? mol first depth geom state ctx node =
          descriptor? mol second depth geom state ctx node := by
        unfold descriptor?
        cases frame : frameAtoms? mol node with
        | none =>
            rw [descriptor_none_of_frame mol first geom state ctx node _ frame,
              descriptor_none_of_frame mol second geom state ctx node _ frame]
        | some atoms =>
            exact descriptorWith_congr_ops mol first second node (agree node reached atoms frame)
              geom state ctx _ _ children
      rw [facts_succ, facts_succ, descriptor]
      congr 1
      exact flatMap_congr_mem _ _ _ fun child member => children child member geom state ctx

theorem descriptor_congr (first second : Operations)
    (agree : ∀ node, Reached mol node → ∀ atoms, frameAtoms? mol node = some atoms →
      AgreeAt first second node)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (reached : Reached mol node) :
    descriptor? mol first depth geom state ctx node =
      descriptor? mol second depth geom state ctx node := by
  unfold descriptor?
  cases frame : frameAtoms? mol node with
  | none =>
      rw [descriptor_none_of_frame mol first geom state ctx node _ frame,
        descriptor_none_of_frame mol second geom state ctx node _ frame]
  | some atoms =>
      exact descriptorWith_congr_ops mol first second node (agree node reached atoms frame)
        geom state ctx _ _ fun child member g s x =>
          facts_congr mol first second agree depth g s x child
            (reached_child mol node child reached member)

theorem assign_congr (first second : Operations)
    (agree : ∀ node, Reached mol node → ∀ atoms, frameAtoms? mol node = some atoms →
      AgreeAt first second node) (geom : Geometry) :
    assign mol first geom = assign mol second geom := by
  unfold assign
  apply List.filterMap_congr
  intro center member
  have valid : center < mol.atomCount := List.mem_range.mp member
  unfold assignCenter?
  rw [descriptor_congr mol first second agree _ geom [] none _ (reached_root mol center valid)]

end Congruence

/-! ## Independently specified operations -/

section Independent

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (fallback : CompleteLigandRule5Key)

/-- Real detected carrier occurrence. -/
abbrev RealDetected (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input)) : Prop :=
  target.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
    IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit target.1).atom

noncomputable section
open scoped Classical

/-- Independent Rules-1–5 partition: the descending order of the retained keys. -/
def independentOrdinaryPartition (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input)) :
    Option (List (Fin 4) × List (Option Ordering)) :=
  if h : RealDetected input target then
    some (keyOrder (rawStateKeys input single state target h.1 ⟨_, h.2⟩ rfl) (List.finRange 4),
      adjacentBy (fun left right => some
        (compare (rawStateKeys input single state target h.1 ⟨_, h.2⟩ rfl left)
          (rawStateKeys input single state target h.1 ⟨_, h.2⟩ rfl right)))
        (keyOrder (rawStateKeys input single state target h.1 ⟨_, h.2⟩ rfl) (List.finRange 4)))
  else none

/-- Independent Rule-6 partition: the descending order of the retained key followed by the
independent canonical marker. -/
def independentMarkedPartition (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input)) (reference : input.Atom)
    (W D : Nat) : Option (List (Fin 4) × List (Option Ordering)) :=
  if h : RealDetected input target then
    some (keyOrder (canonicalKey input single state target h.1 ⟨_, h.2⟩ rfl reference W D fallback)
        (List.finRange 4),
      adjacentBy (fun left right => some
        (compare (canonicalKey input single state target h.1 ⟨_, h.2⟩ rfl reference W D fallback left)
          (canonicalKey input single state target h.1 ⟨_, h.2⟩ rfl reference W D fallback right)))
        (keyOrder (canonicalKey input single state target h.1 ⟨_, h.2⟩ rfl reference W D fallback)
          (List.finRange 4)))
  else none

def independentOrdinary (mol : RawMolecule) (state : OccurrenceAuxState) (node : Node) :
    Option (List Nat × List (Option Ordering)) := do
  let target ← lookup? input node
  let atoms ← frameAtoms? mol node
  let frame ← input.localizedNoDoubleFourLigandFrameExec? target
  let partition ← independentOrdinaryPartition input single state target
  let positions ← positions? input atoms frame partition.1
  some (positions, partition.2)

/-- The promotion-use count is not read by the evaluator; the independent record reports zero. -/
def independentMarked (mol : RawMolecule) (state : OccurrenceAuxState) (node : Node) (mark : Nat) :
    Option Rule6TrackedRanking :=
  if bound : mark < input.certified.input.molecule.atomCount then do
    let target ← lookup? input node
    let atoms ← frameAtoms? mol node
    let frame ← input.localizedNoDoubleFourLigandFrameExec? target
    let partition ← independentMarkedPartition input single fallback state target ⟨mark, bound⟩
      (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))
    let positions ← positions? input atoms frame partition.1
    some { positions := positions, unique := strict partition.2, pseudoComparisons := 0 }
  else none

/-- **The independent operations.** No runtime comparator is called. -/
def independentOperations (mol : RawMolecule) : Operations where
  ordinary := independentOrdinary input single mol
  marked := independentMarked input single fallback mol

end

/-! ## Agreement with the experimental retained-promoted operations -/

theorem ordinaryPartition_eq_independent (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (h : RealDetected input target) :
    ordinaryPartition? input state target = independentOrdinaryPartition input single state target := by
  unfold independentOrdinaryPartition
  rw [dif_pos h]
  exact ordinaryPartition?_eq input single state target h.1 ⟨_, h.2⟩ rfl

theorem markedPartition_eq_independent
    (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (h : RealDetected input target) (reference : input.Atom) (W D : Nat) :
    LocalizedMarkedRetainedPromotedRanking.partition? input state target reference W D =
      independentMarkedPartition input single fallback state target reference W D := by
  unfold independentMarkedPartition
  rw [dif_pos h]
  exact partition?_eq_canonical input single state target h.1 ⟨_, h.2⟩ rfl reference W D fallback

theorem ordinary_eq_independent (mol : RawMolecule) (state : OccurrenceAuxState) (node : Node)
    (detected : ∀ target, lookup? input node = some target → RealDetected input target) :
    LocalizedMarkedRetainedOperations.ordinary input mol state node =
      independentOrdinary input single mol state node := by
  unfold LocalizedMarkedRetainedOperations.ordinary independentOrdinary
  cases found : lookup? input node with
  | none => rfl
  | some target =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [ordinaryPartition_eq_independent input single state target (detected target found)]

theorem marked_shape_eq_independent
    (mol : RawMolecule) (state : OccurrenceAuxState) (node : Node) (mark : Nat)
    (detected : ∀ target, lookup? input node = some target → RealDetected input target) :
    (marked? input mol state node mark).map shape =
      (independentMarked input single fallback mol state node mark).map shape := by
  unfold marked? markedWithLayout? independentMarked
  by_cases bound : mark < input.certified.input.molecule.atomCount
  · rw [dif_pos bound, dif_pos bound]
    cases found : lookup? input node with
    | none => rfl
    | some target =>
        have h := detected target found
        simp only [Option.bind_eq_bind, Option.bind_some]
        cases frameAtomsEq : frameAtoms? mol node with
        | none => rfl
        | some atoms =>
            simp only [Option.bind_some]
            rw [(frames input single state target h.1 ⟨_, h.2⟩ rfl).frameComputed]
            simp only [Option.bind_some]
            rw [markedPartition_eq_independent input single fallback state target h]
            unfold independentMarkedPartition
            rw [dif_pos h]
            simp only [Option.bind_some]
            cases positionsEq : positions? input atoms
                (frames input single state target h.1 ⟨_, h.2⟩ rfl).frame
                (keyOrder (canonicalKey input single state target h.1 ⟨_, h.2⟩ rfl ⟨mark, bound⟩
                  (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) fallback)
                  (List.finRange 4)) with
            | none => rfl
            | some positions =>
                simp only [Option.bind_some]
                have oldTotal : ∀ a b, ∃ order, rawStateBefore input state target
                    (frames input single state target h.1 ⟨_, h.2⟩ rfl).frame a b = some order :=
                  fun a b => ⟨_, rawStateBefore_eq_keys input single state target h.1 ⟨_, h.2⟩ rfl a b⟩
                have newTotal : ∀ a b, ∃ order, before input state target ⟨mark, bound⟩
                    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))
                    (frames input single state target h.1 ⟨_, h.2⟩ rfl).frame a b = some order :=
                  fun a b => ⟨_, before_eq_refined input single state target h.1 ⟨_, h.2⟩ rfl
                    ⟨mark, bound⟩ _ _ a b⟩
                obtain ⟨count, counted⟩ := adjacentPromotionCount?_exists _ _ oldTotal newTotal
                  (keyOrder (canonicalKey input single state target h.1 ⟨_, h.2⟩ rfl ⟨mark, bound⟩
                    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) fallback)
                    (List.finRange 4))
                rw [counted]
                rfl
  · rw [dif_neg bound, dif_neg bound]

variable (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)

/-- No raw atom has exactly three neighbours. -/
def NoThreeCoordinate : Prop :=
  ∀ atom < mol.atomCount, (mol.canonicalIncidentNeighbors atom).length ≠ 3

include agreement admissible supported single in
/-- At every reached occurrence with a raw frame, every looked-up carrier occurrence is a real
detected centre. -/
theorem lookup_realDetected (noThree : NoThreeCoordinate mol) (node : Node)
    (reached : Reached mol node) (atoms : List Nat) (frame : frameAtoms? mol node = some atoms) :
    ∀ target, lookup? input node = some target → RealDetected input target := by
  intro target found
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have rawReal := LocalizedMarkedGeneratedSnapshotSupport.real_of_frame mol node atoms frame
  have valid := reached_atom_valid mol wellFormed node reached
  have four : (mol.canonicalIncidentNeighbors node.atom).length = 4 := by
    rcases frame_atoms_perm_neighbors mol wellFormed rawSingle node reached atoms frame with
      ⟨four, _⟩ | ⟨three, _⟩
    · exact four
    · exact absurd three (noThree node.atom valid)
  exact ⟨lookup?_real input node target found rawReal,
    carrier_detected_of_raw_degree mol input agreement wellFormed unique supported rawSingle
      target node valid (lookup?_sound input node target found) four⟩

include agreement admissible supported in
theorem agreeAt (noThree : NoThreeCoordinate mol)
    (node : Node) (reached : Reached mol node) (atoms : List Nat)
    (frame : frameAtoms? mol node = some atoms) :
    AgreeAt (operations input mol) (independentOperations input single fallback mol) node := by
  have detected := lookup_realDetected input single mol agreement admissible supported noThree
    node reached atoms frame
  exact ⟨fun state => ordinary_eq_independent input single mol state node detected,
    fun state mark => marked_shape_eq_independent input single fallback mol state node
      mark detected⟩

include agreement admissible supported in
/-- **Generated auxiliary facts are those of the independent operations**, at every depth,
geometry, state and inherited context. -/
theorem facts_eq_independent (noThree : NoThreeCoordinate mol) :
    ∀ depth geom state ctx node, Reached mol node →
      facts mol (operations input mol) depth geom state ctx node =
        facts mol (independentOperations input single fallback mol) depth geom state ctx node :=
  facts_congr mol _ _ (agreeAt input single fallback mol agreement admissible supported noThree)

include agreement admissible supported in
/-- Every recursive auxiliary descriptor, including inherited contexts, agrees. -/
theorem descriptor_eq_independent (noThree : NoThreeCoordinate mol)
    (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node) (reached : Reached mol node) :
    descriptor? mol (operations input mol) depth geom state ctx node =
      descriptor? mol (independentOperations input single fallback mol) depth geom state ctx node :=
  descriptor_congr mol _ _ (agreeAt input single fallback mol agreement admissible supported noThree)
    depth geom state ctx node reached

include agreement admissible supported in
/-- **The whole detected-centre report of the experimental evaluator is the report of the
independent operations.** -/
theorem assign_eq_independent (noThree : NoThreeCoordinate mol) (geom : Geometry) :
    assign mol (operations input mol) geom =
      assign mol (independentOperations input single fallback mol) geom :=
  assign_congr mol _ _ (agreeAt input single fallback mol agreement admissible supported noThree)
    geom

end Independent

end TetraStereo.OneCenter.LocalizedMarkedRetainedIndependentOperations

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedIndependentOperations.markedReading_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedIndependentOperations.rawStep_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedIndependentOperations.descriptorWith_congr_ops
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedIndependentOperations.facts_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedIndependentOperations.assign_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedIndependentOperations.ordinary_eq_independent
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedIndependentOperations.marked_shape_eq_independent
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedIndependentOperations.lookup_realDetected
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedIndependentOperations.facts_eq_independent
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedIndependentOperations.descriptor_eq_independent
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedIndependentOperations.assign_eq_independent
