import TetraStereo.OneCenter.P93MolecularFullereneFlagExtension
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Saturation of the molecular-fullerene flag search

The deduplicated search in `P93MolecularFullereneFlagExtension` stores positive bonded darts,
not words.  This file proves the missing finite-state fact: once flag-orbit coverage exists, the
search has already found every covered carrier atom after at most the number of bonded darts.
The proof is a genuine saturation argument over a monotone finite chain; it never enumerates the
exponential family of flag words.
-/

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

private theorem molecularFullereneFlagReachableEdges_mono_one
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (fuel : ℕ) :
    molecularFullereneFlagReachableEdges molecule input source fuel ⊆
      molecularFullereneFlagReachableEdges molecule input source (fuel + 1) := by
  intro edge present
  simp only [molecularFullereneFlagReachableEdges, Finset.mem_union]
  exact Or.inl present

private theorem molecularFullereneFlagReachableEdges_mono
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    {first second : ℕ} (le : first ≤ second) :
    molecularFullereneFlagReachableEdges molecule input source first ⊆
      molecularFullereneFlagReachableEdges molecule input source second := by
  induction second, le using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ second le inductionHypothesis =>
      exact Finset.Subset.trans inductionHypothesis
        (molecularFullereneFlagReachableEdges_mono_one molecule input source second)

private theorem molecularFullereneFlagReachableEdges_subset_bonded
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1)
    (fuel : ℕ) :
    molecularFullereneFlagReachableEdges molecule input source fuel ⊆
      molecularFullereneBondedDirectedEdges molecule input := by
  intro edge present
  have bond := (mem_molecularFullereneFlagReachableEdges_sound molecule input source
    sourceBond fuel edge present).1
  simp only [molecularFullereneBondedDirectedEdges, Finset.mem_filter,
    Finset.mem_univ, true_and, decide_eq_true_eq]
  exact bond

private theorem molecularFullereneFlagReachableEdges_eq_succ_propagates
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    {fuel : ℕ}
    (stable : molecularFullereneFlagReachableEdges molecule input source fuel =
      molecularFullereneFlagReachableEdges molecule input source (fuel + 1)) :
    ∀ offset,
      molecularFullereneFlagReachableEdges molecule input source (fuel + offset) =
        molecularFullereneFlagReachableEdges molecule input source (fuel + offset + 1) := by
  intro offset
  induction offset with
  | zero => simpa using stable
  | succ offset inductionHypothesis =>
      simpa only [molecularFullereneFlagReachableEdges, Nat.add_assoc,
        Nat.add_comm 1 offset, Nat.add_left_comm 1 offset] using
          congrArg (fun previous =>
            previous ∪ (((Finset.univ : Finset MolecularFullereneFlagMove) ×ˢ previous).image
              (fun state => molecularFullereneFlagStep
                (molecularFullereneContinueForwardFace input) state.1 state.2)).filter
                  (fun edge => decide
                    (0 < molecule.bondOrder edge.1.1 edge.2.1))) inductionHypothesis

private theorem molecularFullereneFlagReachableEdges_stable_at_bound
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1) :
    molecularFullereneFlagReachableEdges molecule input source
        (molecularFullereneFlagStateBound molecule input) =
      molecularFullereneFlagReachableEdges molecule input source
        (molecularFullereneFlagStateBound molecule input + 1) := by
  let bound := molecularFullereneFlagStateBound molecule input
  by_contra notStable
  have strictBefore : ∀ fuel, fuel ≤ bound →
      molecularFullereneFlagReachableEdges molecule input source fuel ⊂
        molecularFullereneFlagReachableEdges molecule input source (fuel + 1) := by
    intro fuel fuelLe
    refine (Finset.ssubset_iff_subset_ne).2
      ⟨molecularFullereneFlagReachableEdges_mono_one molecule input source fuel, ?_⟩
    intro equal
    have propagated := molecularFullereneFlagReachableEdges_eq_succ_propagates
      molecule input source equal (bound - fuel)
    have fuelAdd : fuel + (bound - fuel) = bound := Nat.add_sub_of_le fuelLe
    exact notStable (by simpa only [fuelAdd] using propagated)
  have cardLower : ∀ fuel, fuel ≤ bound →
      fuel + 1 ≤ (molecularFullereneFlagReachableEdges molecule input source fuel).card := by
    intro fuel fuelLe
    induction fuel with
    | zero => simp [molecularFullereneFlagReachableEdges]
    | succ fuel inductionHypothesis =>
        have fuelLeBound : fuel ≤ bound := Nat.le_trans (Nat.le_succ fuel) fuelLe
        have lower := inductionHypothesis fuelLeBound
        have strictCard := Finset.card_lt_card
          (strictBefore fuel fuelLeBound)
        omega
  have lower := cardLower bound (Nat.le_refl bound)
  have upper :
      (molecularFullereneFlagReachableEdges molecule input source bound).card ≤ bound := by
    change _ ≤ (molecularFullereneBondedDirectedEdges molecule input).card
    exact Finset.card_le_card
      (molecularFullereneFlagReachableEdges_subset_bonded molecule input source sourceBond bound)
  omega

/-- Every finite flag word lands in the deduplicated bonded-dart search by the exact state-count
bound.  This is the finite-state saturation theorem: the word length disappears entirely. -/
theorem walkMolecularFullereneFlag_mem_reachableEdges_at_stateBound
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1)
    (moves : List MolecularFullereneFlagMove) :
    walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input) source moves ∈
      molecularFullereneFlagReachableEdges molecule input source
        (molecularFullereneFlagStateBound molecule input) := by
  let bound := molecularFullereneFlagStateBound molecule input
  have stable := molecularFullereneFlagReachableEdges_stable_at_bound
    molecule input source sourceBond
  have sourcePresent : source ∈
      molecularFullereneFlagReachableEdges molecule input source bound := by
    apply molecularFullereneFlagReachableEdges_mono molecule input source (Nat.zero_le bound)
    simp [molecularFullereneFlagReachableEdges]
  have closed : ∀ (word : List MolecularFullereneFlagMove)
      (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input),
      edge ∈ molecularFullereneFlagReachableEdges molecule input source bound →
      walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input) edge word ∈
        molecularFullereneFlagReachableEdges molecule input source bound := by
    intro word
    induction word with
    | nil =>
        intro edge present
        exact present
    | cons move word inductionHypothesis =>
        intro edge present
        have nextPresent := molecularFullereneFlagStep_mem_reachableEdges_succ molecule input
          oriented source sourceBond bound edge present move
        rw [← stable] at nextPresent
        exact inductionHypothesis
          (molecularFullereneFlagStep (molecularFullereneContinueForwardFace input) move edge)
          nextPresent
  exact closed moves source sourcePresent

/-- Carrier-covering orbit reachability is therefore equivalent to the concrete bounded BFS
coverage judgment; only the nontrivial direction uses finite-state saturation. -/
theorem molecularFullereneFlagOrbitCoversCarrier_to_deduplicatedSpanning
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1)
    (covers : MolecularFullereneFlagOrbitCoversCarrier input source) :
    MolecularFullereneDeduplicatedFlagSpanningJudgment molecule input source := by
  intro atom
  rcases covers atom with ⟨moves, recovers⟩
  refine ⟨walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
      source moves, ?_, recovers⟩
  exact walkMolecularFullereneFlag_mem_reachableEdges_at_stateBound molecule input oriented
    source sourceBond moves

/-! ## Topological collapse from connected cubic face maps -/

/-- Turning an incoming dart once around its terminal atom: continue along its coherently
oriented incident face, then regard the resulting atom as the new incoming endpoint. -/
def molecularFullereneIncomingTurn
    (input : MolecularFullereneConfigurationInput)
    (incoming center : MolecularFullereneCarrierAtom input) :
    MolecularFullereneCarrierAtom input :=
  molecularFullereneContinueForwardFace input (incoming, center)

private theorem next_next_ne_self_of_nodup_of_three_le
    (face : List ℕ) (nodup : face.Nodup) (threeLe : 3 ≤ face.length)
    (atom : ℕ) (member : atom ∈ face) :
    face.next (face.next atom member) (List.next_mem face atom member) ≠ atom := by
  obtain ⟨index, indexLt, atomEq⟩ := List.getElem_of_mem member
  subst atom
  have memberEq : member = List.getElem_mem indexLt := Subsingleton.elim _ _
  subst member
  let FaceAtom := { value : ℕ // value ∈ face }
  let nextFace : FaceAtom → FaceAtom := fun value =>
    ⟨face.next value.1 value.2, List.next_mem face value.1 value.2⟩
  let first : FaceAtom := ⟨face[index], List.getElem_mem indexLt⟩
  let secondIndex := (index + 1) % face.length
  have secondIndexLt : secondIndex < face.length := Nat.mod_lt _ (by omega)
  let second : FaceAtom := ⟨face[secondIndex], List.getElem_mem secondIndexLt⟩
  let thirdIndex := (secondIndex + 1) % face.length
  have thirdIndexLt : thirdIndex < face.length := Nat.mod_lt _ (by omega)
  let third : FaceAtom := ⟨face[thirdIndex], List.getElem_mem thirdIndexLt⟩
  have firstStep : nextFace first = second := by
    apply Subtype.ext
    exact List.next_getElem face nodup index indexLt
  have secondStep : nextFace second = third := by
    apply Subtype.ext
    exact List.next_getElem face nodup secondIndex secondIndexLt
  intro equal
  have iterationEq : nextFace (nextFace first) = first := by
    apply Subtype.ext
    exact equal
  have thirdEqFirst : third = first := by
    rw [firstStep, secondStep] at iterationEq
    exact iterationEq
  have indexEq : (((index + 1) % face.length) + 1) % face.length = index :=
    (nodup.getElem_inj_iff).mp (congrArg Subtype.val thirdEqFirst)
  by_cases firstBelow : index + 1 < face.length
  · have firstMod : (index + 1) % face.length = index + 1 :=
      Nat.mod_eq_of_lt firstBelow
    rw [firstMod] at indexEq
    by_cases secondBelow : index + 2 < face.length
    · rw [Nat.mod_eq_of_lt secondBelow] at indexEq
      omega
    · have oneWrap : index + 2 - face.length < face.length := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt oneWrap] at indexEq
      omega
  · have atLast : index + 1 = face.length := by omega
    rw [atLast, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega)] at indexEq
    omega

/-- The local turn takes one cage neighbor of `center` to another cage neighbor. -/
theorem molecularFullereneIncomingTurn_mem_neighbors
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (incoming center : MolecularFullereneCarrierAtom input)
    (bond : 0 < molecule.bondOrder incoming.1 center.1) :
    (molecularFullereneIncomingTurn input incoming center).1 ∈
      molecularFullereneCageNeighbors molecule input.carrier center.1 := by
  have nextBond := molecularFullereneFlagStep_bond molecule input oriented
    .continueLeftFace (incoming, center) bond
  simp only [molecularFullereneFlagStep] at nextBond
  simp only [molecularFullereneCageNeighbors, Finset.mem_filter]
  exact ⟨(molecularFullereneIncomingTurn input incoming center).2, nextBond⟩

/-- A validated pentagonal/hexagonal face never turns straight back to the incoming atom. -/
theorem molecularFullereneIncomingTurn_ne
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (incoming center : MolecularFullereneCarrierAtom input)
    (bond : 0 < molecule.bondOrder incoming.1 center.1) :
    molecularFullereneIncomingTurn input incoming center ≠ incoming := by
  rcases molecularFullereneContinueForwardFace_judged molecule input oriented
      (incoming, center) bond with ⟨face, facePresent, firstEdge, secondEdge⟩
  have valid := oriented.1.facesValid face facePresent
  rcases firstEdge with ⟨incomingMember, firstNext⟩
  rcases secondEdge with ⟨centerMember, secondNext⟩
  intro equal
  apply next_next_ne_self_of_nodup_of_three_le face valid.1.2.1
    (by rcases valid.2.2 with length | length <;> omega) incoming.1 incomingMember
  calc
    face.next (face.next incoming.1 incomingMember)
        (List.next_mem face incoming.1 incomingMember) =
        face.next center.1 centerMember := by
      congr 1
    _ = (molecularFullereneIncomingTurn input incoming center).1 := secondNext
    _ = incoming.1 := congrArg Subtype.val equal

/-- The local turn is injective on the three molecular neighbors of a cage atom.  Its inverse is
the semantic opposite-face continuation, so this uses no coordinate or embedding assumption. -/
theorem molecularFullereneIncomingTurn_injective_on_neighbors
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (center first second : MolecularFullereneCarrierAtom input)
    (firstBond : 0 < molecule.bondOrder first.1 center.1)
    (secondBond : 0 < molecule.bondOrder second.1 center.1)
    (equal : molecularFullereneIncomingTurn input first center =
      molecularFullereneIncomingTurn input second center) :
    first = second := by
  let next := molecularFullereneIncomingTurn input first center
  have firstForward := molecularFullereneContinueForwardFace_judged molecule input oriented
    (first, center) firstBond
  have secondForward := molecularFullereneContinueForwardFace_judged molecule input oriented
    (second, center) secondBond
  have firstReverse : MolecularFullereneReverseContinuationJudgment input (next, center) first := by
    rcases firstForward with ⟨face, facePresent, firstEdge, secondEdge⟩
    exact ⟨face, facePresent, by simpa [next, molecularFullereneIncomingTurn] using secondEdge,
      firstEdge⟩
  have secondReverse : MolecularFullereneReverseContinuationJudgment input (next, center) second := by
    rcases secondForward with ⟨face, facePresent, firstEdge, secondEdge⟩
    exact ⟨face, facePresent,
      by simpa [next, molecularFullereneIncomingTurn, equal] using secondEdge, firstEdge⟩
  have nextBond : 0 < molecule.bondOrder next.1 center.1 := by
    have nextPresent := molecularFullereneIncomingTurn_mem_neighbors molecule input oriented
      first center firstBond
    have forward : 0 < molecule.bondOrder center.1 next.1 := by
      exact (Finset.mem_filter.mp nextPresent).2
    simpa [molecule.bondOrder_symm] using forward
  exact molecularFullereneReverseContinuationJudgment_functional molecule input oriented
    (next, center) nextBond first second firstReverse secondReverse

private theorem orbit_three_of_maps_injective_noFixed
    {alpha : Type} [DecidableEq alpha]
    (items : Finset alpha) (card : items.card = 3) (turn : alpha → alpha)
    (closed : ∀ atom ∈ items, turn atom ∈ items)
    (injective : ∀ first ∈ items, ∀ second ∈ items,
      turn first = turn second → first = second)
    (noFixed : ∀ atom ∈ items, turn atom ≠ atom)
    (source target : alpha) (sourcePresent : source ∈ items)
    (targetPresent : target ∈ items) :
    target = source ∨ target = turn source ∨ target = turn (turn source) := by
  by_cases targetSource : target = source
  · exact Or.inl targetSource
  by_cases targetTurn : target = turn source
  · exact Or.inr (Or.inl targetTurn)
  apply Or.inr
  apply Or.inr
  have turnSourcePresent := closed source sourcePresent
  have turnTurnSourcePresent := closed (turn source) turnSourcePresent
  have sourceNeTurn : source ≠ turn source := by
    exact fun equal => noFixed source sourcePresent equal.symm
  have tripleSubset : ({source, turn source, target} : Finset alpha) ⊆ items := by
    intro atom present
    simp only [Finset.mem_insert, Finset.mem_singleton] at present
    rcases present with rfl | rfl | rfl
    · exact sourcePresent
    · exact turnSourcePresent
    · exact targetPresent
  have tripleCard : ({source, turn source, target} : Finset alpha).card = 3 := by
    have sourceNeTarget : source ≠ target := Ne.symm targetSource
    have turnNeTarget : turn source ≠ target := Ne.symm targetTurn
    simp [sourceNeTurn, sourceNeTarget, turnNeTarget]
  have tripleEq : ({source, turn source, target} : Finset alpha) = items :=
    Finset.eq_of_subset_of_card_le tripleSubset (by omega)
  have turnTurnAlternative : turn (turn source) = source ∨
      turn (turn source) = turn source ∨ turn (turn source) = target := by
    simpa only [← tripleEq, Finset.mem_insert, Finset.mem_singleton] using
      turnTurnSourcePresent
  rcases turnTurnAlternative with turnTurnSource | turnTurnFixed | turnTurnTarget
  · exfalso
    have turnTargetPresent := closed target targetPresent
    have turnTargetAlternative : turn target = source ∨
        turn target = turn source ∨ turn target = target := by
      simpa only [← tripleEq, Finset.mem_insert, Finset.mem_singleton] using turnTargetPresent
    rcases turnTargetAlternative with turnTargetSource | turnTargetTurn | turnTargetFixed
    · exact targetTurn (injective target targetPresent (turn source) turnSourcePresent
        (turnTargetSource.trans turnTurnSource.symm))
    · exact targetSource (injective target targetPresent source sourcePresent turnTargetTurn)
    · exact noFixed target targetPresent turnTargetFixed
  · exact False.elim (noFixed (turn source) turnSourcePresent turnTurnFixed)
  · exact turnTurnTarget.symm

/-- From any incoming bonded dart, at most two local face turns reach a dart whose first endpoint
is any prescribed neighbor of the terminal atom.  The returned word has length at most four. -/
theorem molecularFullereneIncomingTurn_reaches_neighbor_bounded
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (incoming center target : MolecularFullereneCarrierAtom input)
    (incomingBond : 0 < molecule.bondOrder incoming.1 center.1)
    (targetBond : 0 < molecule.bondOrder target.1 center.1) :
    ∃ moves, moves.length ≤ 4 ∧
      (walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
        (incoming, center) moves).1 = target := by
  let neighbors := molecularFullereneCageNeighbors molecule input.carrier center.1
  have neighborCard : neighbors.card = 3 := oriented.1.cubic center.1 center.2
  have incomingPresent : incoming.1 ∈ neighbors := by
    simp [neighbors, molecularFullereneCageNeighbors, incoming.2, incomingBond,
      molecule.bondOrder_symm]
  have targetPresent : target.1 ∈ neighbors := by
    simp only [neighbors, molecularFullereneCageNeighbors, Finset.mem_filter]
    exact ⟨target.2, by simpa [molecule.bondOrder_symm] using targetBond⟩
  let turnNat : ℕ → ℕ := fun atom =>
    if member : atom ∈ input.carrier then
      (molecularFullereneIncomingTurn input ⟨atom, member⟩ center).1
    else atom
  have closed : ∀ atom ∈ neighbors, turnNat atom ∈ neighbors := by
    intro atom atomPresent
    have atomCarrier : atom ∈ input.carrier :=
      (Finset.mem_filter.mp atomPresent).1
    have atomBond : 0 < molecule.bondOrder atom center.1 := by
      simpa [molecule.bondOrder_symm] using (Finset.mem_filter.mp atomPresent).2
    simp only [turnNat, dif_pos atomCarrier]
    exact molecularFullereneIncomingTurn_mem_neighbors molecule input oriented
      ⟨atom, atomCarrier⟩ center atomBond
  have injective : ∀ first ∈ neighbors, ∀ second ∈ neighbors,
      turnNat first = turnNat second → first = second := by
    intro first firstPresent second secondPresent equal
    have firstCarrier := (Finset.mem_filter.mp firstPresent).1
    have secondCarrier := (Finset.mem_filter.mp secondPresent).1
    have firstBond : 0 < molecule.bondOrder first center.1 :=
      by simpa [molecule.bondOrder_symm] using (Finset.mem_filter.mp firstPresent).2
    have secondBond : 0 < molecule.bondOrder second center.1 :=
      by simpa [molecule.bondOrder_symm] using (Finset.mem_filter.mp secondPresent).2
    have typedEqual : molecularFullereneIncomingTurn input ⟨first, firstCarrier⟩ center =
        molecularFullereneIncomingTurn input ⟨second, secondCarrier⟩ center := by
      apply Subtype.ext
      simpa [turnNat, firstCarrier, secondCarrier] using equal
    exact congrArg Subtype.val
      (molecularFullereneIncomingTurn_injective_on_neighbors molecule input oriented center
        ⟨first, firstCarrier⟩ ⟨second, secondCarrier⟩ firstBond secondBond typedEqual)
  have noFixed : ∀ atom ∈ neighbors, turnNat atom ≠ atom := by
    intro atom atomPresent equal
    have atomCarrier := (Finset.mem_filter.mp atomPresent).1
    have atomBond : 0 < molecule.bondOrder atom center.1 :=
      by simpa [molecule.bondOrder_symm] using (Finset.mem_filter.mp atomPresent).2
    apply molecularFullereneIncomingTurn_ne molecule input oriented
      ⟨atom, atomCarrier⟩ center atomBond
    apply Subtype.ext
    simpa [turnNat, atomCarrier] using equal
  have alternatives := orbit_three_of_maps_injective_noFixed neighbors neighborCard turnNat
    closed injective noFixed incoming.1 target.1 incomingPresent targetPresent
  rcases alternatives with targetEq | targetEq | targetEq
  · exact ⟨[], by simp, by simpa using congrArg (fun atom : ℕ => atom) targetEq.symm⟩
  · refine ⟨[.continueLeftFace, .reverseEdge], by simp, ?_⟩
    apply Subtype.ext
    simpa [walkMolecularFullereneFlag, molecularFullereneFlagStep,
      molecularFullereneIncomingTurn, turnNat, incoming.2] using targetEq.symm
  · refine ⟨[.continueLeftFace, .reverseEdge,
      .continueLeftFace, .reverseEdge], by simp, ?_⟩
    have turnedPresent : (molecularFullereneIncomingTurn input incoming center).1 ∈
        input.carrier := (molecularFullereneIncomingTurn input incoming center).2
    apply Subtype.ext
    simpa [walkMolecularFullereneFlag, molecularFullereneFlagStep,
      molecularFullereneIncomingTurn, turnNat, incoming.2, turnedPresent] using targetEq.symm

/-- Compatibility projection of the bounded local neighbor route. -/
theorem molecularFullereneIncomingTurn_reaches_neighbor
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (incoming center target : MolecularFullereneCarrierAtom input)
    (incomingBond : 0 < molecule.bondOrder incoming.1 center.1)
    (targetBond : 0 < molecule.bondOrder target.1 center.1) :
    ∃ moves,
      (walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
        (incoming, center) moves).1 = target := by
  rcases molecularFullereneIncomingTurn_reaches_neighbor_bounded molecule input oriented
      incoming center target incomingBond targetBond with ⟨moves, _lengthBound, recovers⟩
  exact ⟨moves, recovers⟩

/-- A reached positive dart can advance to any bonded neighbor of its first endpoint.  Reversing
the dart exposes that endpoint as the local turn center; the cubic three-cycle theorem above then
selects the desired outgoing bond.  Its returned word has length at most five. -/
theorem walkMolecularFullereneFlag_reaches_bonded_neighbor_bounded
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (edgeBond : 0 < molecule.bondOrder edge.1.1 edge.2.1)
    (target : MolecularFullereneCarrierAtom input)
    (targetBond : 0 < molecule.bondOrder edge.1.1 target.1) :
    ∃ moves, moves.length ≤ 5 ∧
      (walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
        edge moves).1 = target := by
  have reversedBond : 0 < molecule.bondOrder edge.2.1 edge.1.1 := by
    simpa [molecule.bondOrder_symm] using edgeBond
  have targetIncomingBond : 0 < molecule.bondOrder target.1 edge.1.1 := by
    simpa [molecule.bondOrder_symm] using targetBond
  rcases molecularFullereneIncomingTurn_reaches_neighbor_bounded molecule input oriented
      edge.2 edge.1 target reversedBond targetIncomingBond with
    ⟨moves, lengthBound, recovers⟩
  exact ⟨.reverseEdge :: moves, by simp only [List.length_cons]; omega, recovers⟩

/-- Compatibility projection of the bounded reached-dart neighbor route. -/
theorem walkMolecularFullereneFlag_reaches_bonded_neighbor
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (edgeBond : 0 < molecule.bondOrder edge.1.1 edge.2.1)
    (target : MolecularFullereneCarrierAtom input)
    (targetBond : 0 < molecule.bondOrder edge.1.1 target.1) :
    ∃ moves,
      (walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
        edge moves).1 = target := by
  rcases walkMolecularFullereneFlag_reaches_bonded_neighbor_bounded molecule input oriented
      edge edgeBond target targetBond with ⟨moves, _lengthBound, recovers⟩
  exact ⟨moves, recovers⟩

/-- Every atom on a simple carrier path beginning at the first endpoint of a reached dart has a
flag word from that dart.  The induction carries a positive dart, not merely a vertex, so each
connected-path step composes directly with the local cubic-map theorem. -/
private theorem molecularFullereneFlagOrbit_reaches_carrierPath
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (edge : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (edgeBond : 0 < molecule.bondOrder edge.1.1 edge.2.1)
    (path : List ℕ)
    (pathNodup : path.Nodup)
    (pathCarrier : ∀ atom ∈ path, atom ∈ input.carrier)
    (pathHead : path.head? = some edge.1.1)
    (pathBonded : P94ConformationUnit.ConsecutivelyBonded molecule path) :
    ∀ atom ∈ path, ∃ moves,
      (walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
        edge moves).1.1 = atom := by
  induction path generalizing edge with
  | nil =>
      intro atom atomPresent
      simp at atomPresent
  | cons first rest inductionHypothesis =>
      have firstEq : first = edge.1.1 := by simpa using Option.some.inj pathHead
      intro atom atomPresent
      simp only [List.mem_cons] at atomPresent
      rcases atomPresent with atomFirst | atomRest
      · subst atom
        exact ⟨[], by simpa [walkMolecularFullereneFlag] using firstEq.symm⟩
      · cases rest with
        | nil => simp at atomRest
        | cons second tail =>
            have restNodup : (second :: tail).Nodup := pathNodup.tail
            have restCarrier : ∀ candidate ∈ second :: tail,
                candidate ∈ input.carrier := by
              intro candidate candidatePresent
              exact pathCarrier candidate (List.mem_cons_of_mem first candidatePresent)
            have firstNeSecond : first ≠ second := by
              have firstNotMem := (List.nodup_cons.mp pathNodup).1
              exact fun equal => firstNotMem (by simp [equal])
            have firstBonded : P94ConformationUnit.Bonded molecule first second := by
              apply pathBonded (first, second)
              simp
            have firstSecondBond : 0 < molecule.bondOrder first second :=
              (molecule.bondOrder_pos_iff_exists_bond firstNeSecond).mpr firstBonded
            let target : MolecularFullereneCarrierAtom input :=
              ⟨second, restCarrier second (by simp)⟩
            have edgeTargetBond : 0 < molecule.bondOrder edge.1.1 target.1 := by
              simpa [target, firstEq] using firstSecondBond
            rcases walkMolecularFullereneFlag_reaches_bonded_neighbor molecule input oriented
                edge edgeBond target edgeTargetBond with ⟨initialMoves, initialRecovers⟩
            let nextEdge := walkMolecularFullereneFlag
              (molecularFullereneContinueForwardFace input) edge initialMoves
            have nextEdgeBond : 0 < molecule.bondOrder nextEdge.1.1 nextEdge.2.1 := by
              have present := walkMolecularFullereneFlag_mem_reachableEdges molecule input
                oriented edge edgeBond initialMoves
              exact (mem_molecularFullereneFlagReachableEdges_sound molecule input edge
                edgeBond initialMoves.length nextEdge present).1
            have restHead : (second :: tail).head? = some nextEdge.1.1 := by
              simp only [List.head?_cons, Option.some.injEq]
              exact congrArg Subtype.val initialRecovers.symm
            have restBonded : P94ConformationUnit.ConsecutivelyBonded molecule
                (second :: tail) := by
              intro pair pairPresent
              apply pathBonded pair
              simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
              exact Or.inr pairPresent
            rcases inductionHypothesis nextEdge nextEdgeBond restNodup restCarrier restHead
                restBonded atom atomRest with ⟨suffix, suffixRecovers⟩
            refine ⟨initialMoves ++ suffix, ?_⟩
            rw [walkMolecularFullereneFlag_append]
            exact suffixRecovers

/-- The topology theorem: on the independently judged connected cubic oriented face map, the
reverse/forward-face orbit of *any* positive source dart reaches every carrier atom.  There is no
spanning assumption and no address family in this statement. -/
theorem orientedMolecularFullereneFaceMap_flagOrbitCoversCarrier
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1) :
    MolecularFullereneFlagOrbitCoversCarrier input source := by
  intro atom
  rcases oriented.1.connected.2 source.1.1 source.1.2 atom.1 atom.2 with
    ⟨path, pathNodup, pathCarrier, pathHead, pathLast, pathBonded⟩
  have pathNe : path ≠ [] := by
    intro empty
    simp [empty] at pathHead
  have targetInPath : atom.1 ∈ path := by
    have lastEq : path.getLast pathNe = atom.1 := by
      apply Option.some.inj
      rw [← pathLast]
      exact (List.getLast?_eq_getLast_of_ne_nil pathNe).symm
    rw [← lastEq]
    exact List.getLast_mem pathNe
  rcases molecularFullereneFlagOrbit_reaches_carrierPath molecule input oriented source
      sourceBond path pathNodup pathCarrier pathHead pathBonded atom.1 targetInPath with
    ⟨moves, recovers⟩
  refine ⟨moves, ?_⟩
  apply Subtype.ext
  exact recovers

/-- The complete mathematical collapse: an independently judged oriented fullerene map and one
positive source dart construct the deduplicated spanning certificate.  The former `spanning`
field is now a consequence of cubic local topology plus carrier connectedness. -/
def MolecularFullereneDeduplicatedFlagSpanningCertificate.ofOrientedFaceMap
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1) :
    MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input where
  oriented := oriented
  source := source
  sourceBond := sourceBond
  spanning := molecularFullereneFlagOrbitCoversCarrier_to_deduplicatedSpanning molecule input
    oriented source sourceBond
      (orientedMolecularFullereneFaceMap_flagOrbitCoversCarrier molecule input oriented
        source sourceBond)

/-- Once topology supplies orbit coverage, no checked spanning field remains: the bounded
deduplicated certificate is constructed as a theorem. -/
def MolecularFullereneDeduplicatedFlagSpanningCertificate.ofOrbitCoverage
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (source : MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input)
    (sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1)
    (covers : MolecularFullereneFlagOrbitCoversCarrier input source) :
    MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input where
  oriented := oriented
  source := source
  sourceBond := sourceBond
  spanning := molecularFullereneFlagOrbitCoversCarrier_to_deduplicatedSpanning molecule input
    oriented source sourceBond covers

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.walkMolecularFullereneFlag_mem_reachableEdges_at_stateBound
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneFlagOrbitCoversCarrier_to_deduplicatedSpanning
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneIncomingTurn_reaches_neighbor
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneIncomingTurn_reaches_neighbor_bounded
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.walkMolecularFullereneFlag_reaches_bonded_neighbor_bounded
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.orientedMolecularFullereneFaceMap_flagOrbitCoversCarrier
