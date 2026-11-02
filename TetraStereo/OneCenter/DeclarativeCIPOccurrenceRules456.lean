import TetraStereo.UniversalProof.NextFrontier.FramedOrdinaryConformance
import TetraStereo.OneCenter.Rule6PartitionGroupCount
import TetraStereo.OneCenter.DeclarativeCIPOccurrenceScheduler
import TetraStereo.OneCenter.ProductionCIPOccurrenceDiscovery
import TetraStereo.OneCenter.ProductionCIPOccurrenceDescriptorComparatorLaws
import TetraStereo.OneCenter.ProductionCIPLinearOccurrenceComparatorCompleteness
import TetraStereo.OneCenter.ProductionCIPBranchingOccurrenceComparatorCompleteness
import TetraStereo.OneCenter.ProductionCIPDescriptorBranchingCompleteness
import TetraStereo.OneCenter.ProductionRule6Certificate

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

/-!
# Executable Rules 4b, 5, and 6 on production occurrences

The state in this module is indexed by the composite production occurrence `(final center root,
center-relative address)`.  It is never flattened across roots.  A single-root translation to the
legacy executable fact list checks every active insertion and rejects a duplicate legacy key,
rather than allowing lookup order to collapse two coordinates.

Ordinary auxiliary labels are computed by the production occurrence comparator over an explicit
four-ligand cursor frame.  Rule 6 is the full four-ligand reference-promotion calculation: it first
forms the Rules-1--5 partition, checks the odd-automorphism gate, and then certifies either all
admissible references of a two-group carrier or both promoted orders of the four-way carrier.
-/

namespace ProductionOccurrenceRules456

open ProductionCIPOccurrenceDiscovery
open ProductionCIPOccurrenceDescriptorComparatorLaws
open ProductionCIPRerootComparatorLaws
open ProductionCIPLinearOccurrenceComparatorCompleteness
open ProductionCIPBranchingOccurrenceComparatorCompleteness
open ProductionCIPDescriptorBranchingCompleteness

variable {mol : RawMolecule}

abbrev Occurrence (discovery : Discovery mol) :=
  ProductionCIPOccurrenceDiscovery.Occurrence discovery

/-- Descriptor sense carried explicitly by a computed production label. -/
def descriptorSense : Descriptor → DescriptorSense
  | .R | .r | .Ra | .Rp | .M | .E | .seqCis => .senior
  | .S | .s | .Sa | .Sp | .P | .Z | .seqTrans => .junior

/-- Proof that a label's complete ranking payload was produced at its exact root-relative frame.

Inner labels must be literal successful results of the production `occurrenceFact?` evaluator.
Rule 6 is a final-center rule, so its labels carry the proof that their frame is the discovered
final occurrence; their complete carrier computation is then required by `Rule6Derivation` before
such a label can occur in a model.  Because this evidence is a proposition, it is erased from the
executable state while still preventing construction of unchecked auxiliary payloads. -/
inductive RankingEvidence (discovery : Discovery mol) (occurrence : Occurrence discovery)
    (fact : OccurrenceAuxFact) : Prop
  | ordinary (fuel : Nat) (aux : OneCenter.OccurrenceAuxState)
      (computed : occurrence.sourceNode?.bind (occurrenceFact? mol fuel aux) = some fact) :
      RankingEvidence discovery occurrence fact
  | final (marker : Unit) (frame_eq : occurrence.node = Sum.inl marker) :
      RankingEvidence discovery occurrence fact

/-- A production label retains the exact executable fact, descriptor sense, exact occurrence
frame, and proof that its ranking payload is legitimate at that frame. -/
structure Label (discovery : Discovery mol) where
  occurrence : Occurrence discovery
  fact : OccurrenceAuxFact
  descriptor : Descriptor
  sense : DescriptorSense
  sense_eq : sense = descriptorSense descriptor
  rankingEvidence : RankingEvidence discovery occurrence fact

/-- A total occurrence state.  `none` is the resolved absence of an auxiliary label, not a
missing entry in a partial list. -/
abbrev State (discovery : Discovery mol) := Occurrence discovery → Option (Label discovery)

/-- Executable source lookup succeeds for every exhaustively discovered occurrence. -/
theorem sourceNode?_isSome (discovery : Discovery mol) (occurrence : Occurrence discovery) :
    occurrence.sourceNode?.isSome = true := by
  rw [Option.isSome_iff_exists]
  exact occurrence.source_exists

/-- Read the source node from the exact executable lookup. -/
def sourceNode (discovery : Discovery mol) (occurrence : Occurrence discovery) :
    RawMolecule.CanonicalBranchNode :=
  occurrence.sourceNode?.get (sourceNode?_isSome discovery occurrence)

theorem sourceNode_spec (discovery : Discovery mol) (occurrence : Occurrence discovery) :
    occurrence.sourceNode? = some (sourceNode discovery occurrence) :=
  (Option.some_get (sourceNode?_isSome discovery occurrence)).symm

/-- Executable two-point descriptor sense. -/
def senseToRS : DescriptorSense → RS
  | .senior => .R
  | .junior => .S

/-- Declarative spelling of an executable occurrence fact. -/
def descriptorOfFact (fact : OccurrenceAuxFact) : Descriptor :=
  match fact.uppercase, fact.descriptor with
  | true, .R => .R
  | true, .S => .S
  | false, .R => .r
  | false, .S => .s

@[simp] theorem descriptorOfFact_sense (fact : OccurrenceAuxFact) :
    descriptorSense (descriptorOfFact fact) =
      match fact.descriptor with
      | .R => .senior
      | .S => .junior := by
  rcases fact with ⟨key, atom, descriptor, uppercase, positions⟩
  cases uppercase <;> cases descriptor <;> rfl

/-- Construct an inner label only from a literal production `occurrenceFact?` result. -/
def labelOfOrdinaryFact (discovery : Discovery mol) (target : Occurrence discovery)
    (fact : OccurrenceAuxFact) (fuel : Nat) (aux : OneCenter.OccurrenceAuxState)
    (computed : target.sourceNode?.bind (occurrenceFact? mol fuel aux) = some fact) :
    Label discovery :=
  { occurrence := target
    fact := fact
    descriptor := descriptorOfFact fact
    sense := match fact.descriptor with | .R => .senior | .S => .junior
    sense_eq := descriptorOfFact_sense fact |>.symm
    rankingEvidence := .ordinary fuel aux computed }

/-- Construct a Rule-6 label only at the discovered final occurrence. -/
def labelOfFinalFact (discovery : Discovery mol) (target : Occurrence discovery)
    (fact : OccurrenceAuxFact) (marker : Unit) (frame_eq : target.node = Sum.inl marker) :
    Label discovery :=
  { occurrence := target
    fact := fact
    descriptor := descriptorOfFact fact
    sense := match fact.descriptor with | .R => .senior | .S => .junior
    sense_eq := descriptorOfFact_sense fact |>.symm
    rankingEvidence := .final marker frame_eq }

@[simp] theorem labelOfFact_rankingEvidence (discovery : Discovery mol)
    (target : Occurrence discovery) (fact : OccurrenceAuxFact)
    (fuel : Nat) (aux : OneCenter.OccurrenceAuxState)
    (computed : target.sourceNode?.bind (occurrenceFact? mol fuel aux) = some fact) :
    (labelOfOrdinaryFact discovery target fact fuel aux computed).fact = fact :=
  rfl

@[simp] theorem labelOfFact_referenceFrame (discovery : Discovery mol)
    (target : Occurrence discovery) (fact : OccurrenceAuxFact)
    (fuel : Nat) (aux : OneCenter.OccurrenceAuxState)
    (computed : target.sourceNode?.bind (occurrenceFact? mol fuel aux) = some fact) :
    (labelOfOrdinaryFact discovery target fact fuel aux computed).occurrence = target :=
  rfl

/-! ## One-root collision-safe executable state -/

/-- Turn one deduplicated hierarchy address into its exact slot-indexed production occurrence. -/
def branchOccurrenceAtAddress (discovery : Discovery mol) (root : Root mol) (slot : Fin 4)
    (node : { address : List Nat //
      address ∈ ((discovery.center root).branch slot).key.hierarchyAddresses.dedup }) :
    Occurrence discovery :=
  let originalNode :
      (((discovery.center root).branch slot).key.toDeclarativeDigraph mol).Node :=
    ⟨node.1, List.dedup_subset _ node.2⟩
  { root := root
    node := branchNode (discovery.center root) slot originalNode }

@[simp] theorem branchOccurrenceAtAddress_address (discovery : Discovery mol)
    (root : Root mol) (slot : Fin 4)
    (node : { address : List Nat //
      address ∈ ((discovery.center root).branch slot).key.hierarchyAddresses.dedup }) :
    (branchOccurrenceAtAddress discovery root slot node).address = slot.val :: node.1 :=
  rfl

/-- Enumerate the deduplicated occurrence family in one ligand slot. -/
def occurrencesAtSlot (discovery : Discovery mol) (root : Root mol) (slot : Fin 4) :
    List (Occurrence discovery) :=
  ((discovery.center root).branch slot).key.hierarchyAddresses.dedup.attach.map
    (branchOccurrenceAtAddress discovery root slot)

/-- Enumerate every composite occurrence below one center root. -/
def occurrencesAtRoot (discovery : Discovery mol) (root : Root mol) :
    List (Occurrence discovery) :=
  finalOccurrence discovery root ::
    (List.finRange 4).flatMap (occurrencesAtSlot discovery root)

/-- The executable four-slot enumeration in its exact production order. -/
theorem occurrencesAtRoot_four_slots (discovery : Discovery mol) (root : Root mol) :
    occurrencesAtRoot discovery root =
      finalOccurrence discovery root ::
        (occurrencesAtSlot discovery root ⟨0, by decide⟩ ++
          occurrencesAtSlot discovery root ⟨1, by decide⟩ ++
          occurrencesAtSlot discovery root ⟨2, by decide⟩ ++
          occurrencesAtSlot discovery root ⟨3, by decide⟩) := by
  simp [occurrencesAtRoot, List.finRange]

theorem branchOccurrenceAtAddress_injective (discovery : Discovery mol)
    (root : Root mol) (slot : Fin 4) :
    Function.Injective (branchOccurrenceAtAddress discovery root slot) := by
  intro left right equal
  apply Subtype.ext
  have addressEqual := congrArg Occurrence.address equal
  change slot.val :: left.1 = slot.val :: right.1 at addressEqual
  exact (List.cons.inj addressEqual).2

theorem occurrencesAtSlot_nodup (discovery : Discovery mol) (root : Root mol)
    (slot : Fin 4) :
    (occurrencesAtSlot discovery root slot).Nodup := by
  unfold occurrencesAtSlot
  exact ((List.nodup_dedup _).attach).map
    (branchOccurrenceAtAddress_injective discovery root slot)

theorem occurrencesAtSlot_disjoint (discovery : Discovery mol) (root : Root mol)
    {left right : Fin 4} (different : left ≠ right) :
    List.Disjoint (occurrencesAtSlot discovery root left)
      (occurrencesAtSlot discovery root right) := by
  rw [List.disjoint_left]
  intro occurrence leftMember rightMember
  unfold occurrencesAtSlot at leftMember rightMember
  rcases List.mem_map.mp leftMember with ⟨leftNode, _, leftEqual⟩
  rcases List.mem_map.mp rightMember with ⟨rightNode, _, rightEqual⟩
  have addressEqual := congrArg Occurrence.address (leftEqual.trans rightEqual.symm)
  have slotEqual : left.val = right.val :=
    (List.cons.inj (by simpa using addressEqual)).1
  exact different (Fin.ext slotEqual)

/-- Per-address deduplication is sufficient for the complete one-root family: addresses within a
slot are unique, slot prefixes separate different branches, and the center's empty address cannot
equal any branch address. -/
theorem occurrencesAtRoot_nodup (discovery : Discovery mol) (root : Root mol) :
    (occurrencesAtRoot discovery root).Nodup := by
  have branchesNodup :
      ((List.finRange 4).flatMap (occurrencesAtSlot discovery root)).Nodup := by
    rw [List.nodup_flatMap]
    constructor
    · intro slot _
      exact occurrencesAtSlot_nodup discovery root slot
    · exact (List.nodup_finRange 4).imp fun {left right} different =>
        occurrencesAtSlot_disjoint discovery root different
  rw [occurrencesAtRoot, List.nodup_cons]
  constructor
  · intro centerMember
    rw [List.mem_flatMap] at centerMember
    rcases centerMember with ⟨slot, _, slotMember⟩
    unfold occurrencesAtSlot at slotMember
    rcases List.mem_map.mp slotMember with ⟨node, _, equal⟩
    have addressEqual := congrArg Occurrence.address equal
    simp at addressEqual
  · exact branchesNodup

/-- The executable root enumeration is exact: it contains every occurrence over `root`, and no
occurrence over another root.  Together with `occurrencesAtRoot_nodup`, this rules out both
omission and duplication in the local production traversal. -/
theorem mem_occurrencesAtRoot_iff (discovery : Discovery mol) (root : Root mol)
    (occurrence : Occurrence discovery) :
    occurrence ∈ occurrencesAtRoot discovery root ↔ occurrence.root = root := by
  constructor
  · intro member
    rw [occurrencesAtRoot, List.mem_cons] at member
    rcases member with centerEqual | branchMember
    · simpa using congrArg (fun current : Occurrence discovery => current.root) centerEqual
    · rw [List.mem_flatMap] at branchMember
      rcases branchMember with ⟨slot, _, slotMember⟩
      unfold occurrencesAtSlot at slotMember
      rcases List.mem_map.mp slotMember with ⟨node, _, occurrenceEqual⟩
      exact (congrArg (fun current : Occurrence discovery => current.root) occurrenceEqual).symm
  · intro rootEqual
    rcases occurrence with ⟨occurrenceRoot, node⟩
    dsimp only at rootEqual
    subst occurrenceRoot
    rcases node with marker | branch
    · apply List.mem_cons.mpr
      apply Or.inl
      apply ProductionCIPOccurrenceDiscovery.Occurrence.eq_of_root_eq_address_eq
      · rfl
      · rfl
    · rcases branch with ⟨slot, node⟩
      apply List.mem_cons_of_mem
      rw [List.mem_flatMap]
      refine ⟨slot, by simp, ?_⟩
      unfold occurrencesAtSlot
      apply List.mem_map.mpr
      let deduplicatedNode :
          { address : List Nat //
            address ∈ ((discovery.center root).branch slot).key.hierarchyAddresses.dedup } :=
        ⟨node.1, List.mem_dedup.mpr node.2⟩
      refine ⟨deduplicatedNode, by simp [deduplicatedNode], ?_⟩
      apply ProductionCIPOccurrenceDiscovery.Occurrence.eq_of_root_eq_address_eq
      · rfl
      · rfl

/-- Only real tetrahedral occurrences can carry an auxiliary fact. -/
def labelCapable (discovery : Discovery mol) (occurrence : Occurrence discovery) : Bool :=
  let source := sourceNode discovery occurrence
  source.provenance == RawMolecule.CanonicalNodeProvenance.realAtom &&
    (mol.atomAt? source.atom).any fun spec => spec.tetrahedral?.isSome

/-- Canonical executable lookup key of one exact root-relative occurrence. -/
def factKey (discovery : Discovery mol) (occurrence : Occurrence discovery) :
    CanonicalOccurrenceKey :=
  canonicalOccurrenceKey (sourceNode discovery occurrence)

/-- A previously resolved label contributes exactly its certified fact.  Resolved `none` produces
no fact; unlike the rejected implementation, there is no separate missing-state interpretation. -/
def inputFact? {discovery : Discovery mol} (state : State discovery)
    (occurrence : Occurrence discovery) :
    Option OccurrenceAuxFact :=
  match state occurrence with
  | none => none
  | some label =>
      if label.occurrence.root.1 == occurrence.root.1 &&
          label.occurrence.address == occurrence.address &&
          label.fact.key == factKey discovery occurrence &&
          label.fact.atom == (sourceNode discovery occurrence).atom &&
          label.descriptor == descriptorOfFact label.fact &&
          label.sense == descriptorSense label.descriptor then
        some label.fact
      else none

theorem inputFact?_some_valid {discovery : Discovery mol} (state : State discovery)
    (occurrence : Occurrence discovery) (fact : OccurrenceAuxFact)
    (accepted : inputFact? state occurrence = some fact) :
    ∃ label, state occurrence = some label ∧
      label.occurrence.root = occurrence.root ∧
      label.occurrence.address = occurrence.address ∧
      label.fact = fact ∧
      fact.key = factKey discovery occurrence ∧
      fact.atom = (sourceNode discovery occurrence).atom ∧
      label.descriptor = descriptorOfFact fact := by
  cases stateEq : state occurrence with
  | none => simp [inputFact?, stateEq] at accepted
  | some label =>
    simp only [inputFact?, stateEq] at accepted
    split at accepted
    · rename_i valid
      simp only [Bool.and_eq_true, beq_iff_eq] at valid
      rcases valid with ⟨⟨⟨⟨⟨rootEq, addressEq⟩, keyEq⟩, atomEq⟩, descriptorEq⟩, _⟩
      have factEq := Option.some.inj accepted
      subst fact
      exact ⟨label, rfl, Subtype.ext rootEq, addressEq, rfl, keyEq, atomEq, descriptorEq⟩
    · simp at accepted

theorem inputFact?_eq_of_state_eq {discovery : Discovery mol}
    {left right : State discovery} (occurrence : Occurrence discovery)
    (agree : left occurrence = right occurrence) :
    inputFact? left occurrence = inputFact? right occurrence := by
  unfold inputFact?
  rw [agree]

/-- Strict dependency direction used by production evaluation: only deeper occurrences in the
same center-rooted hierarchy can be consulted while deriving the target. -/
def DepthDependency {discovery : Discovery mol}
    (source target : Occurrence discovery) : Prop :=
  source.root = target.root ∧ target.address.length < source.address.length

instance {discovery : Discovery mol} (source target : Occurrence discovery) :
    Decidable (DepthDependency source target) := by
  unfold DepthDependency
  infer_instance

/-- A strict predecessor can never be a final-frame-only label.  Therefore every active fact that
may actually be consumed by another occurrence carries a literal production `occurrenceFact?`
certificate, including its uppercase flag and complete priority positions. -/
theorem RankingEvidence.ordinary_of_dependency {discovery : Discovery mol}
    {source target : Occurrence discovery} {fact : OccurrenceAuxFact}
    (evidence : RankingEvidence discovery source fact)
    (dependency : DepthDependency source target) :
    ∃ fuel aux, source.sourceNode?.bind (occurrenceFact? mol fuel aux) = some fact := by
  cases evidence with
  | ordinary fuel aux computed => exact ⟨fuel, aux, computed⟩
  | final marker frameEq =>
      have sourceAddress : source.address = [] := by
        rcases source with ⟨root, node⟩
        simp only at frameEq
        subst node
        rfl
      have depth := dependency.2
      rw [sourceAddress] at depth
      exact (Nat.not_lt_zero _ depth).elim

theorem inputFact?_some_production_certified {discovery : Discovery mol}
    (state : State discovery) (source target : Occurrence discovery)
    (fact : OccurrenceAuxFact) (dependency : DepthDependency source target)
    (accepted : inputFact? state source = some fact) :
    ∃ fuel aux, source.sourceNode?.bind (occurrenceFact? mol fuel aux) = some fact := by
  rcases inputFact?_some_valid state source fact accepted with
    ⟨label, _, rootEq, addressEq, factEq, _, _, _⟩
  have occurrenceEq : label.occurrence = source :=
    ProductionCIPOccurrenceDiscovery.Occurrence.eq_of_root_eq_address_eq
      label.occurrence source rootEq addressEq
  subst source
  subst fact
  exact label.rankingEvidence.ordinary_of_dependency dependency

/-- Insert one active fact only when its legacy key is new.  Equal keys are rejected, never
collapsed by `factAt?` lookup order. -/
def appendInputFact? (facts : OneCenter.OccurrenceAuxState) (fact : OccurrenceAuxFact) :
    Option OneCenter.OccurrenceAuxState :=
  if facts.any fun existing => existing.key == fact.key then none
  else some (facts ++ [fact])

/-- Translate the active strict predecessors of one target.  A resolved `none` cell contributes
no fact.  A malformed active `some` cell or a second active occurrence with the same legacy key
rejects the whole translation instead of being silently dropped or collapsed. -/
def encodeOccurrenceFacts? (discovery : Discovery mol) (state : State discovery)
    (target : Occurrence discovery) :
    List (Occurrence discovery) → OneCenter.OccurrenceAuxState →
      Option OneCenter.OccurrenceAuxState
  | [], facts => some facts
  | occurrence :: occurrences, facts =>
      if DepthDependency occurrence target then
        match state occurrence with
        | none => encodeOccurrenceFacts? discovery state target occurrences facts
        | some _label =>
            if labelCapable discovery occurrence then
              match inputFact? state occurrence with
              | none => none
              | some fact =>
                  match appendInputFact? facts fact with
                  | none => none
                  | some next => encodeOccurrenceFacts? discovery state target occurrences next
            else none
      else encodeOccurrenceFacts? discovery state target occurrences facts

/-- A list containing only resolved-`none` coordinates leaves the accumulated executable facts
unchanged.  This is the structural replacement for reducing a concrete full occurrence family. -/
theorem encodeOccurrenceFacts?_all_none (discovery : Discovery mol) (state : State discovery)
    (target : Occurrence discovery) (occurrences : List (Occurrence discovery))
    (facts : OneCenter.OccurrenceAuxState)
    (inactive : ∀ occurrence, occurrence ∈ occurrences → state occurrence = none) :
    encodeOccurrenceFacts? discovery state target occurrences facts = some facts := by
  induction occurrences generalizing facts with
  | nil => rfl
  | cons occurrence occurrences inductionHypothesis =>
      have headNone : state occurrence = none := inactive occurrence (by simp)
      have tailNone : ∀ other, other ∈ occurrences → state other = none := by
        intro other member
        exact inactive other (by simp [member])
      by_cases depends : DepthDependency occurrence target
      · simpa [encodeOccurrenceFacts?, depends, headNone] using
          inductionHypothesis facts tailNone
      · simpa [encodeOccurrenceFacts?, depends] using
          inductionHypothesis facts tailNone

/-- An inactive prefix can be removed without changing either the accumulator or the remaining
encoding problem. -/
theorem encodeOccurrenceFacts?_skip_inactive_prefix
    (discovery : Discovery mol) (state : State discovery)
    (target : Occurrence discovery) (initial remaining : List (Occurrence discovery))
    (facts : OneCenter.OccurrenceAuxState)
    (inactive : ∀ occurrence, occurrence ∈ initial → state occurrence = none) :
    encodeOccurrenceFacts? discovery state target (initial ++ remaining) facts =
      encodeOccurrenceFacts? discovery state target remaining facts := by
  induction initial generalizing facts with
  | nil => rfl
  | cons occurrence initial inductionHypothesis =>
      have headNone : state occurrence = none := inactive occurrence (by simp)
      have tailNone : ∀ other, other ∈ initial → state other = none := by
        intro other member
        exact inactive other (by simp [member])
      by_cases depends : DepthDependency occurrence target
      · simpa [encodeOccurrenceFacts?, depends, headNone] using
          inductionHypothesis facts tailNone
      · simpa [encodeOccurrenceFacts?, depends] using
          inductionHypothesis facts tailNone

/-- If a duplicate-free occurrence list has exactly one active, dependency-relevant, label-capable
coordinate and that coordinate validates to `fact`, encoding from the empty accumulator returns
the singleton fact list.  The proof traverses the list and never evaluates a concrete molecule. -/
theorem encodeOccurrenceFacts?_singleton_active_on_list
    (discovery : Discovery mol) (state : State discovery)
    (target source : Occurrence discovery) (fact : OccurrenceAuxFact)
    (occurrences : List (Occurrence discovery))
    (nodup : occurrences.Nodup) (sourceMember : source ∈ occurrences)
    (dependency : DepthDependency source target)
    (capable : labelCapable discovery source = true)
    (accepted : inputFact? state source = some fact)
    (inactive : ∀ occurrence, occurrence ≠ source → state occurrence = none) :
    encodeOccurrenceFacts? discovery state target occurrences [] = some [fact] := by
  induction occurrences with
  | nil => simp at sourceMember
  | cons occurrence occurrences inductionHypothesis =>
      have nodupParts := List.nodup_cons.mp nodup
      rcases List.mem_cons.mp sourceMember with headEqual | tailMember
      · subst occurrence
        have tailNone : ∀ other, other ∈ occurrences → state other = none := by
          intro other member
          apply inactive other
          intro equal
          subst other
          exact nodupParts.1 member
        have tailResult :=
          encodeOccurrenceFacts?_all_none discovery state target occurrences [fact] tailNone
        cases sourceState : state source with
        | none =>
            have rejected : inputFact? state source = none := by
              simp [inputFact?, sourceState]
            rw [rejected] at accepted
            cases accepted
        | some label =>
            simpa [encodeOccurrenceFacts?, dependency, sourceState, capable, accepted,
              appendInputFact?] using tailResult
      · have headDifferent : occurrence ≠ source := by
          intro equal
          subst occurrence
          exact nodupParts.1 tailMember
        have headNone := inactive occurrence headDifferent
        have tailResult := inductionHypothesis nodupParts.2 tailMember
        by_cases headDependency : DepthDependency occurrence target
        · simpa [encodeOccurrenceFacts?, headDependency, headNone] using tailResult
        · simpa [encodeOccurrenceFacts?, headDependency] using tailResult

/-- Root-family specialization of `encodeOccurrenceFacts?_singleton_active_on_list`. -/
theorem encodeOccurrenceFacts?_singleton_active
    (discovery : Discovery mol) (state : State discovery)
    (target source : Occurrence discovery) (fact : OccurrenceAuxFact)
    (nodup : (occurrencesAtRoot discovery target.root).Nodup)
    (sourceMember : source ∈ occurrencesAtRoot discovery target.root)
    (dependency : DepthDependency source target)
    (capable : labelCapable discovery source = true)
    (accepted : inputFact? state source = some fact)
    (inactive : ∀ occurrence, occurrence ≠ source → state occurrence = none) :
    encodeOccurrenceFacts? discovery state target
      (occurrencesAtRoot discovery target.root) [] = some [fact] :=
  encodeOccurrenceFacts?_singleton_active_on_list discovery state target source fact
    (occurrencesAtRoot discovery target.root) nodup sourceMember dependency capable accepted inactive

/-- Two validated active coordinates are encoded in their occurrence-list order.  The explicit
decomposition prevents a proof from silently assuming an order unrelated to production discovery. -/
theorem encodeOccurrenceFacts?_two_active_on_list
    (discovery : Discovery mol) (state : State discovery)
    (target first second : Occurrence discovery) (firstFact secondFact : OccurrenceAuxFact)
    (occurrences before between after : List (Occurrence discovery))
    (decomposition : occurrences = before ++ (first :: (between ++ (second :: after))))
    (nodup : occurrences.Nodup)
    (firstDependency : DepthDependency first target)
    (secondDependency : DepthDependency second target)
    (firstCapable : labelCapable discovery first = true)
    (secondCapable : labelCapable discovery second = true)
    (firstAccepted : inputFact? state first = some firstFact)
    (secondAccepted : inputFact? state second = some secondFact)
    (keysDistinct : firstFact.key ≠ secondFact.key)
    (inactive : ∀ occurrence, occurrence ≠ first → occurrence ≠ second →
      state occurrence = none) :
    encodeOccurrenceFacts? discovery state target occurrences [] =
      some [firstFact, secondFact] := by
  subst occurrences
  have beforeDisjoint : List.Disjoint before (first :: between ++ second :: after) :=
    nodup.disjoint
  have tailNodup : (first :: between ++ second :: after).Nodup :=
    nodup.of_append_right
  have firstParts := List.nodup_cons.mp tailNodup
  have betweenSecondNodup : (between ++ second :: after).Nodup := firstParts.2
  have betweenDisjoint : List.Disjoint between (second :: after) :=
    betweenSecondNodup.disjoint
  have secondAfterNodup : (second :: after).Nodup :=
    betweenSecondNodup.of_append_right
  have secondParts := List.nodup_cons.mp secondAfterNodup
  have beforeInactive : ∀ occurrence, occurrence ∈ before → state occurrence = none := by
    intro occurrence member
    apply inactive occurrence
    · intro equal
      subst occurrence
      exact (List.disjoint_left.mp beforeDisjoint member (by simp)).elim
    · intro equal
      subst occurrence
      exact (List.disjoint_left.mp beforeDisjoint member (by simp)).elim
  have betweenInactive : ∀ occurrence, occurrence ∈ between → state occurrence = none := by
    intro occurrence member
    apply inactive occurrence
    · intro equal
      subst occurrence
      exact (firstParts.1 (by simp [member])).elim
    · intro equal
      subst occurrence
      exact (List.disjoint_left.mp betweenDisjoint member (by simp)).elim
  have afterInactive : ∀ occurrence, occurrence ∈ after → state occurrence = none := by
    intro occurrence member
    apply inactive occurrence
    · intro equal
      subst occurrence
      exact (firstParts.1 (by simp [member])).elim
    · intro equal
      subst occurrence
      exact (secondParts.1 member).elim
  change encodeOccurrenceFacts? discovery state target
    (before ++ (first :: (between ++ (second :: after)))) [] = some [firstFact, secondFact]
  calc
    _ = encodeOccurrenceFacts? discovery state target
        (first :: (between ++ (second :: after))) [] :=
      encodeOccurrenceFacts?_skip_inactive_prefix discovery state target before
        (first :: (between ++ (second :: after))) [] beforeInactive
    _ = some [firstFact, secondFact] := by
      simp only [encodeOccurrenceFacts?, firstDependency]
      have firstState : ∃ label, state first = some label := by
        unfold inputFact? at firstAccepted
        cases equation : state first with
        | none => simp [equation] at firstAccepted
        | some label => exact ⟨label, rfl⟩
      rcases firstState with ⟨firstLabel, firstState⟩
      simp only [firstState, firstCapable, firstAccepted, appendInputFact?, List.any_nil,
        ↓reduceIte]
      calc
        _ = encodeOccurrenceFacts? discovery state target (second :: after) [firstFact] :=
          encodeOccurrenceFacts?_skip_inactive_prefix discovery state target between
            (second :: after) [firstFact] betweenInactive
        _ = some [firstFact, secondFact] := by
          simp only [encodeOccurrenceFacts?, secondDependency]
          have secondState : ∃ label, state second = some label := by
            unfold inputFact? at secondAccepted
            cases equation : state second with
            | none => simp [equation] at secondAccepted
            | some label => exact ⟨label, rfl⟩
          rcases secondState with ⟨secondLabel, secondState⟩
          simp only [secondState, secondCapable, secondAccepted, appendInputFact?,
            List.any_cons, List.any_nil, Bool.or_false, beq_iff_eq, keysDistinct,
            ↓reduceIte]
          exact encodeOccurrenceFacts?_all_none discovery state target after
            [firstFact, secondFact] afterInactive

/-- Encode exactly one target's active strict predecessors. -/
def executableStateFor? (discovery : Discovery mol) (state : State discovery)
    (target : Occurrence discovery) : Option OneCenter.OccurrenceAuxState :=
  encodeOccurrenceFacts? discovery state target
    (occurrencesAtRoot discovery target.root) []

/-- `executableStateFor?` traverses exactly the complete occurrence carrier over the target root.
The encoder subsequently selects the strict-depth dependencies from this exhaustive, duplicate-free
family; no caller can omit a rooted occurrence or introduce a duplicate. -/
theorem executableStateFor?_complete_root_traversal (discovery : Discovery mol)
    (state : State discovery) (target : Occurrence discovery) :
    executableStateFor? discovery state target =
        encodeOccurrenceFacts? discovery state target
          (occurrencesAtRoot discovery target.root) [] ∧
      (occurrencesAtRoot discovery target.root).Nodup ∧
      ∀ occurrence,
        occurrence ∈ occurrencesAtRoot discovery target.root ↔
          occurrence.root = target.root := by
  exact ⟨rfl, occurrencesAtRoot_nodup discovery target.root,
    mem_occurrencesAtRoot_iff discovery target.root⟩

theorem executableStateFor?_eq_of_depth_agree (discovery : Discovery mol)
    {left right : State discovery} (target : Occurrence discovery)
    (agree : ∀ source, DepthDependency source target → left source = right source) :
    executableStateFor? discovery left target = executableStateFor? discovery right target := by
  unfold executableStateFor?
  generalize occurrencesAtRoot discovery target.root = occurrences
  suffices ∀ facts,
      encodeOccurrenceFacts? discovery left target occurrences facts =
        encodeOccurrenceFacts? discovery right target occurrences facts by
    exact this []
  intro facts
  induction occurrences generalizing facts with
  | nil => rfl
  | cons occurrence occurrences inductionHypothesis =>
      by_cases dependency : DepthDependency occurrence target
      · have stateEq := agree occurrence dependency
        have factEq := inputFact?_eq_of_state_eq occurrence stateEq
        cases stateRight : right occurrence with
        | none =>
            simpa [encodeOccurrenceFacts?, dependency, stateEq, stateRight] using
              inductionHypothesis facts
        | some label =>
            by_cases capable : labelCapable discovery occurrence = true
            · cases factRight : inputFact? right occurrence with
              | none =>
                  simp [encodeOccurrenceFacts?, dependency, stateEq, stateRight, capable,
                    factEq, factRight]
              | some fact =>
                  cases appendEq : appendInputFact? facts fact with
                  | none =>
                      simp [encodeOccurrenceFacts?, dependency, stateEq, stateRight, capable,
                        factEq, factRight, appendEq]
                  | some next =>
                      simpa [encodeOccurrenceFacts?, dependency, stateEq, stateRight, capable,
                        factEq, factRight, appendEq] using inductionHypothesis next
            · simp [encodeOccurrenceFacts?, dependency, stateEq, stateRight, capable]
      · simp [encodeOccurrenceFacts?, dependency, inductionHypothesis]

/-- Finite strict-depth dependence is well founded. -/
theorem depthDependency_wellFounded (discovery : Discovery mol) :
    WellFounded (@DepthDependency mol discovery) := by
  letI : IsTrans (Occurrence discovery) (@DepthDependency mol discovery) :=
    ⟨by
      intro first second third hfirst hsecond
      exact ⟨hfirst.1.trans hsecond.1,
        Nat.lt_trans hsecond.2 hfirst.2⟩⟩
  letI : Std.Irrefl (@DepthDependency mol discovery) :=
    ⟨by intro occurrence dependency; exact (Nat.lt_irrefl _ dependency.2).elim⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

/-! ## Explicit occurrence-local four-ligand frame -/

/-- The explicit frame at a discovered final center is exactly the four discovery cursors,
including a possible ligand value equal to `mol.atomCount`. -/
def finalLigandFrame (_discovery : Discovery mol) (root : Root mol) :
    List CanonicalRerootCursor :=
  ligandCursors root

@[simp] theorem finalLigandFrame_length (discovery : Discovery mol) (root : Root mol) :
    (finalLigandFrame discovery root).length = 4 :=
  ligandCursors_length root

/-- Use discovery's proof-carrying four-slot frame at the final center and the exact re-rooted
frame at every inner occurrence. -/
def targetLigandFrame? (discovery : Discovery mol) (target : Occurrence discovery) :
    Option (List CanonicalRerootCursor) :=
  match target.node with
  | .inl _ => some (finalLigandFrame discovery target.root)
  | .inr _ => OneCenter.occurrenceLigandFrame? mol (sourceNode discovery target)

/-! ## Actual Rules 4b and 5 inside the ordinary label equation -/

/-- Rule-4b equation used by the comparator called from production `occurrenceFact?`. -/
def Rule4bEquation (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) (outcome : Option Ordering) : Prop :=
  compareOccurrenceRule4b? mol aux fuel left right = outcome

/-- Rule-5 equation used by the same comparator, retaining the enantiomorphic flag. -/
def Rule5Equation (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) (outcome : Option RawRule5Comparison) : Prop :=
  compareOccurrenceRule5? mol aux fuel left right = outcome

/-- The production constitutional stage: raw Rule-2 comparison with disputed pairwise
automorphism conflicts withheld. -/
def ordinaryConstitutionalStage? (fuel : Nat)
    (left right : CanonicalRerootCursor) : Option Ordering :=
  certifiedConstitutionalStage? mol fuel left right

/-- Pure precedence assembly for independently retained stage results.  It performs no molecular
comparison itself. -/
def assembleOccurrenceComparison?
    (constitutional rule4a rule4b : Option Ordering)
    (rule4c : Option OccurrenceRule4cDecision)
    (rule5 : Option RawRule5Comparison) : Option OccurrenceComparison := do
  let constitutional ← constitutional
  if constitutional != Ordering.eq then return { ordering := constitutional }
  let rule4a ← rule4a
  if rule4a != Ordering.eq then return { ordering := rule4a }
  let rule4b ← rule4b
  if rule4b != Ordering.eq then return { ordering := rule4b }
  let rule4c ← rule4c
  if rule4c.ordering != Ordering.eq then
    return { ordering := rule4c.ordering, rule4cCarrier? := rule4c.carrier? }
  let rule5 ← rule5
  some { ordering := rule5.ordering, pseudo := rule5.pseudo }

theorem sourceNode_bind_occurrenceFact_eq (discovery : Discovery mol)
    (target : Occurrence discovery) (fuel : Nat) (aux : OneCenter.OccurrenceAuxState)
    (fact : OccurrenceAuxFact)
    (computed : occurrenceFact? mol fuel aux (sourceNode discovery target) = some fact) :
    target.sourceNode?.bind (occurrenceFact? mol fuel aux) = some fact := by
  rw [sourceNode_spec]
  exact computed

/-- Package the literal production occurrence result together with its ranking certificate. -/
def ordinaryLabelFromAux? (discovery : Discovery mol) (fuel : Nat)
    (aux : OneCenter.OccurrenceAuxState) (target : Occurrence discovery) :
    Option (Label discovery) :=
  match computed : occurrenceFact? mol fuel aux (sourceNode discovery target) with
  | none => none
  | some fact =>
      some (labelOfOrdinaryFact discovery target fact fuel aux (by
        rw [sourceNode_spec]
        exact computed))

theorem ordinaryLabelFromAux?_eq_none (discovery : Discovery mol) (fuel : Nat)
    (aux : OneCenter.OccurrenceAuxState) (target : Occurrence discovery)
    (computed : occurrenceFact? mol fuel aux (sourceNode discovery target) = none) :
    ordinaryLabelFromAux? discovery fuel aux target = none := by
  unfold ordinaryLabelFromAux?
  split <;> simp_all

theorem ordinaryLabelFromAux?_eq_some (discovery : Discovery mol) (fuel : Nat)
    (aux : OneCenter.OccurrenceAuxState) (target : Occurrence discovery)
    (fact : OccurrenceAuxFact)
    (computed : occurrenceFact? mol fuel aux (sourceNode discovery target) = some fact) :
    ordinaryLabelFromAux? discovery fuel aux target =
      some (labelOfOrdinaryFact discovery target fact fuel aux
        (sourceNode_bind_occurrenceFact_eq discovery target fuel aux fact computed)) := by
  unfold ordinaryLabelFromAux?
  split
  · rename_i noneEq
    simp [noneEq] at computed
  · rename_i otherFact otherEq
    have factEq := Option.some.inj (otherEq.symm.trans computed)
    subst otherFact
    rfl

theorem ordinaryLabelFromAux?_eq_none_iff (discovery : Discovery mol) (fuel : Nat)
    (aux : OneCenter.OccurrenceAuxState) (target : Occurrence discovery) :
    ordinaryLabelFromAux? discovery fuel aux target = none ↔
      occurrenceFact? mol fuel aux (sourceNode discovery target) = none := by
  constructor
  · intro labelNone
    cases computed : occurrenceFact? mol fuel aux (sourceNode discovery target) with
    | none => rfl
    | some fact =>
        have labelSome := ordinaryLabelFromAux?_eq_some discovery fuel aux target fact computed
        rw [labelSome] at labelNone
        simp at labelNone
  · exact ordinaryLabelFromAux?_eq_none discovery fuel aux target

/-- Ordinary derivation consumes one collision-free root state and invokes the actual production
`occurrenceFact?` boundary. -/
def ordinaryLabel? (discovery : Discovery mol) (fuel : Nat) (state : State discovery)
    (target : Occurrence discovery) : Option (Label discovery) := do
  let aux ← executableStateFor? discovery state target
  ordinaryLabelFromAux? discovery fuel aux target

theorem ordinaryLabel?_eq_none_iff_of_aux_eq (discovery : Discovery mol) (fuel : Nat)
    (state : State discovery) (target : Occurrence discovery)
    (aux : OneCenter.OccurrenceAuxState)
    (aux_eq : executableStateFor? discovery state target = some aux) :
    ordinaryLabel? discovery fuel state target = none ↔
      occurrenceFact? mol fuel aux (sourceNode discovery target) = none := by
  unfold ordinaryLabel?
  rw [aux_eq]
  exact ordinaryLabelFromAux?_eq_none_iff discovery fuel aux target

/-- The exact Rule-4c stage occurring between Rules 4b and 5 in the production comparator. -/
def ordinaryRule4cStage? (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) : Option OccurrenceRule4cDecision :=
  if aux.any fun fact => !fact.uppercase then
    let before := compareOccurrenceDescriptorBranchAt mol aux fuel .rule4c
    compareOccurrenceRule4cWithWitness mol aux before before fuel [(left, right)]
  else some { ordering := Ordering.eq }

/-- The production comparator factors through the five independently named stage calls and the
pure precedence assembler. -/
theorem compareOccurrenceBranches?_factorization (aux : OneCenter.OccurrenceAuxState)
    (fuel : Nat) (left right : CanonicalRerootCursor) :
    compareOccurrenceBranches? mol aux fuel left right =
      assembleOccurrenceComparison?
        (ordinaryConstitutionalStage? (mol := mol) fuel left right)
        (compareOccurrenceDescriptorAtTiedRoot? mol aux fuel .rule4a left right)
        (compareOccurrenceRule4b? mol aux fuel left right)
        (ordinaryRule4cStage? (mol := mol) aux fuel left right)
        (compareOccurrenceRule5? mol aux fuel left right) := by
  unfold compareOccurrenceBranches? ordinaryConstitutionalStage?
    assembleOccurrenceComparison? ordinaryRule4cStage?
  cases constitutional : certifiedConstitutionalStage? mol fuel left right with
  | none => simp
  | some constitutionalResult =>
      cases constitutionalResult <;>
        by_cases hasLower : ∃ fact ∈ aux, fact.uppercase = false <;>
        simp [hasLower]

/-- Independent stage evidence for one retained adjacent decision.  There is deliberately no
`compareOccurrenceBranches? = ...` field: the combined equation must be reconstructed from the
individual stage equations and the pure precedence equation. -/
structure Rule45Evaluation (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (comparison : OccurrenceComparedPair mol aux fuel) where
  constitutionalResult : Option Ordering
  constitutionalEquation : ordinaryConstitutionalStage? (mol := mol) fuel
    comparison.left comparison.right = constitutionalResult
  rule4aResult : Option Ordering
  rule4aEquation : compareOccurrenceDescriptorAtTiedRoot? mol aux fuel .rule4a
    comparison.left comparison.right = rule4aResult
  rule4bResult : Option Ordering
  rule4bEquation : Rule4bEquation (mol := mol) aux fuel comparison.left comparison.right
    rule4bResult
  rule4cResult : Option OccurrenceRule4cDecision
  rule4cEquation : ordinaryRule4cStage? (mol := mol) aux fuel
    comparison.left comparison.right = rule4cResult
  rule5Result : Option RawRule5Comparison
  rule5Equation : Rule5Equation (mol := mol) aux fuel comparison.left comparison.right
    rule5Result
  precedenceEquation : assembleOccurrenceComparison? constitutionalResult rule4aResult
    rule4bResult rule4cResult rule5Result = some comparison.decision

/-- Stage equations reconstruct the combined production decision.  In particular, when
precedence reaches Rule 4b or Rule 5, deleting its equation makes this proof impossible: the
assembler contains only a stored result until that equation identifies it with the actual call. -/
theorem Rule45Evaluation.production_eq
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {comparison : OccurrenceComparedPair mol aux fuel}
    (evaluation : Rule45Evaluation (mol := mol) aux fuel comparison) :
    compareOccurrenceBranches? mol aux fuel comparison.left comparison.right =
      some comparison.decision := by
  rw [compareOccurrenceBranches?_factorization]
  rw [evaluation.constitutionalEquation, evaluation.rule4aEquation,
    evaluation.rule4bEquation, evaluation.rule4cEquation, evaluation.rule5Equation]
  exact evaluation.precedenceEquation

def rule45Evaluation (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (comparison : OccurrenceComparedPair mol aux fuel)
    (fullEquation : compareOccurrenceBranches? mol aux fuel comparison.left comparison.right =
      some comparison.decision) :
    Rule45Evaluation (mol := mol) aux fuel comparison :=
  { constitutionalResult := ordinaryConstitutionalStage? (mol := mol) fuel
      comparison.left comparison.right
    constitutionalEquation := rfl
    rule4aResult := compareOccurrenceDescriptorAtTiedRoot? mol aux fuel .rule4a
      comparison.left comparison.right
    rule4aEquation := rfl
    rule4bResult := compareOccurrenceRule4b? mol aux fuel comparison.left comparison.right
    rule4bEquation := rfl
    rule4cResult := ordinaryRule4cStage? (mol := mol) aux fuel
      comparison.left comparison.right
    rule4cEquation := rfl
    rule5Result := compareOccurrenceRule5? mol aux fuel comparison.left comparison.right
    rule5Equation := rfl
    precedenceEquation := by
      rw [← compareOccurrenceBranches?_factorization]
      exact fullEquation }

/-- Once the constitutional and Rule-4a stages tie, a non-tie returned by the certified Rule-4b
call is exactly the decision returned by the full adjacent comparison. -/
theorem Rule45Evaluation.rule4b_controls_after_prior_ties
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {comparison : OccurrenceComparedPair mol aux fuel}
    (evaluation : Rule45Evaluation (mol := mol) aux fuel comparison)
    (constitutional_eq : ordinaryConstitutionalStage? (mol := mol) fuel
      comparison.left comparison.right = some Ordering.eq)
    (rule4a_eq : compareOccurrenceDescriptorAtTiedRoot? mol aux fuel .rule4a
      comparison.left comparison.right = some Ordering.eq)
    (rule4b : Ordering) (rule4b_result : evaluation.rule4bResult = some rule4b)
    (rule4b_nonTie : rule4b ≠ Ordering.eq) :
    comparison.decision = ({ ordering := rule4b } : OccurrenceComparison) := by
  have rule4b_eq : compareOccurrenceRule4b? mol aux fuel comparison.left comparison.right =
      some rule4b :=
    evaluation.rule4bEquation.trans rule4b_result
  have constitutional_eq' : certifiedConstitutionalStage? mol fuel
      comparison.left comparison.right = some Ordering.eq := by
    simpa [ordinaryConstitutionalStage?] using constitutional_eq
  have full :
      some ({ ordering := rule4b } : OccurrenceComparison) = some comparison.decision := by
    simpa [compareOccurrenceBranches?, constitutional_eq',
      rule4a_eq, rule4b_eq, rule4b_nonTie] using evaluation.production_eq
  exact (Option.some.inj full).symm

/-- When Rules 1--4c all tie, the exact certified Rule-5 result supplies both the ordering and
the pseudoasymmetric flag returned by the full adjacent comparison. -/
theorem Rule45Evaluation.rule5_controls_after_prior_ties
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {comparison : OccurrenceComparedPair mol aux fuel}
    (evaluation : Rule45Evaluation (mol := mol) aux fuel comparison)
    (constitutional_eq : ordinaryConstitutionalStage? (mol := mol) fuel
      comparison.left comparison.right = some Ordering.eq)
    (rule4a_eq : compareOccurrenceDescriptorAtTiedRoot? mol aux fuel .rule4a
      comparison.left comparison.right = some Ordering.eq)
    (rule4b_tie : evaluation.rule4bResult = some Ordering.eq)
    (rule4c_tie : ordinaryRule4cStage? (mol := mol) aux fuel
      comparison.left comparison.right = some { ordering := Ordering.eq })
    (rule5 : RawRule5Comparison) (rule5_result : evaluation.rule5Result = some rule5) :
    comparison.decision =
      ({ ordering := rule5.ordering, pseudo := rule5.pseudo } : OccurrenceComparison) := by
  have rule4b_eq : compareOccurrenceRule4b? mol aux fuel comparison.left comparison.right =
      some Ordering.eq :=
    evaluation.rule4bEquation.trans rule4b_tie
  have rule5_eq : compareOccurrenceRule5? mol aux fuel comparison.left comparison.right =
      some rule5 :=
    evaluation.rule5Equation.trans rule5_result
  have constitutional_eq' : certifiedConstitutionalStage? mol fuel
      comparison.left comparison.right = some Ordering.eq := by
    simpa [ordinaryConstitutionalStage?] using constitutional_eq
  have full :
      some ({ ordering := rule5.ordering, pseudo := rule5.pseudo } : OccurrenceComparison) =
        some comparison.decision := by
    cases hasLower : (aux.any fun fact => !fact.uppercase) with
    | false =>
        simpa [compareOccurrenceBranches?, constitutional_eq',
          rule4a_eq, rule4b_eq, hasLower, rule5_eq] using evaluation.production_eq
    | true =>
        have rule4c_eq :
            compareOccurrenceRule4cWithWitness mol aux
              (compareOccurrenceDescriptorBranchAt mol aux fuel .rule4c)
              (compareOccurrenceDescriptorBranchAt mol aux fuel .rule4c) fuel
              [(comparison.left, comparison.right)] = some { ordering := Ordering.eq } := by
          simpa [ordinaryRule4cStage?, hasLower] using rule4c_tie
        simpa [compareOccurrenceBranches?, constitutional_eq',
          rule4a_eq, rule4b_eq, hasLower, rule4c_eq, rule5_eq] using evaluation.production_eq
  exact (Option.some.inj full).symm

/-! ### Structural comparison derivations

These relations mirror the production insertion sort and adjacent traversal, but their comparison
steps are `Rule45Evaluation` certificates.  Consequently the declarative ordinary certificate no
longer stores an opaque equation for either `sortOccurrencesTracked?` or
`compareOccurrenceAdjacentPairs?`. -/

inductive InsertOccurrenceDerivation (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (candidate : CanonicalRerootCursor) :
    List CanonicalRerootCursor → (List CanonicalRerootCursor × Nat) → Prop
  | nil : InsertOccurrenceDerivation aux fuel candidate [] ([candidate], 0)
  | before (head : CanonicalRerootCursor) (tail : List CanonicalRerootCursor)
      (decision : OccurrenceComparison)
      (stage : Rule45Evaluation (mol := mol) aux fuel
        { left := candidate, right := head, decision := decision })
      (not_lt : (decision.ordering == Ordering.lt) = false) :
      InsertOccurrenceDerivation aux fuel candidate (head :: tail)
        (candidate :: head :: tail, if decision.pseudo then 1 else 0)
  | after (head : CanonicalRerootCursor) (tail inserted : List CanonicalRerootCursor)
      (count : Nat) (decision : OccurrenceComparison)
      (stage : Rule45Evaluation (mol := mol) aux fuel
        { left := candidate, right := head, decision := decision })
      (is_lt : (decision.ordering == Ordering.lt) = true)
      (deeper : InsertOccurrenceDerivation aux fuel candidate tail (inserted, count)) :
      InsertOccurrenceDerivation aux fuel candidate (head :: tail)
        (head :: inserted, (if decision.pseudo then 1 else 0) + count)

theorem InsertOccurrenceDerivation.production_eq
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {candidate : CanonicalRerootCursor} {input : List CanonicalRerootCursor}
    {output : List CanonicalRerootCursor × Nat}
    (derivation : InsertOccurrenceDerivation (mol := mol) aux fuel candidate input output) :
    insertOccurrenceTracked mol aux fuel candidate input = some output := by
  induction derivation with
  | nil => rfl
  | before head tail decision stage not_lt =>
      have not_lt' : decision.ordering ≠ Ordering.lt := by simpa using not_lt
      simp [insertOccurrenceTracked, stage.production_eq, not_lt']
  | after head tail inserted count decision stage is_lt deeper inductionHypothesis =>
      have is_lt' : decision.ordering = Ordering.lt := by simpa using is_lt
      simp [insertOccurrenceTracked, stage.production_eq, is_lt', inductionHypothesis]

theorem insertOccurrenceDerivation_of_production
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (candidate : CanonicalRerootCursor) (input : List CanonicalRerootCursor)
    (output : List CanonicalRerootCursor × Nat)
    (computed : insertOccurrenceTracked mol aux fuel candidate input = some output) :
    InsertOccurrenceDerivation (mol := mol) aux fuel candidate input output := by
  induction input generalizing output with
  | nil =>
      simp [insertOccurrenceTracked] at computed
      subst output
      exact .nil
  | cons head tail inductionHypothesis =>
      simp only [insertOccurrenceTracked] at computed
      cases comparisonEq : compareOccurrenceBranches? mol aux fuel candidate head with
      | none => simp [comparisonEq] at computed
      | some decision =>
          cases isLt : decision.ordering == Ordering.lt with
          | false =>
              have notLt : decision.ordering ≠ Ordering.lt := by simpa using isLt
              have direct : insertOccurrenceTracked mol aux fuel candidate (head :: tail) =
                  some (candidate :: head :: tail, if decision.pseudo then 1 else 0) := by
                simp [insertOccurrenceTracked, comparisonEq, notLt]
              have outputEq : output =
                  (candidate :: head :: tail, if decision.pseudo then 1 else 0) :=
                Option.some.inj (computed.symm.trans direct)
              subst output
              exact .before head tail decision
                (rule45Evaluation (mol := mol) aux fuel _ comparisonEq) isLt
          | true =>
              have isLt' : decision.ordering = Ordering.lt := by simpa using isLt
              cases deeperEq : insertOccurrenceTracked mol aux fuel candidate tail with
              | none =>
                  simp [comparisonEq, isLt', deeperEq] at computed
              | some deeper =>
                  have direct : insertOccurrenceTracked mol aux fuel candidate (head :: tail) =
                      some (head :: deeper.1,
                        (if decision.pseudo then 1 else 0) + deeper.2) := by
                    simp [insertOccurrenceTracked, comparisonEq, isLt', deeperEq]
                  have outputEq : output =
                      (head :: deeper.1, (if decision.pseudo then 1 else 0) + deeper.2) :=
                    Option.some.inj (computed.symm.trans direct)
                  subst output
                  exact .after head tail deeper.1 deeper.2 decision
                    (rule45Evaluation (mol := mol) aux fuel _ comparisonEq) isLt
                    (inductionHypothesis deeper deeperEq)

inductive SortOccurrencesDerivation (aux : OneCenter.OccurrenceAuxState) (fuel : Nat) :
    List CanonicalRerootCursor → (List CanonicalRerootCursor × Nat) → Prop
  | nil : SortOccurrencesDerivation aux fuel [] ([], 0)
  | cons (cursor : CanonicalRerootCursor) (cursors : List CanonicalRerootCursor)
      (sorted inserted : List CanonicalRerootCursor × Nat)
      (tail : SortOccurrencesDerivation aux fuel cursors sorted)
      (insertion : InsertOccurrenceDerivation (mol := mol) aux fuel cursor sorted.1 inserted) :
      SortOccurrencesDerivation aux fuel (cursor :: cursors)
        (inserted.1, sorted.2 + inserted.2)

theorem SortOccurrencesDerivation.production_eq
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {input : List CanonicalRerootCursor} {output : List CanonicalRerootCursor × Nat}
    (derivation : SortOccurrencesDerivation (mol := mol) aux fuel input output) :
    sortOccurrencesTracked? mol aux fuel input = some output := by
  induction derivation with
  | nil => rfl
  | cons cursor cursors sorted inserted tail insertion tailHypothesis =>
      simp [sortOccurrencesTracked?, tailHypothesis, insertion.production_eq]

theorem sortOccurrencesDerivation_of_production
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (input : List CanonicalRerootCursor) (output : List CanonicalRerootCursor × Nat)
    (computed : sortOccurrencesTracked? mol aux fuel input = some output) :
    SortOccurrencesDerivation (mol := mol) aux fuel input output := by
  induction input generalizing output with
  | nil =>
      simp [sortOccurrencesTracked?] at computed
      subst output
      exact .nil
  | cons cursor cursors inductionHypothesis =>
      simp only [sortOccurrencesTracked?] at computed
      cases sortedEq : sortOccurrencesTracked? mol aux fuel cursors with
      | none => simp [sortedEq] at computed
      | some sorted =>
          cases insertedEq : insertOccurrenceTracked mol aux fuel cursor sorted.1 with
          | none => simp [sortedEq, insertedEq] at computed
          | some inserted =>
              simp [sortedEq, insertedEq] at computed
              subst output
              exact .cons cursor cursors sorted inserted
                (inductionHypothesis sorted sortedEq)
                (insertOccurrenceDerivation_of_production aux fuel cursor sorted.1 inserted
                  insertedEq)

inductive AdjacentComparisonsDerivation (aux : OneCenter.OccurrenceAuxState) (fuel : Nat) :
    List CanonicalRerootCursor → List (OccurrenceComparedPair mol aux fuel) → Prop
  | nil : AdjacentComparisonsDerivation aux fuel [] []
  | singleton (cursor : CanonicalRerootCursor) :
      AdjacentComparisonsDerivation aux fuel [cursor] []
  | cons (left right : CanonicalRerootCursor) (remaining : List CanonicalRerootCursor)
      (decision : OccurrenceComparison) (deeper : List (OccurrenceComparedPair mol aux fuel))
      (stage : Rule45Evaluation (mol := mol) aux fuel
        { left := left, right := right, decision := decision })
      (tail : AdjacentComparisonsDerivation aux fuel (right :: remaining) deeper) :
      AdjacentComparisonsDerivation aux fuel (left :: right :: remaining)
        ({ left := left, right := right, decision := decision } :: deeper)

theorem AdjacentComparisonsDerivation.production_eq
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {input : List CanonicalRerootCursor}
    {output : List (OccurrenceComparedPair mol aux fuel)}
    (derivation : AdjacentComparisonsDerivation (mol := mol) aux fuel input output) :
    compareOccurrenceAdjacentPairs? mol aux fuel input = some output := by
  induction derivation with
  | nil => rfl
  | singleton cursor => rfl
  | cons left right remaining decision deeper stage tail inductionHypothesis =>
      simp [compareOccurrenceAdjacentPairs?, stage.production_eq, inductionHypothesis]

theorem adjacentComparisonsDerivation_of_production
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (input : List CanonicalRerootCursor)
    (output : List (OccurrenceComparedPair mol aux fuel))
    (computed : compareOccurrenceAdjacentPairs? mol aux fuel input = some output) :
    AdjacentComparisonsDerivation (mol := mol) aux fuel input output := by
  induction input generalizing output with
  | nil =>
      simp [compareOccurrenceAdjacentPairs?] at computed
      subst output
      exact .nil
  | cons left tail inductionHypothesis =>
      cases tail with
      | nil =>
          simp [compareOccurrenceAdjacentPairs?] at computed
          subst output
          exact .singleton left
      | cons right remaining =>
          simp only [compareOccurrenceAdjacentPairs?] at computed
          cases comparisonEq : compareOccurrenceBranches? mol aux fuel left right with
          | none => simp [comparisonEq] at computed
          | some decision =>
              cases deeperEq : compareOccurrenceAdjacentPairs? mol aux fuel
                  (right :: remaining) with
              | none => simp [comparisonEq, deeperEq] at computed
              | some deeper =>
                  simp [comparisonEq, deeperEq] at computed
                  subst output
                  exact .cons left right remaining decision deeper
                    (rule45Evaluation (mol := mol) aux fuel _ comparisonEq)
                    (inductionHypothesis deeper deeperEq)

/-- Independent declarative clauses for one successful ordinary occurrence ranking.  The
relation names every primitive production stage and the Rule-4b/5 equations on every adjacent
comparison, but does not mention `legacyOccurrenceFact?` itself. -/
structure LegacyOrdinaryFactCertificate (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact) where
  spec : AtomSpec
  parity : TetrahedralInputParity
  roots : List CanonicalRerootCursor
  sorted : List CanonicalRerootCursor × Nat
  positions : List Nat
  compared : List (OccurrenceComparedPair mol aux fuel)
  atom_spec : mol.atomAt? node.atom = some spec
  tetrahedral : spec.tetrahedral? = some parity
  frame : OneCenter.occurrenceLigandFrame? mol node = some roots
  ranking : SortOccurrencesDerivation (mol := mol) aux fuel roots sorted
  positions_eq :
    (sorted.1.mapM fun cursor =>
      ((mol.ligandsWithLonePair node.atom).zipIdx.find?
        fun entry => entry.1 == cursor.node.atom).map Prod.snd) = some positions
  comparisons : AdjacentComparisonsDerivation (mol := mol) aux fuel sorted.1 compared
  strict : (compared.map fun comparison => comparison.decision).all
      (fun decision => decision.ordering != Ordering.eq) = true
  fact_eq : fact =
    { key := canonicalOccurrenceKey node
      atom := node.atom
      descriptor := RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven positions)
      uppercase :=
        ((compared.map fun comparison => comparison.decision).filter
          fun decision => decision.pseudo).length % 2 == 0
      priorityPositions := positions }

/-- The proof-irrelevant declarative proposition corresponding to the proof-relevant certificate. -/
def LegacyOrdinaryFactClauses (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact) : Prop :=
  Nonempty (LegacyOrdinaryFactCertificate (mol := mol) aux fuel node fact)

/-- The independent ordinary clauses are sound for the production boundary. -/
theorem LegacyOrdinaryFactClauses.production_eq {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {fact : OccurrenceAuxFact}
    (clauses : LegacyOrdinaryFactClauses (mol := mol) aux fuel node fact) :
    legacyOccurrenceFact? mol fuel aux node = some fact := by
  rcases clauses with ⟨certificate⟩
  have allStrict := (List.all_eq_true.mp certificate.strict)
  simp [legacyOccurrenceFact?, certificate.atom_spec, certificate.tetrahedral,
    certificate.frame, certificate.ranking.production_eq, certificate.positions_eq,
    certificate.comparisons.production_eq, ← certificate.fact_eq]
  intro comparison member
  have decisionMember : comparison.decision ∈
      certificate.compared.map fun entry => entry.decision :=
    List.mem_map.mpr ⟨comparison, member, rfl⟩
  simpa using allStrict comparison.decision decisionMember

/-- Every successful production occurrence fact yields the independent primitive clauses. -/
theorem legacyOrdinaryFactClauses_of_production {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {fact : OccurrenceAuxFact}
    (computed : legacyOccurrenceFact? mol fuel aux node = some fact) :
    LegacyOrdinaryFactClauses (mol := mol) aux fuel node fact := by
  refine ⟨?_⟩
  unfold legacyOccurrenceFact? at computed
  cases atomEq : mol.atomAt? node.atom with
  | none => simp [atomEq] at computed
  | some spec =>
      cases parityEq : spec.tetrahedral? with
      | none => simp [atomEq, parityEq] at computed
      | some parity =>
          cases frameEq : OneCenter.occurrenceLigandFrame? mol node with
          | none => simp [atomEq, frameEq] at computed
          | some roots =>
              cases rankingEq : sortOccurrencesTracked? mol aux fuel roots with
              | none => simp [atomEq, frameEq, rankingEq] at computed
              | some sorted =>
                  cases positionsEq : (sorted.1.mapM fun cursor =>
                      ((mol.ligandsWithLonePair node.atom).zipIdx.find?
                        fun entry => entry.1 == cursor.node.atom).map Prod.snd) with
                  | none =>
                      simp [atomEq, frameEq, rankingEq, positionsEq] at computed
                  | some positions =>
                      cases comparisonsEq : compareOccurrenceAdjacentPairs? mol aux fuel
                          sorted.1 with
                      | none =>
                          simp [atomEq, frameEq, rankingEq, positionsEq,
                            comparisonsEq] at computed
                      | some compared =>
                          have simplified := computed
                          simp [atomEq, parityEq, frameEq, rankingEq, positionsEq,
                            comparisonsEq] at simplified
                          have strictEq : (compared.map fun comparison =>
                              comparison.decision).all
                                (fun decision => decision.ordering != Ordering.eq) = true := by
                            simpa [List.all_eq_true] using simplified.1
                          have factEq : fact =
                              { key := canonicalOccurrenceKey node
                                atom := node.atom
                                descriptor := RawMolecule.descriptorOfParity parity
                                  (RawMolecule.permutationIsEven positions)
                                uppercase :=
                                  ((compared.map fun comparison => comparison.decision).filter
                                    fun decision => decision.pseudo).length % 2 == 0
                                priorityPositions := positions } :=
                            simplified.2.symm
                          refine
                            { spec := spec
                              parity := parity
                              roots := roots
                              sorted := sorted
                              positions := positions
                              compared := compared
                              atom_spec := atomEq
                              tetrahedral := parityEq
                              frame := frameEq
                              ranking := sortOccurrencesDerivation_of_production aux fuel roots
                                sorted rankingEq
                              positions_eq := positionsEq
                              comparisons := adjacentComparisonsDerivation_of_production aux fuel
                                sorted.1 compared comparisonsEq
                              strict := strictEq
                              fact_eq := factEq }

/-- The independently defined ordinary clauses are extensionally complete for production. -/
theorem legacyOrdinaryFactClauses_iff_production (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact) :
    LegacyOrdinaryFactClauses (mol := mol) aux fuel node fact ↔
      legacyOccurrenceFact? mol fuel aux node = some fact :=
  ⟨LegacyOrdinaryFactClauses.production_eq, legacyOrdinaryFactClauses_of_production⟩

/-- Primitive public evidence records the selected backend. The legacy branch requires profile
unavailability; the framed branch supplies primitive profile, ranking and adjacency evidence.
Neither constructor stores the final evaluator equation. -/
inductive OrdinaryFactCertificate (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact) where
  | legacy (unavailable : FrameRuntime.profile? mol node = none)
      (certificate : LegacyOrdinaryFactCertificate (mol := mol) aux fuel node fact)
  | framed (certificate : FramedOrdinaryConformance.OrdinaryFactCertificateComplete
      (mol := mol) false aux fuel node fact)

/-- Public fact clauses follow the profile-selected backend without supplying a desired result. -/
def OrdinaryFactClauses (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact) : Prop :=
  Nonempty (OrdinaryFactCertificate (mol := mol) aux fuel node fact)

theorem OrdinaryFactClauses.production_eq {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {fact : OccurrenceAuxFact}
    (clauses : OrdinaryFactClauses (mol := mol) aux fuel node fact) :
    occurrenceFact? mol fuel aux node = some fact := by
  rcases clauses with ⟨certificate⟩
  cases certificate with
  | legacy unavailable certificate =>
      rw [occurrenceFact?_eq_legacy_of_profile_none mol fuel aux node unavailable]
      exact LegacyOrdinaryFactClauses.production_eq ⟨certificate⟩
  | framed certificate =>
      rw [occurrenceFact?_eq_framed_of_profile_some mol fuel aux node
        certificate.profile certificate.profile_eq, framedOccurrenceFact?_eq_complete]
      exact certificate.production_eq

theorem ordinaryFactClauses_of_production {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {fact : OccurrenceAuxFact}
    (computed : occurrenceFact? mol fuel aux node = some fact) :
    OrdinaryFactClauses (mol := mol) aux fuel node fact := by
  cases profileEq : FrameRuntime.profile? mol node with
  | none =>
      have legacyComputed : legacyOccurrenceFact? mol fuel aux node = some fact := by
        simpa only [occurrenceFact?, profileEq] using computed
      rcases legacyOrdinaryFactClauses_of_production legacyComputed with ⟨certificate⟩
      exact ⟨.legacy profileEq certificate⟩
  | some profile =>
      have framedComputed : FramedCompleteRuntime.occurrenceFactComplete?
          mol false fuel aux node = some fact := by
        rw [← framedOccurrenceFact?_eq_complete]
        simpa only [occurrenceFact?, profileEq] using computed
      rcases FramedOrdinaryConformance.ordinaryFactClausesComplete_of_production
        framedComputed with ⟨certificate⟩
      exact ⟨.framed certificate⟩

theorem ordinaryFactClauses_iff_production (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact) :
    OrdinaryFactClauses (mol := mol) aux fuel node fact ↔
      occurrenceFact? mol fuel aux node = some fact :=
  ⟨OrdinaryFactClauses.production_eq, ordinaryFactClauses_of_production⟩

/-- Decomposed ordinary derivation.  It relates the root-local state to the independent primitive
clauses and to the fully certified label, without assuming the combined evaluator equation. -/
inductive OrdinaryDerivation (discovery : Discovery mol) (fuel : Nat) (state : State discovery)
    (target : Occurrence discovery) (label : Label discovery) : Prop
  | intro (aux : OneCenter.OccurrenceAuxState) (fact : OccurrenceAuxFact)
      (aux_eq : executableStateFor? discovery state target = some aux)
      (clauses : OrdinaryFactClauses (mol := mol) aux fuel
        (sourceNode discovery target) fact)
      (label_eq : labelOfOrdinaryFact discovery target fact fuel aux (by
        rw [sourceNode_spec]
        exact clauses.production_eq) = label) :
      OrdinaryDerivation discovery fuel state target label

theorem ordinaryLabel?_eq_some_iff (discovery : Discovery mol) (fuel : Nat)
    (state : State discovery) (target : Occurrence discovery) (label : Label discovery) :
    ordinaryLabel? discovery fuel state target = some label ↔
      ∃ aux fact,
        ∃ computed : occurrenceFact? mol fuel aux (sourceNode discovery target) = some fact,
          executableStateFor? discovery state target = some aux ∧
          labelOfOrdinaryFact discovery target fact fuel aux
            (sourceNode_bind_occurrenceFact_eq discovery target fuel aux fact computed) = label := by
  cases auxEq : executableStateFor? discovery state target with
  | none => simp [ordinaryLabel?, auxEq]
  | some aux =>
      cases productionEq : occurrenceFact? mol fuel aux (sourceNode discovery target) with
      | none =>
          rw [show ordinaryLabel? discovery fuel state target = none by
            simp [ordinaryLabel?, auxEq,
              ordinaryLabelFromAux?_eq_none discovery fuel aux target productionEq]]
          constructor
          · simp
          · rintro ⟨otherAux, otherFact, otherProductionEq, otherAuxEq, _⟩
            have auxEqual := Option.some.inj otherAuxEq
            subst otherAux
            simp [productionEq] at otherProductionEq
      | some fact =>
          rw [show ordinaryLabel? discovery fuel state target =
              some (labelOfOrdinaryFact discovery target fact fuel aux
                (sourceNode_bind_occurrenceFact_eq discovery target fuel aux fact productionEq)) by
            simp [ordinaryLabel?, auxEq,
              ordinaryLabelFromAux?_eq_some discovery fuel aux target fact productionEq]]
          constructor
          · intro accepted
            have accepted' := Option.some.inj accepted
            refine ⟨aux, fact, productionEq, rfl, ?_⟩
            exact accepted'
          · rintro ⟨otherAux, otherFact, otherProductionEq, otherAuxEq, labelEq⟩
            have auxEqual := Option.some.inj otherAuxEq
            subst otherAux
            have factEqual := Option.some.inj (productionEq.symm.trans otherProductionEq)
            subst otherFact
            exact congrArg some labelEq

theorem ordinaryDerivation_iff (discovery : Discovery mol) (fuel : Nat)
    (state : State discovery) (target : Occurrence discovery) (label : Label discovery) :
    OrdinaryDerivation discovery fuel state target label ↔
      ordinaryLabel? discovery fuel state target = some label := by
  constructor
  · rintro ⟨aux, fact, auxEq, clauses, labelEq⟩
    apply (ordinaryLabel?_eq_some_iff discovery fuel state target label).2
    exact ⟨aux, fact, clauses.production_eq, auxEq, labelEq⟩
  · intro accepted
    rcases (ordinaryLabel?_eq_some_iff discovery fuel state target label).1 accepted with
      ⟨aux, fact, productionEq, auxEq, labelEq⟩
    exact .intro aux fact auxEq (ordinaryFactClauses_of_production productionEq) labelEq

/-- Ranking evidence, case, positions, and reference frame are outputs of `occurrenceFact?`,
not unchecked premises. -/
theorem ordinaryLabel_certified (discovery : Discovery mol) (fuel : Nat)
    (state : State discovery) (target : Occurrence discovery) (label : Label discovery)
    (accepted : ordinaryLabel? discovery fuel state target = some label) :
    ∃ aux fact,
      OrdinaryFactClauses (mol := mol) aux fuel (sourceNode discovery target) fact ∧
      label.fact = fact ∧
      label.occurrence = target := by
  rcases (ordinaryDerivation_iff discovery fuel state target label).2 accepted with
    ⟨aux, fact, _, clauses, labelEq⟩
  subst label
  exact ⟨aux, fact, clauses, rfl, rfl⟩

/-! ## Full descriptor-level Rule 6 on the same occurrence state -/

/-! ### Fail-closed structural Rules-1--5 carrier ranking

The first Rule-6 partition must not use a Boolean sort which interprets an inconclusive
comparison as `true`.  These definitions mirror the production insertion order with an `Option`
comparison and retain a `Rule45Evaluation` at every comparison actually used by the sort and by
the final adjacent traversal. -/

/-- Compare two positions in the discovered four-ligand frame through the actual Rules-1--5
comparator.  Missing positions and inconclusive comparisons fail. -/
def compareRule6InitialPositions? (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (leftPosition rightPosition : Nat) :
    Option OccurrenceComparison := do
  let left ← roots[leftPosition]?
  let right ← roots[rightPosition]?
  compareOccurrenceBranches? mol aux fuel left right

/-- Proof-relevant stage decomposition of one successful initial carrier comparison. -/
structure Rule6InitialPositionEvaluation (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (leftPosition rightPosition : Nat)
    (decision : OccurrenceComparison) where
  left : CanonicalRerootCursor
  right : CanonicalRerootCursor
  left_eq : roots[leftPosition]? = some left
  right_eq : roots[rightPosition]? = some right
  stages : Rule45Evaluation (mol := mol) aux fuel
    { left := left, right := right, decision := decision }

theorem Rule6InitialPositionEvaluation.production_eq
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor} {leftPosition rightPosition : Nat}
    {decision : OccurrenceComparison}
    (evaluation : Rule6InitialPositionEvaluation (mol := mol) aux fuel roots
      leftPosition rightPosition decision) :
    compareRule6InitialPositions? (mol := mol) aux fuel roots leftPosition rightPosition =
      some decision := by
  simp [compareRule6InitialPositions?, evaluation.left_eq, evaluation.right_eq,
    evaluation.stages.production_eq]

def rule6InitialPositionEvaluation_of_production
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (leftPosition rightPosition : Nat)
    (decision : OccurrenceComparison)
    (computed : compareRule6InitialPositions? (mol := mol) aux fuel roots
      leftPosition rightPosition = some decision) :
    Rule6InitialPositionEvaluation (mol := mol) aux fuel roots
      leftPosition rightPosition decision := by
  unfold compareRule6InitialPositions? at computed
  cases leftEq : roots[leftPosition]? with
  | none => simp [leftEq] at computed
  | some left =>
      cases rightEq : roots[rightPosition]? with
      | none => simp [leftEq, rightEq] at computed
      | some right =>
          cases comparisonEq : compareOccurrenceBranches? mol aux fuel left right with
          | none => simp [leftEq, rightEq, comparisonEq] at computed
          | some actual =>
              have actualEq : actual = decision := by
                apply Option.some.inj
                simpa [leftEq, rightEq, comparisonEq] using computed
              subst actual
              exact
                { left := left
                  right := right
                  left_eq := leftEq
                  right_eq := rightEq
                  stages := rule45Evaluation (mol := mol) aux fuel _ comparisonEq }

/-- Fail-closed insertion of one ligand position into the initial Rules-1--5 order. -/
def insertRule6InitialPosition? (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (candidate : Nat) :
    List Nat → Option (List Nat)
  | [] => some [candidate]
  | head :: tail => do
      let decision ← compareRule6InitialPositions? (mol := mol) aux fuel roots candidate head
      if decision.ordering == Ordering.lt then
        let inserted ← insertRule6InitialPosition? aux fuel roots candidate tail
        some (head :: inserted)
      else
        some (candidate :: head :: tail)

inductive InsertRule6InitialDerivation (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (candidate : Nat) :
    List Nat → List Nat → Prop
  | nil : InsertRule6InitialDerivation aux fuel roots candidate [] [candidate]
  | before (head : Nat) (tail : List Nat) (decision : OccurrenceComparison)
      (evaluation : Rule6InitialPositionEvaluation (mol := mol) aux fuel roots
        candidate head decision)
      (not_lt : decision.ordering ≠ Ordering.lt) :
      InsertRule6InitialDerivation aux fuel roots candidate (head :: tail)
        (candidate :: head :: tail)
  | after (head : Nat) (tail inserted : List Nat) (decision : OccurrenceComparison)
      (evaluation : Rule6InitialPositionEvaluation (mol := mol) aux fuel roots
        candidate head decision)
      (is_lt : decision.ordering = Ordering.lt)
      (deeper : InsertRule6InitialDerivation aux fuel roots candidate tail inserted) :
      InsertRule6InitialDerivation aux fuel roots candidate (head :: tail) (head :: inserted)

theorem InsertRule6InitialDerivation.production_eq
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor} {candidate : Nat} {input output : List Nat}
    (derived : InsertRule6InitialDerivation (mol := mol) aux fuel roots candidate input output) :
    insertRule6InitialPosition? (mol := mol) aux fuel roots candidate input = some output := by
  induction derived with
  | nil => rfl
  | before head tail decision evaluation notLt =>
      simp [insertRule6InitialPosition?, evaluation.production_eq, notLt]
  | after head tail inserted decision evaluation isLt deeper inductionHypothesis =>
      simp [insertRule6InitialPosition?, evaluation.production_eq, isLt, inductionHypothesis]

theorem insertRule6InitialDerivation_of_production
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (candidate : Nat) (input output : List Nat)
    (computed : insertRule6InitialPosition? (mol := mol) aux fuel roots candidate input =
      some output) :
    InsertRule6InitialDerivation (mol := mol) aux fuel roots candidate input output := by
  induction input generalizing output with
  | nil =>
      simp [insertRule6InitialPosition?] at computed
      subst output
      exact .nil
  | cons head tail inductionHypothesis =>
      simp only [insertRule6InitialPosition?] at computed
      cases comparisonEq : compareRule6InitialPositions? (mol := mol) aux fuel roots
          candidate head with
      | none => simp [comparisonEq] at computed
      | some decision =>
          by_cases isLt : decision.ordering = Ordering.lt
          · cases deeperEq : insertRule6InitialPosition? (mol := mol) aux fuel roots
                candidate tail with
            | none => simp [comparisonEq, isLt, deeperEq] at computed
            | some inserted =>
                have outputEq : head :: inserted = output := by
                  apply Option.some.inj
                  simpa [comparisonEq, isLt, deeperEq] using computed
                subst output
                exact .after head tail inserted decision
                  (rule6InitialPositionEvaluation_of_production aux fuel roots candidate head
                    decision comparisonEq)
                  isLt (inductionHypothesis inserted deeperEq)
          · have outputEq : candidate :: head :: tail = output := by
              apply Option.some.inj
              simpa [comparisonEq, isLt] using computed
            subst output
            exact .before head tail decision
              (rule6InitialPositionEvaluation_of_production aux fuel roots candidate head
                decision comparisonEq) isLt

/-- Fail-closed structural insertion sort of the four ligand positions. -/
def sortRule6InitialPositions? (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) : List Nat → Option (List Nat)
  | [] => some []
  | position :: positions => do
      let sorted ← sortRule6InitialPositions? aux fuel roots positions
      insertRule6InitialPosition? (mol := mol) aux fuel roots position sorted

inductive SortRule6InitialDerivation (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) : List Nat → List Nat → Prop
  | nil : SortRule6InitialDerivation aux fuel roots [] []
  | cons (position : Nat) (positions sorted output : List Nat)
      (tail : SortRule6InitialDerivation aux fuel roots positions sorted)
      (insertion : InsertRule6InitialDerivation (mol := mol) aux fuel roots
        position sorted output) :
      SortRule6InitialDerivation aux fuel roots (position :: positions) output

theorem SortRule6InitialDerivation.production_eq
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor} {input output : List Nat}
    (derived : SortRule6InitialDerivation (mol := mol) aux fuel roots input output) :
    sortRule6InitialPositions? (mol := mol) aux fuel roots input = some output := by
  induction derived with
  | nil => rfl
  | cons position positions sorted output tail insertion inductionHypothesis =>
      simp [sortRule6InitialPositions?, inductionHypothesis, insertion.production_eq]

theorem sortRule6InitialDerivation_of_production
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (input output : List Nat)
    (computed : sortRule6InitialPositions? (mol := mol) aux fuel roots input = some output) :
    SortRule6InitialDerivation (mol := mol) aux fuel roots input output := by
  induction input generalizing output with
  | nil =>
      simp [sortRule6InitialPositions?] at computed
      subst output
      exact .nil
  | cons position positions inductionHypothesis =>
      simp only [sortRule6InitialPositions?] at computed
      cases sortedEq : sortRule6InitialPositions? (mol := mol) aux fuel roots positions with
      | none => simp [sortedEq] at computed
      | some sorted =>
          exact .cons position positions sorted output
            (inductionHypothesis sorted sortedEq)
            (insertRule6InitialDerivation_of_production aux fuel roots position sorted output
              (by simpa [sortedEq] using computed))

/-- Fail-closed adjacent traversal of the certified initial order. -/
def compareRule6InitialAdjacent? (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) : List Nat → Option (List (Option Ordering))
  | [] | [_] => some []
  | left :: right :: remaining => do
      let decision ← compareRule6InitialPositions? (mol := mol) aux fuel roots left right
      let deeper ← compareRule6InitialAdjacent? aux fuel roots (right :: remaining)
      some (some decision.ordering :: deeper)

inductive Rule6InitialAdjacentDerivation (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) :
    List Nat → List (Option Ordering) → Prop
  | nil : Rule6InitialAdjacentDerivation aux fuel roots [] []
  | singleton (position : Nat) : Rule6InitialAdjacentDerivation aux fuel roots [position] []
  | cons (left right : Nat) (remaining : List Nat) (decision : OccurrenceComparison)
      (deeper : List (Option Ordering))
      (evaluation : Rule6InitialPositionEvaluation (mol := mol) aux fuel roots
        left right decision)
      (tail : Rule6InitialAdjacentDerivation aux fuel roots (right :: remaining) deeper) :
      Rule6InitialAdjacentDerivation aux fuel roots (left :: right :: remaining)
        (some decision.ordering :: deeper)

theorem Rule6InitialAdjacentDerivation.production_eq
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor} {input : List Nat}
    {output : List (Option Ordering)}
    (derived : Rule6InitialAdjacentDerivation (mol := mol) aux fuel roots input output) :
    compareRule6InitialAdjacent? (mol := mol) aux fuel roots input = some output := by
  induction derived with
  | nil => rfl
  | singleton position => rfl
  | cons left right remaining decision deeper evaluation tail inductionHypothesis =>
      simp [compareRule6InitialAdjacent?, evaluation.production_eq, inductionHypothesis]

theorem rule6InitialAdjacentDerivation_of_production
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (input : List Nat)
    (output : List (Option Ordering))
    (computed : compareRule6InitialAdjacent? (mol := mol) aux fuel roots input = some output) :
    Rule6InitialAdjacentDerivation (mol := mol) aux fuel roots input output := by
  induction input generalizing output with
  | nil =>
      simp [compareRule6InitialAdjacent?] at computed
      subst output
      exact .nil
  | cons left tail inductionHypothesis =>
      cases tail with
      | nil =>
          simp [compareRule6InitialAdjacent?] at computed
          subst output
          exact .singleton left
      | cons right remaining =>
          simp only [compareRule6InitialAdjacent?] at computed
          cases comparisonEq : compareRule6InitialPositions? (mol := mol) aux fuel roots
              left right with
          | none => simp [comparisonEq] at computed
          | some decision =>
              cases deeperEq : compareRule6InitialAdjacent? (mol := mol) aux fuel roots
                  (right :: remaining) with
              | none => simp [comparisonEq, deeperEq] at computed
              | some deeper =>
                  have outputEq : some decision.ordering :: deeper = output := by
                    apply Option.some.inj
                    simpa [comparisonEq, deeperEq] using computed
                  subst output
                  exact .cons left right remaining decision deeper
                    (rule6InitialPositionEvaluation_of_production aux fuel roots left right
                      decision comparisonEq)
                    (inductionHypothesis deeper deeperEq)

/-- Compare two ligand positions through actual occurrence Rules 1--6. -/
def comparePositionsThroughRule6? (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands : List Nat)
    (referencePosition leftPosition rightPosition : Nat) : Option Rule6TrackedDecision := do
  let reference ← ligands[referencePosition]?
  let left ← roots[leftPosition]?
  let right ← roots[rightPosition]?
  compareOccurrenceBranchesThroughRule6At? mol aux reference fuel left right

/-- Stable insertion with a callback-parametric occurrence comparison. -/
def insertOccurrencePositionRule6Tracked? (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands : List Nat) (reference candidate : Nat) :
    List Nat → Option (List Nat × Nat × Bool)
  | [] => some ([candidate], 0, true)
  | low :: remaining => do
      let decision ← comparePositionsThroughRule6? (mol := mol) aux fuel roots ligands
        reference low candidate
      let observed := if decision.pseudo then 1 else 0
      match decision.ordering with
      | .lt =>
          let deeper ← insertOccurrencePositionRule6Tracked? aux fuel roots ligands reference
            candidate remaining
          some (low :: deeper.1, observed + deeper.2.1, deeper.2.2)
      | .eq => some (candidate :: low :: remaining, observed, false)
      | .gt => some (candidate :: low :: remaining, observed, true)

/-- Complete four-ligand Rule-6 ranking for one promoted reference position. -/
def rankOccurrencePositionsThroughRule6Tracked? (aux : OneCenter.OccurrenceAuxState)
    (fuel : Nat) (roots : List CanonicalRerootCursor) (ligands start : List Nat)
    (referencePosition : Nat) : Option Rule6TrackedRanking := do
  let tracked ← start.foldlM (fun accumulator candidate => do
    let inserted ← insertOccurrencePositionRule6Tracked? (mol := mol) aux fuel roots ligands
      referencePosition candidate accumulator.1
    some (inserted.1, accumulator.2.1 + inserted.2.1,
      accumulator.2.2 && inserted.2.2)) ([], 0, true)
  some
    { positions := tracked.1.reverse
      pseudoComparisons := tracked.2.1
      unique := tracked.2.2 }

abbrev Cursor := CanonicalRerootCursor
abbrev CursorPair := Cursor × Cursor

/-- A proof-relevant trace for the callback used while reranking child spheres. -/
abbrev BeforeTrace := Cursor → Cursor → Ordering → Prop

inductive InsertCursorTrace
    (before : Cursor → Cursor → Option Ordering) (trace : BeforeTrace)
    (candidate : Cursor) : List Cursor → List Cursor → Prop
  | nil : InsertCursorTrace before trace candidate [] [candidate]
  | before (head : Cursor) (tail : List Cursor) (decision : Ordering)
      (evaluated : trace candidate head decision)
      (not_lt : decision ≠ Ordering.lt) :
      InsertCursorTrace before trace candidate (head :: tail) (candidate :: head :: tail)
  | after (head : Cursor) (tail inserted : List Cursor) (decision : Ordering)
      (evaluated : trace candidate head decision)
      (is_lt : decision = Ordering.lt)
      (deeper : InsertCursorTrace before trace candidate tail inserted) :
      InsertCursorTrace before trace candidate (head :: tail) (head :: inserted)

inductive SortCursorTrace
    (before : Cursor → Cursor → Option Ordering) (trace : BeforeTrace) :
    List Cursor → List Cursor → Prop
  | nil : SortCursorTrace before trace [] []
  | cons (head : Cursor) (tail sorted output : List Cursor)
      (tailTrace : SortCursorTrace before trace tail sorted)
      (insertion : InsertCursorTrace before trace head sorted output) :
      SortCursorTrace before trace (head :: tail) output

inductive RankedChildrenTrace (mol : RawMolecule)
    (before : Cursor → Cursor → Option Ordering) (trace : BeforeTrace) :
    Cursor → List Cursor → Prop
  | intro (cursor : Cursor) (children sorted : List Cursor)
      (children_eq : cursor.children mol = children)
      (width : ¬ 3 < children.length)
      (sorting : SortCursorTrace before trace children sorted) :
      RankedChildrenTrace mol before trace cursor
        (sorted ++ List.replicate (3 - sorted.length)
          { node := mol.canonicalPhantom cursor.node.atom
              (cursor.node.rule1bRootDistance + 1) })

inductive NextPairsTrace (mol : RawMolecule)
    (before : Cursor → Cursor → Option Ordering) (trace : BeforeTrace) :
    List CursorPair → List CursorPair → Prop
  | nil : NextPairsTrace mol before trace [] []
  | terminal (pair : CursorPair) (pairs rest : List CursorPair)
      (tailTrace : NextPairsTrace mol before trace pairs rest)
      (left_terminal : cursorTerminal mol pair.1 = true)
      (right_terminal : cursorTerminal mol pair.2 = true) :
      NextPairsTrace mol before trace (pair :: pairs) rest
  | expand (pair : CursorPair) (pairs rest : List CursorPair)
      (left right : List Cursor)
      (tailTrace : NextPairsTrace mol before trace pairs rest)
      (not_both_terminal : ¬
        (cursorTerminal mol pair.1 = true ∧ cursorTerminal mol pair.2 = true))
      (leftTrace : RankedChildrenTrace mol before trace pair.1 left)
      (rightTrace : RankedChildrenTrace mol before trace pair.2 right) :
      NextPairsTrace mol before trace (pair :: pairs) (left.zip right ++ rest)

inductive Rule6SphereTrace (mol : RawMolecule)
    (before : Cursor → Cursor → Option Ordering) (trace : BeforeTrace)
    (reference : Nat) : Nat → List CursorPair → Ordering → Prop
  | zero_decisive (pairs : List CursorPair) (decision : Ordering)
      (width : ¬ RawMolecule.defaultBranchWidthCap < pairs.length)
      (labels_eq : compareOccurrenceRule6PairLabels reference pairs = decision)
      (decisive : decision ≠ Ordering.eq) :
      Rule6SphereTrace mol before trace reference 0 pairs decision
  | zero_exhausted (pairs : List CursorPair)
      (width : ¬ RawMolecule.defaultBranchWidthCap < pairs.length)
      (labels_eq : compareOccurrenceRule6PairLabels reference pairs = Ordering.eq)
      (nextTrace : NextPairsTrace mol before trace pairs []) :
      Rule6SphereTrace mol before trace reference 0 pairs Ordering.eq
  | succ_decisive (fuel : Nat) (pairs : List CursorPair) (decision : Ordering)
      (width : ¬ RawMolecule.defaultBranchWidthCap < pairs.length)
      (labels_eq : compareOccurrenceRule6PairLabels reference pairs = decision)
      (decisive : decision ≠ Ordering.eq) :
      Rule6SphereTrace mol before trace reference (fuel + 1) pairs decision
  | succ_exhausted (fuel : Nat) (pairs : List CursorPair)
      (width : ¬ RawMolecule.defaultBranchWidthCap < pairs.length)
      (labels_eq : compareOccurrenceRule6PairLabels reference pairs = Ordering.eq)
      (nextTrace : NextPairsTrace mol before trace pairs []) :
      Rule6SphereTrace mol before trace reference (fuel + 1) pairs Ordering.eq
  | succ_next (fuel : Nat) (pairs next : List CursorPair) (decision : Ordering)
      (width : ¬ RawMolecule.defaultBranchWidthCap < pairs.length)
      (labels_eq : compareOccurrenceRule6PairLabels reference pairs = Ordering.eq)
      (nextTrace : NextPairsTrace mol before trace pairs next)
      (nonempty : next ≠ [])
      (deeper : Rule6SphereTrace mol before trace reference fuel next decision) :
      Rule6SphereTrace mol before trace reference (fuel + 1) pairs decision

/-- The recursive promoted comparator trace.  At every recursive level it retains a full
Rules-1--5 stage evaluation, and every callback comparison used by Rule 6 is traced at the
strictly smaller promoted-comparison fuel. -/
def PromotedComparisonTrace (aux : OccurrenceAuxState) (reference : Nat) :
    (fuel : Nat) → Cursor → Cursor → Rule6TrackedDecision → Prop
  | 0, left, right, result =>
      ∃ prior : OccurrenceComparison,
        ∃ _evaluation : Rule45Evaluation (mol := mol) aux 0
          { left := left, right := right, decision := prior },
        ((prior.ordering ≠ Ordering.eq ∧
            result = { ordering := prior.ordering, pseudo := false }) ∨
         (prior.ordering = Ordering.eq ∧
            let ordering := compare
              (if left.node.atom == reference then 1 else 0)
              (if right.node.atom == reference then 1 else 0)
            result = { ordering := ordering, pseudo := ordering != Ordering.eq }))
  | fuel + 1, left, right, result =>
      ∃ prior : OccurrenceComparison,
        ∃ _evaluation : Rule45Evaluation (mol := mol) aux (fuel + 1)
          { left := left, right := right, decision := prior },
        ((prior.ordering ≠ Ordering.eq ∧
            result = { ordering := prior.ordering, pseudo := false }) ∨
         (prior.ordering = Ordering.eq ∧
            ∃ ordering : Ordering,
              Rule6SphereTrace mol
                (fun a b =>
                  (compareOccurrenceBranchesThroughRule6At? mol aux reference fuel a b).map
                    Rule6TrackedDecision.ordering)
                (fun a b ordering =>
                  ∃ decision,
                    PromotedComparisonTrace aux reference fuel a b decision ∧
                    decision.ordering = ordering)
                reference (fuel + 1) [(left, right)] ordering ∧
              result = { ordering := ordering, pseudo := ordering != Ordering.eq }))

theorem InsertCursorTrace.sound
    {before : Cursor → Cursor → Option Ordering} {trace : BeforeTrace}
    (trace_sound : ∀ left right decision, trace left right decision →
      before left right = some decision)
    {candidate : Cursor} {input output : List Cursor}
    (derived : InsertCursorTrace before trace candidate input output) :
    insertCursorBy? before candidate input = some output := by
  induction derived with
  | nil => rfl
  | before head tail decision evaluated notLt =>
      cases decision <;> simp_all [insertCursorBy?, trace_sound _ _ _ evaluated]
  | after head tail inserted decision evaluated isLt deeper ih =>
      simp [insertCursorBy?, trace_sound _ _ _ evaluated, isLt, ih]

theorem insertCursorTrace_complete
    {before : Cursor → Cursor → Option Ordering} {trace : BeforeTrace}
    (trace_complete : ∀ left right decision, before left right = some decision →
      trace left right decision)
    (candidate : Cursor) (input output : List Cursor)
    (computed : insertCursorBy? before candidate input = some output) :
    InsertCursorTrace before trace candidate input output := by
  induction input generalizing output with
  | nil =>
      simp [insertCursorBy?] at computed
      subst output
      exact .nil
  | cons head tail ih =>
      simp only [insertCursorBy?] at computed
      cases comparisonEq : before candidate head with
      | none => simp [comparisonEq] at computed
      | some decision =>
          cases decision with
          | lt =>
              cases deeperEq : insertCursorBy? before candidate tail with
              | none => simp [comparisonEq, deeperEq] at computed
              | some inserted =>
                  have outputEq : output = head :: inserted := by
                    simpa [comparisonEq, deeperEq] using computed.symm
                  subst output
                  exact .after head tail inserted Ordering.lt
                    (trace_complete _ _ _ comparisonEq) rfl (ih inserted deeperEq)
          | eq =>
              have outputEq : output = candidate :: head :: tail := by
                simpa [comparisonEq] using computed.symm
              subst output
              exact .before head tail Ordering.eq
                (trace_complete _ _ _ comparisonEq) (by decide)
          | gt =>
              have outputEq : output = candidate :: head :: tail := by
                simpa [comparisonEq] using computed.symm
              subst output
              exact .before head tail Ordering.gt
                (trace_complete _ _ _ comparisonEq) (by decide)

theorem SortCursorTrace.sound
    {before : Cursor → Cursor → Option Ordering} {trace : BeforeTrace}
    (trace_sound : ∀ left right decision, trace left right decision →
      before left right = some decision)
    {input output : List Cursor} (derived : SortCursorTrace before trace input output) :
    sortCursorsBy? before input = some output := by
  induction derived with
  | nil => rfl
  | cons head tail sorted output tailTrace insertion ih =>
      simp [sortCursorsBy?, ih, insertion.sound trace_sound]

theorem sortCursorTrace_complete
    {before : Cursor → Cursor → Option Ordering} {trace : BeforeTrace}
    (trace_complete : ∀ left right decision, before left right = some decision →
      trace left right decision)
    (input output : List Cursor) (computed : sortCursorsBy? before input = some output) :
    SortCursorTrace before trace input output := by
  induction input generalizing output with
  | nil =>
      simp [sortCursorsBy?] at computed
      subst output
      exact .nil
  | cons head tail ih =>
      simp only [sortCursorsBy?] at computed
      cases sortedEq : sortCursorsBy? before tail with
      | none => simp [sortedEq] at computed
      | some sorted =>
          exact .cons head tail sorted output (ih sorted sortedEq)
            (insertCursorTrace_complete trace_complete head sorted output
              (by simpa [sortedEq] using computed))

theorem RankedChildrenTrace.sound
    {before : Cursor → Cursor → Option Ordering} {trace : BeforeTrace}
    (trace_sound : ∀ left right decision, trace left right decision →
      before left right = some decision)
    {cursor : Cursor} {output : List Cursor}
    (derived : RankedChildrenTrace mol before trace cursor output) :
    rankedCursorChildren? mol before cursor = some output := by
  cases derived with
  | intro children sorted childrenEq width sorting =>
      have widthLe : children.length ≤ 3 := Nat.le_of_not_gt width
      simp [rankedCursorChildren?, childrenEq, widthLe, sorting.sound trace_sound]

theorem rankedChildrenTrace_complete
    {before : Cursor → Cursor → Option Ordering} {trace : BeforeTrace}
    (trace_complete : ∀ left right decision, before left right = some decision →
      trace left right decision)
    (cursor : Cursor) (output : List Cursor)
    (computed : rankedCursorChildren? mol before cursor = some output) :
    RankedChildrenTrace mol before trace cursor output := by
  unfold rankedCursorChildren? at computed
  let children := cursor.children mol
  by_cases widthBad : 3 < children.length
  · simp [children, widthBad] at computed
  · cases sortedEq : sortCursorsBy? before children with
    | none => simp [children, widthBad, sortedEq] at computed
    | some sorted =>
        have outputEq : output = sorted ++ List.replicate (3 - sorted.length)
            { node := mol.canonicalPhantom cursor.node.atom
                (cursor.node.rule1bRootDistance + 1) } := by
          simpa [children, widthBad, sortedEq] using computed.symm
        subst output
        exact .intro cursor children sorted rfl widthBad
          (sortCursorTrace_complete trace_complete children sorted sortedEq)

theorem NextPairsTrace.sound
    {before : Cursor → Cursor → Option Ordering} {trace : BeforeTrace}
    (trace_sound : ∀ left right decision, trace left right decision →
      before left right = some decision)
    {input output : List CursorPair}
    (derived : NextPairsTrace mol before trace input output) :
    nextOccurrenceDescriptorPairs? mol before before input = some output := by
  induction derived with
  | nil => rfl
  | terminal pair pairs rest tailTrace leftTerminal rightTerminal ih =>
      simp [nextOccurrenceDescriptorPairs?, ih, leftTerminal, rightTerminal]
  | expand pair pairs rest left right tailTrace notBoth leftTrace rightTrace ih =>
      simp [nextOccurrenceDescriptorPairs?, ih, notBoth,
        leftTrace.sound trace_sound, rightTrace.sound trace_sound]

theorem nextPairsTrace_complete
    {before : Cursor → Cursor → Option Ordering} {trace : BeforeTrace}
    (trace_complete : ∀ left right decision, before left right = some decision →
      trace left right decision)
    (input output : List CursorPair)
    (computed : nextOccurrenceDescriptorPairs? mol before before input = some output) :
    NextPairsTrace mol before trace input output := by
  induction input generalizing output with
  | nil =>
      simp [nextOccurrenceDescriptorPairs?] at computed
      subst output
      exact .nil
  | cons pair pairs ih =>
      simp only [nextOccurrenceDescriptorPairs?] at computed
      cases restEq : nextOccurrenceDescriptorPairs? mol before before pairs with
      | none => simp [restEq] at computed
      | some rest =>
          by_cases terminal :
              cursorTerminal mol pair.1 = true ∧ cursorTerminal mol pair.2 = true
          · have outputEq : output = rest := by
              simpa [restEq, terminal] using computed.symm
            subst output
            exact .terminal pair pairs rest (ih rest restEq) terminal.1 terminal.2
          ·
            cases leftEq : rankedCursorChildren? mol before pair.1 with
            | none => simp [restEq, terminal, leftEq] at computed
            | some left =>
                cases rightEq : rankedCursorChildren? mol before pair.2 with
                | none => simp [restEq, terminal, leftEq, rightEq] at computed
                | some right =>
                    have outputEq : output = left.zip right ++ rest := by
                      simpa [restEq, terminal, leftEq, rightEq] using computed.symm
                    subst output
                    exact .expand pair pairs rest left right (ih rest restEq) terminal
                      (rankedChildrenTrace_complete trace_complete pair.1 left leftEq)
                      (rankedChildrenTrace_complete trace_complete pair.2 right rightEq)

theorem Rule6SphereTrace.sound
    {before : Cursor → Cursor → Option Ordering} {trace : BeforeTrace}
    (trace_sound : ∀ left right decision, trace left right decision →
      before left right = some decision)
    {reference sphereFuel : Nat} {pairs : List CursorPair} {decision : Ordering}
    (derived : Rule6SphereTrace mol before trace reference sphereFuel pairs decision) :
    compareOccurrenceRule6 mol before reference sphereFuel pairs = some decision := by
  induction derived with
  | zero_decisive pairs decision width labelsEq decisive =>
      have widthLe := Nat.le_of_not_gt width
      cases decision <;> simp_all [compareOccurrenceRule6]
  | zero_exhausted pairs width labelsEq nextTrace =>
      have widthLe := Nat.le_of_not_gt width
      simp [compareOccurrenceRule6, widthLe, labelsEq,
        nextTrace.sound trace_sound]
  | succ_decisive fuel pairs decision width labelsEq decisive =>
      have widthLe := Nat.le_of_not_gt width
      cases decision <;> simp_all [compareOccurrenceRule6]
  | succ_exhausted fuel pairs width labelsEq nextTrace =>
      have widthLe := Nat.le_of_not_gt width
      simp [compareOccurrenceRule6, widthLe, labelsEq,
        nextTrace.sound trace_sound]
  | succ_next fuel pairs next decision width labelsEq nextTrace nonempty deeper ih =>
      have widthLe := Nat.le_of_not_gt width
      simp [compareOccurrenceRule6, widthLe, labelsEq,
        nextTrace.sound trace_sound, ih]

theorem rule6SphereTrace_complete
    {before : Cursor → Cursor → Option Ordering} {trace : BeforeTrace}
    (trace_complete : ∀ left right decision, before left right = some decision →
      trace left right decision)
    (reference sphereFuel : Nat) (pairs : List CursorPair) (decision : Ordering)
    (computed : compareOccurrenceRule6 mol before reference sphereFuel pairs = some decision) :
    Rule6SphereTrace mol before trace reference sphereFuel pairs decision := by
  induction sphereFuel generalizing pairs decision with
  | zero =>
      simp only [compareOccurrenceRule6] at computed
      by_cases widthBad : RawMolecule.defaultBranchWidthCap < pairs.length
      · simp [widthBad] at computed
      · cases labelsEq : compareOccurrenceRule6PairLabels reference pairs with
        | lt =>
            have decisionEq : decision = Ordering.lt := by
              simpa [widthBad, labelsEq] using computed.symm
            subst decision
            exact .zero_decisive pairs Ordering.lt widthBad labelsEq (by decide)
        | gt =>
            have decisionEq : decision = Ordering.gt := by
              simpa [widthBad, labelsEq] using computed.symm
            subst decision
            exact .zero_decisive pairs Ordering.gt widthBad labelsEq (by decide)
        | eq =>
            cases nextEq : nextOccurrenceDescriptorPairs? mol before before pairs with
            | none => simp [widthBad, labelsEq, nextEq] at computed
            | some next =>
                cases next with
                | nil =>
                    have decisionEq : decision = Ordering.eq := by
                      simpa [widthBad, labelsEq, nextEq] using computed.symm
                    subst decision
                    exact .zero_exhausted pairs widthBad labelsEq
                      (nextPairsTrace_complete trace_complete pairs [] nextEq)
                | cons head tail => simp [widthBad, labelsEq, nextEq] at computed
  | succ fuel ih =>
      simp only [compareOccurrenceRule6] at computed
      by_cases widthBad : RawMolecule.defaultBranchWidthCap < pairs.length
      · simp [widthBad] at computed
      · cases labelsEq : compareOccurrenceRule6PairLabels reference pairs with
        | lt =>
            have decisionEq : decision = Ordering.lt := by
              simpa [widthBad, labelsEq] using computed.symm
            subst decision
            exact .succ_decisive fuel pairs Ordering.lt widthBad labelsEq (by decide)
        | gt =>
            have decisionEq : decision = Ordering.gt := by
              simpa [widthBad, labelsEq] using computed.symm
            subst decision
            exact .succ_decisive fuel pairs Ordering.gt widthBad labelsEq (by decide)
        | eq =>
            cases nextEq : nextOccurrenceDescriptorPairs? mol before before pairs with
            | none => simp [widthBad, labelsEq, nextEq] at computed
            | some next =>
                cases next with
                | nil =>
                    have decisionEq : decision = Ordering.eq := by
                      simpa [widthBad, labelsEq, nextEq] using computed.symm
                    subst decision
                    exact .succ_exhausted fuel pairs widthBad labelsEq
                      (nextPairsTrace_complete trace_complete pairs [] nextEq)
                | cons head tail =>
                    exact .succ_next fuel pairs (head :: tail) decision widthBad labelsEq
                      (nextPairsTrace_complete trace_complete pairs (head :: tail) nextEq)
                      (by simp) (ih (head :: tail) decision (by
                        simpa [widthBad, labelsEq, nextEq] using computed))

theorem PromotedComparisonTrace.sound
    (aux : OccurrenceAuxState) (reference : Nat) :
    ∀ {fuel : Nat} {left right : Cursor} {result : Rule6TrackedDecision},
      PromotedComparisonTrace (mol := mol) aux reference fuel left right result →
      compareOccurrenceBranchesThroughRule6At? mol aux reference fuel left right =
        some result := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right result derived
      rcases derived with ⟨prior, evaluation, priorCase⟩
      have priorEq := evaluation.production_eq
      rcases priorCase with ⟨notTie, resultEq⟩ | ⟨tie, resultEq⟩
      · subst result
        cases orderingEq : prior.ordering <;>
          simp_all [compareOccurrenceBranchesThroughRule6At?]
      · subst result
        simp [compareOccurrenceBranchesThroughRule6At?, priorEq, tie]
  | succ fuel ih =>
      intro left right result derived
      rcases derived with ⟨prior, evaluation, priorCase⟩
      have priorEq := evaluation.production_eq
      rcases priorCase with ⟨notTie, resultEq⟩ | ⟨tie, ordering, sphere, resultEq⟩
      · subst result
        cases orderingEq : prior.ordering <;>
          simp_all [compareOccurrenceBranchesThroughRule6At?]
      · subst result
        have callbackSound : ∀ a b decision,
            (∃ promoted,
                PromotedComparisonTrace (mol := mol) aux reference fuel a b promoted ∧
                promoted.ordering = decision) →
              ((compareOccurrenceBranchesThroughRule6At? mol aux reference fuel a b).map
                Rule6TrackedDecision.ordering) = some decision := by
          intro a b decision callback
          rcases callback with ⟨promoted, promotedTrace, rfl⟩
          simp [ih promotedTrace]
        have sphereEq := sphere.sound callbackSound
        simp [compareOccurrenceBranchesThroughRule6At?, priorEq, tie, sphereEq]

theorem promotedComparisonTrace_complete
    (aux : OccurrenceAuxState) (reference : Nat) :
    ∀ (fuel : Nat) (left right : Cursor) (result : Rule6TrackedDecision),
      compareOccurrenceBranchesThroughRule6At? mol aux reference fuel left right =
        some result →
      PromotedComparisonTrace (mol := mol) aux reference fuel left right result := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right result computed
      cases priorEq : compareOccurrenceBranches? mol aux 0 left right with
      | none => simp [compareOccurrenceBranchesThroughRule6At?, priorEq] at computed
      | some prior =>
          let evaluation := rule45Evaluation (mol := mol) aux 0
            ({ left := left, right := right, decision := prior }) priorEq
          by_cases tie : prior.ordering = Ordering.eq
          · have resultEq :
                result =
                  let ordering := compare
                    (if left.node.atom == reference then 1 else 0)
                    (if right.node.atom == reference then 1 else 0)
                  { ordering := ordering, pseudo := ordering != Ordering.eq } := by
              simpa [compareOccurrenceBranchesThroughRule6At?, priorEq, tie] using computed.symm
            exact ⟨prior, evaluation, Or.inr ⟨tie, resultEq⟩⟩
          · have resultEq : result =
                ({ ordering := prior.ordering, pseudo := false } : Rule6TrackedDecision) := by
              cases orderingEq : prior.ordering <;>
                simp_all [compareOccurrenceBranchesThroughRule6At?]
            exact ⟨prior, evaluation, Or.inl ⟨tie, resultEq⟩⟩
  | succ fuel ih =>
      intro left right result computed
      cases priorEq : compareOccurrenceBranches? mol aux (fuel + 1) left right with
      | none => simp [compareOccurrenceBranchesThroughRule6At?, priorEq] at computed
      | some prior =>
          let evaluation := rule45Evaluation (mol := mol) aux (fuel + 1)
            ({ left := left, right := right, decision := prior }) priorEq
          by_cases tie : prior.ordering = Ordering.eq
          · let before := fun a b =>
              (compareOccurrenceBranchesThroughRule6At? mol aux reference fuel a b).map
                Rule6TrackedDecision.ordering
            cases sphereEq : compareOccurrenceRule6 mol before reference (fuel + 1)
                [(left, right)] with
            | none =>
                simp [compareOccurrenceBranchesThroughRule6At?, priorEq, tie, before,
                  sphereEq] at computed
            | some ordering =>
                have resultEq : result =
                    ({ ordering := ordering, pseudo := ordering != Ordering.eq } :
                      Rule6TrackedDecision) := by
                  simpa [compareOccurrenceBranchesThroughRule6At?, priorEq, tie, before,
                    sphereEq] using computed.symm
                have callbackComplete : ∀ a b decision,
                    before a b = some decision →
                    ∃ promoted,
                      PromotedComparisonTrace (mol := mol) aux reference fuel a b promoted ∧
                      promoted.ordering = decision := by
                  intro a b decision callbackEq
                  unfold before at callbackEq
                  cases promotedEq :
                      compareOccurrenceBranchesThroughRule6At? mol aux reference fuel a b with
                  | none => simp [promotedEq] at callbackEq
                  | some promoted =>
                      have decisionEq : promoted.ordering = decision := by
                        simpa [promotedEq] using callbackEq
                      exact ⟨promoted, ih a b promoted promotedEq, decisionEq⟩
                have sphereTrace : Rule6SphereTrace mol before
                    (fun a b decision =>
                      ∃ promoted,
                        PromotedComparisonTrace (mol := mol) aux reference fuel a b promoted ∧
                        promoted.ordering = decision)
                    reference (fuel + 1) [(left, right)] ordering :=
                  rule6SphereTrace_complete callbackComplete reference (fuel + 1)
                    [(left, right)] ordering sphereEq
                exact ⟨prior, evaluation, Or.inr ⟨tie, ordering, sphereTrace, resultEq⟩⟩
          · have resultEq : result =
                ({ ordering := prior.ordering, pseudo := false } : Rule6TrackedDecision) := by
              cases orderingEq : prior.ordering <;>
                simp_all [compareOccurrenceBranchesThroughRule6At?]
            exact ⟨prior, evaluation, Or.inl ⟨tie, resultEq⟩⟩

theorem promotedComparisonTrace_iff
    (aux : OccurrenceAuxState) (reference fuel : Nat)
    (left right : Cursor) (result : Rule6TrackedDecision) :
    PromotedComparisonTrace (mol := mol) aux reference fuel left right result ↔
      compareOccurrenceBranchesThroughRule6At? mol aux reference fuel left right =
        some result :=
  ⟨PromotedComparisonTrace.sound aux reference,
    promotedComparisonTrace_complete aux reference fuel left right result⟩

inductive PositionPromotedComparisonTrace (aux : OccurrenceAuxState) (fuel : Nat)
    (roots : List Cursor) (ligands : List Nat)
    (referencePosition leftPosition rightPosition : Nat) :
    Rule6TrackedDecision → Prop
  | intro (reference : Nat) (left right : Cursor) (decision : Rule6TrackedDecision)
      (reference_eq : ligands[referencePosition]? = some reference)
      (left_eq : roots[leftPosition]? = some left)
      (right_eq : roots[rightPosition]? = some right)
      (promoted : PromotedComparisonTrace (mol := mol) aux reference fuel left right decision) :
      PositionPromotedComparisonTrace aux fuel roots ligands
        referencePosition leftPosition rightPosition decision

theorem PositionPromotedComparisonTrace.sound
    {aux : OccurrenceAuxState} {fuel : Nat} {roots : List Cursor} {ligands : List Nat}
    {referencePosition leftPosition rightPosition : Nat} {decision : Rule6TrackedDecision}
    (derived : PositionPromotedComparisonTrace (mol := mol) aux fuel roots ligands
      referencePosition leftPosition rightPosition decision) :
    comparePositionsThroughRule6? (mol := mol) aux fuel roots ligands referencePosition
      leftPosition rightPosition = some decision := by
  cases derived with
  | intro reference left right decision referenceEq leftEq rightEq promoted =>
      simp [comparePositionsThroughRule6?, referenceEq, leftEq, rightEq,
        promoted.sound aux reference]

theorem positionPromotedComparisonTrace_complete
    (aux : OccurrenceAuxState) (fuel : Nat) (roots : List Cursor) (ligands : List Nat)
    (referencePosition leftPosition rightPosition : Nat) (decision : Rule6TrackedDecision)
    (computed : comparePositionsThroughRule6? (mol := mol) aux fuel roots ligands
      referencePosition leftPosition rightPosition = some decision) :
    PositionPromotedComparisonTrace (mol := mol) aux fuel roots ligands
      referencePosition leftPosition rightPosition decision := by
  unfold comparePositionsThroughRule6? at computed
  cases referenceEq : ligands[referencePosition]? with
  | none => simp [referenceEq] at computed
  | some reference =>
      cases leftEq : roots[leftPosition]? with
      | none => simp [referenceEq, leftEq] at computed
      | some left =>
          cases rightEq : roots[rightPosition]? with
          | none => simp [referenceEq, leftEq, rightEq] at computed
          | some right =>
              exact .intro reference left right decision referenceEq leftEq rightEq
                (promotedComparisonTrace_complete aux reference fuel left right decision
                  (by simpa [referenceEq, leftEq, rightEq] using computed))

inductive InsertPromotedPositionTrace (aux : OccurrenceAuxState) (fuel : Nat)
    (roots : List Cursor) (ligands : List Nat) (referencePosition candidate : Nat) :
    List Nat → (List Nat × Nat × Bool) → Prop
  | nil : InsertPromotedPositionTrace aux fuel roots ligands referencePosition candidate
      [] ([candidate], 0, true)
  | lt (low : Nat) (remaining : List Nat) (decision : Rule6TrackedDecision)
      (deeper : List Nat × Nat × Bool)
      (comparison : PositionPromotedComparisonTrace (mol := mol) aux fuel roots ligands
        referencePosition low candidate decision)
      (is_lt : decision.ordering = Ordering.lt)
      (tail : InsertPromotedPositionTrace aux fuel roots ligands referencePosition candidate
        remaining deeper) :
      InsertPromotedPositionTrace aux fuel roots ligands referencePosition candidate
        (low :: remaining)
        (low :: deeper.1, (if decision.pseudo then 1 else 0) + deeper.2.1, deeper.2.2)
  | eq (low : Nat) (remaining : List Nat) (decision : Rule6TrackedDecision)
      (comparison : PositionPromotedComparisonTrace (mol := mol) aux fuel roots ligands
        referencePosition low candidate decision)
      (is_eq : decision.ordering = Ordering.eq) :
      InsertPromotedPositionTrace aux fuel roots ligands referencePosition candidate
        (low :: remaining)
        (candidate :: low :: remaining, (if decision.pseudo then 1 else 0), false)
  | gt (low : Nat) (remaining : List Nat) (decision : Rule6TrackedDecision)
      (comparison : PositionPromotedComparisonTrace (mol := mol) aux fuel roots ligands
        referencePosition low candidate decision)
      (is_gt : decision.ordering = Ordering.gt) :
      InsertPromotedPositionTrace aux fuel roots ligands referencePosition candidate
        (low :: remaining)
        (candidate :: low :: remaining, (if decision.pseudo then 1 else 0), true)

theorem InsertPromotedPositionTrace.sound
    {aux : OccurrenceAuxState} {fuel : Nat} {roots : List Cursor} {ligands : List Nat}
    {referencePosition candidate : Nat} {input : List Nat}
    {output : List Nat × Nat × Bool}
    (derived : InsertPromotedPositionTrace (mol := mol) aux fuel roots ligands
      referencePosition candidate input output) :
    insertOccurrencePositionRule6Tracked? (mol := mol) aux fuel roots ligands
      referencePosition candidate input = some output := by
  induction derived with
  | nil => rfl
  | lt low remaining decision deeper comparison isLt tail ih =>
      simp [insertOccurrencePositionRule6Tracked?, comparison.sound, isLt, ih]
  | eq low remaining decision comparison isEq =>
      simp [insertOccurrencePositionRule6Tracked?, comparison.sound, isEq]
  | gt low remaining decision comparison isGt =>
      simp [insertOccurrencePositionRule6Tracked?, comparison.sound, isGt]

theorem insertPromotedPositionTrace_complete
    (aux : OccurrenceAuxState) (fuel : Nat) (roots : List Cursor) (ligands : List Nat)
    (referencePosition candidate : Nat) (input : List Nat)
    (output : List Nat × Nat × Bool)
    (computed : insertOccurrencePositionRule6Tracked? (mol := mol) aux fuel roots ligands
      referencePosition candidate input = some output) :
    InsertPromotedPositionTrace (mol := mol) aux fuel roots ligands
      referencePosition candidate input output := by
  induction input generalizing output with
  | nil =>
      simp [insertOccurrencePositionRule6Tracked?] at computed
      subst output
      exact .nil
  | cons low remaining ih =>
      simp only [insertOccurrencePositionRule6Tracked?] at computed
      cases comparisonEq : comparePositionsThroughRule6? (mol := mol) aux fuel roots ligands
          referencePosition low candidate with
      | none => simp [comparisonEq] at computed
      | some decision =>
          have comparison := positionPromotedComparisonTrace_complete aux fuel roots ligands
            referencePosition low candidate decision comparisonEq
          cases orderingEq : decision.ordering with
          | lt =>
              cases deeperEq : insertOccurrencePositionRule6Tracked? (mol := mol) aux fuel
                  roots ligands referencePosition candidate remaining with
              | none => simp [comparisonEq, orderingEq, deeperEq] at computed
              | some deeper =>
                  have outputEq : output =
                      (low :: deeper.1,
                        (if decision.pseudo then 1 else 0) + deeper.2.1, deeper.2.2) := by
                    simpa [comparisonEq, orderingEq, deeperEq] using computed.symm
                  subst output
                  exact .lt low remaining decision deeper comparison orderingEq
                    (ih deeper deeperEq)
          | eq =>
              have outputEq : output =
                  (candidate :: low :: remaining,
                    (if decision.pseudo then 1 else 0), false) := by
                simpa [comparisonEq, orderingEq] using computed.symm
              subst output
              exact .eq low remaining decision comparison orderingEq
          | gt =>
              have outputEq : output =
                  (candidate :: low :: remaining,
                    (if decision.pseudo then 1 else 0), true) := by
                simpa [comparisonEq, orderingEq] using computed.symm
              subst output
              exact .gt low remaining decision comparison orderingEq

inductive FoldPromotedPositionsTrace (aux : OccurrenceAuxState) (fuel : Nat)
    (roots : List Cursor) (ligands : List Nat) (referencePosition : Nat) :
    List Nat → (List Nat × Nat × Bool) → (List Nat × Nat × Bool) → Prop
  | nil (accumulator : List Nat × Nat × Bool) :
      FoldPromotedPositionsTrace aux fuel roots ligands referencePosition [] accumulator accumulator
  | cons (candidate : Nat) (remaining : List Nat)
      (accumulator inserted output : List Nat × Nat × Bool)
      (insertion : InsertPromotedPositionTrace (mol := mol) aux fuel roots ligands
        referencePosition candidate accumulator.1 inserted)
      (tail : FoldPromotedPositionsTrace aux fuel roots ligands referencePosition remaining
        (inserted.1, accumulator.2.1 + inserted.2.1,
          accumulator.2.2 && inserted.2.2) output) :
      FoldPromotedPositionsTrace aux fuel roots ligands referencePosition
        (candidate :: remaining) accumulator output

theorem FoldPromotedPositionsTrace.sound
    {aux : OccurrenceAuxState} {fuel : Nat} {roots : List Cursor} {ligands : List Nat}
    {referencePosition : Nat} {input : List Nat}
    {accumulator output : List Nat × Nat × Bool}
    (derived : FoldPromotedPositionsTrace (mol := mol) aux fuel roots ligands
      referencePosition input accumulator output) :
    input.foldlM (fun accumulator candidate => do
      let inserted ← insertOccurrencePositionRule6Tracked? (mol := mol) aux fuel roots ligands
        referencePosition candidate accumulator.1
      some (inserted.1, accumulator.2.1 + inserted.2.1,
        accumulator.2.2 && inserted.2.2)) accumulator = some output := by
  induction derived with
  | nil accumulator => rfl
  | cons candidate remaining accumulator inserted output insertion tail ih =>
      simp only [List.foldlM]
      rw [insertion.sound]
      exact ih

theorem foldPromotedPositionsTrace_complete
    (aux : OccurrenceAuxState) (fuel : Nat) (roots : List Cursor) (ligands : List Nat)
    (referencePosition : Nat) (input : List Nat)
    (accumulator output : List Nat × Nat × Bool)
    (computed : input.foldlM (fun accumulator candidate => do
      let inserted ← insertOccurrencePositionRule6Tracked? (mol := mol) aux fuel roots ligands
        referencePosition candidate accumulator.1
      some (inserted.1, accumulator.2.1 + inserted.2.1,
        accumulator.2.2 && inserted.2.2)) accumulator = some output) :
    FoldPromotedPositionsTrace (mol := mol) aux fuel roots ligands referencePosition
      input accumulator output := by
  induction input generalizing accumulator with
  | nil =>
      simp [List.foldlM] at computed
      subst output
      exact .nil accumulator
  | cons candidate remaining ih =>
      simp only [List.foldlM] at computed
      cases insertedEq : insertOccurrencePositionRule6Tracked? (mol := mol) aux fuel roots
          ligands referencePosition candidate accumulator.1 with
      | none => simp [insertedEq] at computed
      | some inserted =>
          exact .cons candidate remaining accumulator inserted output
            (insertPromotedPositionTrace_complete aux fuel roots ligands referencePosition
              candidate accumulator.1 inserted insertedEq)
            (ih (inserted.1, accumulator.2.1 + inserted.2.1,
              accumulator.2.2 && inserted.2.2) (by simpa [insertedEq] using computed))

inductive PromotedRankingTrace (aux : OccurrenceAuxState) (fuel : Nat)
    (roots : List Cursor) (ligands start : List Nat) (referencePosition : Nat) :
    Rule6TrackedRanking → Prop
  | intro (tracked : List Nat × Nat × Bool)
      (fold : FoldPromotedPositionsTrace (mol := mol) aux fuel roots ligands
        referencePosition start ([], 0, true) tracked) :
      PromotedRankingTrace aux fuel roots ligands start referencePosition
        { positions := tracked.1.reverse
          pseudoComparisons := tracked.2.1
          unique := tracked.2.2 }

theorem PromotedRankingTrace.sound
    {aux : OccurrenceAuxState} {fuel : Nat} {roots : List Cursor} {ligands start : List Nat}
    {referencePosition : Nat} {ranking : Rule6TrackedRanking}
    (derived : PromotedRankingTrace (mol := mol) aux fuel roots ligands start
      referencePosition ranking) :
    rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands start
      referencePosition = some ranking := by
  cases derived with
  | intro tracked fold =>
      unfold rankOccurrencePositionsThroughRule6Tracked?
      rw [fold.sound]
      rfl

theorem promotedRankingTrace_complete
    (aux : OccurrenceAuxState) (fuel : Nat) (roots : List Cursor) (ligands start : List Nat)
    (referencePosition : Nat) (ranking : Rule6TrackedRanking)
    (computed : rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands
      start referencePosition = some ranking) :
    PromotedRankingTrace (mol := mol) aux fuel roots ligands start referencePosition ranking := by
  unfold rankOccurrencePositionsThroughRule6Tracked? at computed
  let foldCall := start.foldlM (fun accumulator candidate => do
    let inserted ← insertOccurrencePositionRule6Tracked? (mol := mol) aux fuel roots ligands
      referencePosition candidate accumulator.1
    some (inserted.1, accumulator.2.1 + inserted.2.1,
      accumulator.2.2 && inserted.2.2)) ([], 0, true)
  change foldCall.bind (fun tracked => some
    { positions := tracked.1.reverse
      pseudoComparisons := tracked.2.1
      unique := tracked.2.2 }) = some ranking at computed
  cases foldEq : foldCall with
  | none => simp [foldEq] at computed
  | some tracked =>
      have rankingEq : ranking =
          ({ positions := tracked.1.reverse
             pseudoComparisons := tracked.2.1
             unique := tracked.2.2 } : Rule6TrackedRanking) := by
        simpa [foldEq] using computed.symm
      subst ranking
      exact .intro tracked
        (foldPromotedPositionsTrace_complete aux fuel roots ligands referencePosition start
          ([], 0, true) tracked (by simpa [foldCall] using foldEq))

theorem promotedRankingTrace_iff
    (aux : OccurrenceAuxState) (fuel : Nat) (roots : List Cursor) (ligands start : List Nat)
    (referencePosition : Nat) (ranking : Rule6TrackedRanking) :
    PromotedRankingTrace (mol := mol) aux fuel roots ligands start referencePosition ranking ↔
      rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands start
        referencePosition = some ranking :=
  ⟨PromotedRankingTrace.sound,
    promotedRankingTrace_complete aux fuel roots ligands start referencePosition ranking⟩

/-- Descriptor produced by one complete promoted-reference ranking. -/
def ProductionOccurrenceRule6DescriptorJudgment (aux : OneCenter.OccurrenceAuxState)
    (fuel : Nat) (roots : List CanonicalRerootCursor) (ligands sorted : List Nat)
    (parity : TetrahedralInputParity) (referencePosition : Nat) (descriptor : RS) : Prop :=
  ProductionRule6BackendDescriptorJudgment
    (fun reference =>
      rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands sorted
        reference)
    parity referencePosition descriptor

/-- The root-relative occurrence-state instance of the shared production Rule-6 ranking
backend. -/
def productionOccurrenceRule6RankingBackend (aux : OneCenter.OccurrenceAuxState)
    (fuel : Nat) (roots : List CanonicalRerootCursor) (ligands sorted : List Nat) :
    ProductionRule6RankingBackend :=
  fun reference =>
    rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands sorted
      reference

/-- Check every admissible reference in the complete two-group reference class. -/
def rankOccurrenceEquivalentReferences? (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (parity : TetrahedralInputParity)
    (ligands sorted references : List Nat) : Option Rule6TrackedRanking :=
  rankProductionRule6EquivalentReferencesWithBackend?
    (productionOccurrenceRule6RankingBackend (mol := mol) aux fuel roots ligands sorted)
    parity references

/-- Occurrence-specific proof of all equivalent-reference rankings.  Ranking success is never
stored as an equation: each reference carries the complete promoted-comparison trace above. -/
structure OccurrenceEquivalentReferencesTrace
    (aux : OccurrenceAuxState) (fuel : Nat) (roots : List Cursor)
    (parity : TetrahedralInputParity) (ligands sorted references : List Nat)
    (first : Rule6TrackedRanking) where
  firstReferencePosition : Nat
  reference_head : references.head? = some firstReferencePosition
  first_trace : PromotedRankingTrace (mol := mol) aux fuel roots ligands sorted
    firstReferencePosition first
  first_unique : first.unique = true
  all_references : ∀ referencePosition, referencePosition ∈ references →
    ∃ ranking,
      PromotedRankingTrace (mol := mol) aux fuel roots ligands sorted referencePosition ranking ∧
      ranking.unique = true ∧
      RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven ranking.positions) =
        RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven first.positions)

theorem OccurrenceEquivalentReferencesTrace.sound
    {aux : OccurrenceAuxState} {fuel : Nat} {roots : List Cursor}
    {parity : TetrahedralInputParity} {ligands sorted references : List Nat}
    {first : Rule6TrackedRanking}
    (derived : OccurrenceEquivalentReferencesTrace (mol := mol) aux fuel roots parity ligands
      sorted references first) :
    rankOccurrenceEquivalentReferences? (mol := mol) aux fuel roots parity ligands sorted
      references = some first := by
  apply rankProductionRule6EquivalentReferencesWithBackend?_complete
    (productionOccurrenceRule6RankingBackend (mol := mol) aux fuel roots ligands sorted)
    parity references first
  refine
    { firstReferencePosition := derived.firstReferencePosition
      reference_head := derived.reference_head
      first_ranking := ?_
      first_unique := derived.first_unique
      all_references := ?_ }
  · simpa [productionOccurrenceRule6RankingBackend] using derived.first_trace.sound
  · intro referencePosition member
    rcases derived.all_references referencePosition member with
      ⟨ranking, rankingTrace, unique, descriptorEq⟩
    exact ⟨ranking,
      (by simpa [productionOccurrenceRule6RankingBackend] using rankingTrace.sound),
      unique, descriptorEq⟩

theorem occurrenceEquivalentReferencesTrace_complete
    (aux : OccurrenceAuxState) (fuel : Nat) (roots : List Cursor)
    (parity : TetrahedralInputParity) (ligands sorted references : List Nat)
    (first : Rule6TrackedRanking)
    (computed : rankOccurrenceEquivalentReferences? (mol := mol) aux fuel roots parity ligands
      sorted references = some first) :
    Nonempty (OccurrenceEquivalentReferencesTrace (mol := mol) aux fuel roots parity ligands
      sorted references first) := by
  rcases rankProductionRule6EquivalentReferencesWithBackend?_sound
      (productionOccurrenceRule6RankingBackend (mol := mol) aux fuel roots ligands sorted)
      parity references first computed with ⟨certificate⟩
  refine ⟨
    { firstReferencePosition := certificate.firstReferencePosition
      reference_head := certificate.reference_head
      first_trace := promotedRankingTrace_complete aux fuel roots ligands sorted
        certificate.firstReferencePosition first ?_
      first_unique := certificate.first_unique
      all_references := ?_ }⟩
  · simpa [productionOccurrenceRule6RankingBackend] using certificate.first_ranking
  · intro referencePosition member
    rcases certificate.all_references referencePosition member with
      ⟨ranking, rankingEq, unique, descriptorEq⟩
    exact ⟨ranking,
      promotedRankingTrace_complete aux fuel roots ligands sorted referencePosition ranking
        (by simpa [productionOccurrenceRule6RankingBackend] using rankingEq),
      unique, descriptorEq⟩

theorem occurrenceEquivalentReferencesTrace_iff
    (aux : OccurrenceAuxState) (fuel : Nat) (roots : List Cursor)
    (parity : TetrahedralInputParity) (ligands sorted references : List Nat)
    (first : Rule6TrackedRanking) :
    Nonempty (OccurrenceEquivalentReferencesTrace (mol := mol) aux fuel roots parity ligands
      sorted references first) ↔
      rankOccurrenceEquivalentReferences? (mol := mol) aux fuel roots parity ligands sorted
        references = some first := by
  constructor
  · rintro ⟨derived⟩
    exact derived.sound
  · intro computed
    exact occurrenceEquivalentReferencesTrace_complete aux fuel roots parity ligands sorted
      references first computed

/-- Two promoted orders for the four-way carrier. -/
def rankOccurrenceFourWayReferences? (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (parity : TetrahedralInputParity)
    (ligands sorted : List Nat) : Option Rule6FourWayAgreement := do
  let firstPosition ← sorted[0]?
  let first ← rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands
    sorted firstPosition
  let secondReference := first.positions.getD 1 0
  let second ← rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands
    first.positions secondReference
  let firstDescriptor := RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven first.positions)
  let secondDescriptor := RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven second.positions)
  if first.positions != second.positions && firstDescriptor == secondDescriptor &&
      first.unique == second.unique then
    some
      { firstRanking := first
        secondRanking := second
        descriptor := if second.unique then secondDescriptor else RS.swap secondDescriptor }
  else none

/-- Occurrence-specific two-promotion S4 certificate.  Both ranking computations are full
promoted traces; only the frame lookup and semantic agreement proposition remain as data. -/
structure OccurrenceFourWayTrace
    (aux : OccurrenceAuxState) (fuel : Nat) (roots : List Cursor)
    (parity : TetrahedralInputParity) (ligands sorted : List Nat)
    (agreement : Rule6FourWayAgreement) where
  firstPosition : Nat
  first_position : sorted[0]? = some firstPosition
  first_trace : PromotedRankingTrace (mol := mol) aux fuel roots ligands sorted
    firstPosition agreement.firstRanking
  second_trace : PromotedRankingTrace (mol := mol) aux fuel roots ligands
    agreement.firstRanking.positions (agreement.firstRanking.positions[1]?.getD 0)
    agreement.secondRanking
  production : Rule6FourWayAgreementCertificate parity agreement

theorem OccurrenceFourWayTrace.sound
    {aux : OccurrenceAuxState} {fuel : Nat} {roots : List Cursor}
    {parity : TetrahedralInputParity} {ligands sorted : List Nat}
    {agreement : Rule6FourWayAgreement}
    (derived : OccurrenceFourWayTrace (mol := mol) aux fuel roots parity ligands sorted
      agreement) :
    rankOccurrenceFourWayReferences? (mol := mol) aux fuel roots parity ligands sorted =
      some agreement := by
  rcases derived.production with ⟨different, sameDescriptor, sameUnique, descriptorEq⟩
  have agreementEq :
      ({ firstRanking := agreement.firstRanking
         secondRanking := agreement.secondRanking
         descriptor := if agreement.secondRanking.unique then
           RawMolecule.descriptorOfParity parity
             (RawMolecule.permutationIsEven agreement.secondRanking.positions)
         else RS.swap (RawMolecule.descriptorOfParity parity
           (RawMolecule.permutationIsEven agreement.secondRanking.positions)) } :
        Rule6FourWayAgreement) = agreement := by
    cases agreement
    simp_all
  unfold rankOccurrenceFourWayReferences?
  simp [derived.first_position, derived.first_trace.sound, derived.second_trace.sound,
    different, sameDescriptor, sameUnique, agreementEq]

theorem occurrenceFourWayTrace_complete
    (aux : OccurrenceAuxState) (fuel : Nat) (roots : List Cursor)
    (parity : TetrahedralInputParity) (ligands sorted : List Nat)
    (agreement : Rule6FourWayAgreement)
    (computed : rankOccurrenceFourWayReferences? (mol := mol) aux fuel roots parity ligands
      sorted = some agreement) :
    Nonempty (OccurrenceFourWayTrace (mol := mol) aux fuel roots parity ligands sorted
      agreement) := by
  unfold rankOccurrenceFourWayReferences? at computed
  cases firstPositionEq : sorted[0]? with
  | none => simp [firstPositionEq] at computed
  | some firstPosition =>
      cases firstEq : rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots
          ligands sorted firstPosition with
      | none => simp [firstPositionEq, firstEq] at computed
      | some first =>
          cases secondEq : rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots
              ligands first.positions (first.positions[1]?.getD 0) with
          | none => simp [firstPositionEq, firstEq, secondEq] at computed
          | some second =>
              let firstDescriptor := RawMolecule.descriptorOfParity parity
                (RawMolecule.permutationIsEven first.positions)
              let secondDescriptor := RawMolecule.descriptorOfParity parity
                (RawMolecule.permutationIsEven second.positions)
              by_cases different : first.positions ≠ second.positions
              · by_cases sameDescriptor : firstDescriptor = secondDescriptor
                · by_cases sameUnique : first.unique = second.unique
                  · have agreementEq :
                        ({ firstRanking := first
                           secondRanking := second
                           descriptor := if second.unique then secondDescriptor
                             else RS.swap secondDescriptor } : Rule6FourWayAgreement) = agreement := by
                      apply Option.some.inj
                      simpa [firstPositionEq, firstEq, secondEq, firstDescriptor,
                        secondDescriptor, different, sameDescriptor, sameUnique] using computed
                    subst agreement
                    refine ⟨
                      { firstPosition := firstPosition
                        first_position := firstPositionEq
                        first_trace := promotedRankingTrace_complete aux fuel roots ligands sorted
                          firstPosition first firstEq
                        second_trace := promotedRankingTrace_complete aux fuel roots ligands
                          first.positions (first.positions[1]?.getD 0) second secondEq
                        production := ?_ }⟩
                    exact ⟨different, sameDescriptor, sameUnique, rfl⟩
                  · simp [firstPositionEq, firstEq, secondEq, firstDescriptor,
                      secondDescriptor, different, sameDescriptor, sameUnique] at computed
                · simp [firstPositionEq, firstEq, secondEq, firstDescriptor,
                    secondDescriptor, different, sameDescriptor] at computed
              · simp [firstPositionEq, firstEq, secondEq, different] at computed

theorem occurrenceFourWayTrace_iff
    (aux : OccurrenceAuxState) (fuel : Nat) (roots : List Cursor)
    (parity : TetrahedralInputParity) (ligands sorted : List Nat)
    (agreement : Rule6FourWayAgreement) :
    Nonempty (OccurrenceFourWayTrace (mol := mol) aux fuel roots parity ligands sorted agreement) ↔
      rankOccurrenceFourWayReferences? (mol := mol) aux fuel roots parity ligands sorted =
        some agreement := by
  constructor
  · rintro ⟨derived⟩
    exact derived.sound
  · intro computed
    exact occurrenceFourWayTrace_complete aux fuel roots parity ligands sorted agreement computed


/-- A descriptor fact occurs on the promoted branch itself, not merely elsewhere in the root. -/
def occurrenceBranchHasLocalReference (aux : OneCenter.OccurrenceAuxState) :
    Nat → List CanonicalRerootCursor → Bool
  | 0, frontier => frontier.any fun cursor => (aux.factAt? cursor.node).isSome
  | fuel + 1, frontier =>
      (frontier.any fun cursor => (aux.factAt? cursor.node).isSome) ||
        occurrenceBranchHasLocalReference aux fuel
          (frontier.flatMap fun cursor => cursor.children mol)

inductive OccurrenceRule6Carrier
  | twoGroup (references : List Nat) (ranking : Rule6TrackedRanking)
  | threeGroup (reference : Nat) (ranking : Rule6TrackedRanking)
  | fourWay (agreement : Rule6FourWayAgreement)
  deriving DecidableEq, Repr

structure OccurrenceRule6Result where
  fact : OccurrenceAuxFact
  parity : TetrahedralInputParity
  ligands : List Nat
  roots : List CanonicalRerootCursor
  sorted : List Nat
  adjacent : List (Option Ordering)
  groupCount : Nat
  oddTopology? : Option Bool
  carrier : OccurrenceRule6Carrier
  deriving DecidableEq, Repr

/-! ### Complete initial Rule-6 partition certificate -/

/-- Insertion retains exactly the candidate and the original input positions. -/
theorem InsertRule6InitialDerivation.perm
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor} {candidate : Nat} {input output : List Nat}
    (derived : InsertRule6InitialDerivation (mol := mol) aux fuel roots candidate input output) :
    output.Perm (candidate :: input) := by
  induction derived with
  | nil => exact List.Perm.refl _
  | before => exact List.Perm.refl _
  | after head tail inserted decision evaluation isLt deeper inductionHypothesis =>
      exact (List.Perm.cons head inductionHypothesis).trans
        (List.Perm.swap candidate head tail)

/-- The fail-closed structural sort is a permutation of its complete input. -/
theorem SortRule6InitialDerivation.perm
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor} {input output : List Nat}
    (derived : SortRule6InitialDerivation (mol := mol) aux fuel roots input output) :
    output.Perm input := by
  induction derived with
  | nil => exact List.Perm.refl _
  | cons position positions sorted output tail insertion inductionHypothesis =>
      exact insertion.perm.trans (List.Perm.cons position inductionHypothesis)

/-- Adjacent traversal returns one fewer comparison than positions, with the empty case truncated
at zero. -/
theorem Rule6InitialAdjacentDerivation.length_eq_pred
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor} {input : List Nat}
    {output : List (Option Ordering)}
    (derived : Rule6InitialAdjacentDerivation (mol := mol) aux fuel roots input output) :
    output.length = input.length - 1 := by
  induction derived with
  | nil => simp
  | singleton => simp
  | cons left right remaining decision deeper evaluation tail inductionHypothesis =>
      simp at inductionHypothesis ⊢
      omega

/-- Every structurally traversed adjacent entry is the ordering of an actual successful
comparison; missing labels cannot appear in the returned list. -/
theorem Rule6InitialAdjacentDerivation.mem_some
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor} {input : List Nat}
    {output : List (Option Ordering)}
    (derived : Rule6InitialAdjacentDerivation (mol := mol) aux fuel roots input output)
    {entry : Option Ordering} (member : entry ∈ output) :
    ∃ ordering, entry = some ordering := by
  induction derived with
  | nil => simp at member
  | singleton => simp at member
  | cons left right remaining decision deeper evaluation tail inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨decision.ordering, rfl⟩
      · exact inductionHypothesis member

/-- Number of strict Rules-1--5 boundaries preceding a sorted rank. -/
def rule6InitialGroupIndex (adjacent : List (Option Ordering)) (rank : Nat) : Nat :=
  (adjacent.take rank).count (some Ordering.gt)

/-- Total comparison of partition indices, oriented with the senior group first. -/
def rule6GroupOrdering (leftGroup rightGroup : Nat) : Ordering :=
  if leftGroup = rightGroup then Ordering.eq
  else if leftGroup < rightGroup then Ordering.gt else Ordering.lt

/-- The complete partition requires equality inside one Rules-1--5 group, `gt` from a senior
group to a junior group, and `lt` in the reverse direction. -/
def rule6ExpectedPartitionOrdering (adjacent : List (Option Ordering))
    (leftRank rightRank : Nat) : Ordering :=
  rule6GroupOrdering (rule6InitialGroupIndex adjacent leftRank)
    (rule6InitialGroupIndex adjacent rightRank)

/-- Partial composition for comparison outcomes. Oppositely directed strict comparisons do not
determine the endpoints and therefore return `none`. -/
def composeOrdering? : Ordering → Ordering → Option Ordering
  | .eq, ordering | ordering, .eq => some ordering
  | .gt, .gt => some .gt
  | .lt, .lt => some .lt
  | .gt, .lt | .lt, .gt => none

@[simp] theorem rule6GroupOrdering_eq_iff (left right : Nat) :
    rule6GroupOrdering left right = Ordering.eq ↔ left = right := by
  unfold rule6GroupOrdering
  by_cases equal : left = right
  · simp [equal]
  · by_cases less : left < right
    · simp [equal, less]
    · simp [equal, less]

@[simp] theorem rule6GroupOrdering_gt_iff (left right : Nat) :
    rule6GroupOrdering left right = Ordering.gt ↔ left < right := by
  unfold rule6GroupOrdering
  by_cases equal : left = right
  · simp [equal]
  · by_cases less : left < right
    · simp [equal, less]
    · simp [equal, less]

@[simp] theorem rule6GroupOrdering_lt_iff (left right : Nat) :
    rule6GroupOrdering left right = Ordering.lt ↔ right < left := by
  unfold rule6GroupOrdering
  by_cases equal : left = right
  · simp [equal]
  · by_cases less : left < right
    · have notReverse : ¬ right < left := by omega
      simp [equal, less, notReverse]
    · have reverse : right < left := by omega
      simp [equal, less, reverse]

/-- Whenever two group-index comparisons compose, their composition is exactly the direct
group-index comparison. -/
theorem rule6GroupOrdering_compose {left middle right : Nat} {composed : Ordering}
    (composition : composeOrdering? (rule6GroupOrdering left middle)
      (rule6GroupOrdering middle right) = some composed) :
    rule6GroupOrdering left right = composed := by
  cases leftMiddleEq : rule6GroupOrdering left middle <;>
    cases middleRightEq : rule6GroupOrdering middle right <;>
    simp [composeOrdering?, leftMiddleEq, middleRightEq] at composition
  all_goals subst composed
  all_goals simp_all
  all_goals omega

/-- The non-junior direction of group-index comparison is transitive. -/
theorem rule6GroupOrdering_senior_preorder {left middle right : Nat}
    (left_middle : rule6GroupOrdering left middle ≠ Ordering.lt)
    (middle_right : rule6GroupOrdering middle right ≠ Ordering.lt) :
    rule6GroupOrdering left right ≠ Ordering.lt := by
  intro leftRight
  have left_le_middle : left ≤ middle := by
    by_contra notLe
    have middle_lt_left : middle < left := by omega
    exact left_middle ((rule6GroupOrdering_lt_iff left middle).2 middle_lt_left)
  have middle_le_right : middle ≤ right := by
    by_contra notLe
    have right_lt_middle : right < middle := by omega
    exact middle_right ((rule6GroupOrdering_lt_iff middle right).2 right_lt_middle)
  have right_lt_left := (rule6GroupOrdering_lt_iff left right).1 leftRight
  omega

/-- Compare two sorted ranks through the actual initial occurrence comparator. -/
def compareRule6InitialRanks? (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (sorted : List Nat)
    (leftRank rightRank : Nat) : Option Ordering := do
  let leftPosition ← sorted[leftRank]?
  let rightPosition ← sorted[rightRank]?
  let decision ← compareRule6InitialPositions? (mol := mol) aux fuel roots
    leftPosition rightPosition
  some decision.ordering

/-- Executable fail-closed check of one directed pair in the sorted initial partition. -/
def checkRule6InitialDirectedPair? (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (sorted : List Nat)
    (adjacent : List (Option Ordering)) (leftRank rightRank : Nat) : Option Unit := do
  let ordering ← compareRule6InitialRanks? (mol := mol) aux fuel roots sorted leftRank rightRank
  if ordering == rule6ExpectedPartitionOrdering adjacent leftRank rightRank then some () else none

/-- Proof-relevant evidence for one directed pair used by the complete initial partition check. -/
structure Rule6InitialDirectedPairEvaluation (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (sorted : List Nat)
    (adjacent : List (Option Ordering)) (leftRank rightRank : Nat) where
  leftPosition : Nat
  rightPosition : Nat
  decision : OccurrenceComparison
  left_eq : sorted[leftRank]? = some leftPosition
  right_eq : sorted[rightRank]? = some rightPosition
  comparison : Rule6InitialPositionEvaluation (mol := mol) aux fuel roots
    leftPosition rightPosition decision
  expected_eq : decision.ordering =
    rule6ExpectedPartitionOrdering adjacent leftRank rightRank

theorem Rule6InitialDirectedPairEvaluation.comparison_eq
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor} {sorted : List Nat}
    {adjacent : List (Option Ordering)} {leftRank rightRank : Nat}
    (evaluation : Rule6InitialDirectedPairEvaluation (mol := mol) aux fuel roots sorted adjacent
      leftRank rightRank) :
    compareRule6InitialRanks? (mol := mol) aux fuel roots sorted leftRank rightRank =
      some (rule6ExpectedPartitionOrdering adjacent leftRank rightRank) := by
  simp [compareRule6InitialRanks?, evaluation.left_eq, evaluation.right_eq,
    evaluation.comparison.production_eq, evaluation.expected_eq]

theorem Rule6InitialDirectedPairEvaluation.production_eq
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor} {sorted : List Nat}
    {adjacent : List (Option Ordering)} {leftRank rightRank : Nat}
    (evaluation : Rule6InitialDirectedPairEvaluation (mol := mol) aux fuel roots sorted adjacent
      leftRank rightRank) :
    checkRule6InitialDirectedPair? (mol := mol) aux fuel roots sorted adjacent
      leftRank rightRank = some () := by
  simp [checkRule6InitialDirectedPair?, evaluation.comparison_eq]

def rule6InitialDirectedPairEvaluation_of_production
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (sorted : List Nat)
    (adjacent : List (Option Ordering)) (leftRank rightRank : Nat)
    (computed : checkRule6InitialDirectedPair? (mol := mol) aux fuel roots sorted adjacent
      leftRank rightRank = some ()) :
    Rule6InitialDirectedPairEvaluation (mol := mol) aux fuel roots sorted adjacent
      leftRank rightRank := by
  unfold checkRule6InitialDirectedPair? compareRule6InitialRanks? at computed
  cases leftEq : sorted[leftRank]? with
  | none => simp [leftEq] at computed
  | some leftPosition =>
      cases rightEq : sorted[rightRank]? with
      | none => simp [leftEq, rightEq] at computed
      | some rightPosition =>
          cases comparisonEq : compareRule6InitialPositions? (mol := mol) aux fuel roots
              leftPosition rightPosition with
          | none => simp [leftEq, rightEq, comparisonEq] at computed
          | some decision =>
              have expectedEq : decision.ordering =
                  rule6ExpectedPartitionOrdering adjacent leftRank rightRank := by
                simpa [leftEq, rightEq, comparisonEq] using computed
              exact
                { leftPosition := leftPosition
                  rightPosition := rightPosition
                  decision := decision
                  left_eq := leftEq
                  right_eq := rightEq
                  comparison := rule6InitialPositionEvaluation_of_production aux fuel roots
                    leftPosition rightPosition decision comparisonEq
                  expected_eq := expectedEq }

/-- All sixteen directed rank pairs of a four-ligand frame. -/
def rule6InitialDirectedRankPairs : List (Nat × Nat) :=
  (List.range 4).flatMap fun leftRank =>
    (List.range 4).map fun rightRank => (leftRank, rightRank)

/-- Fail-closed traversal of a caller-independent directed-pair family. -/
def checkRule6InitialDirectedPairs? (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (sorted : List Nat)
    (adjacent : List (Option Ordering)) : List (Nat × Nat) → Option Unit
  | [] => some ()
  | pair :: pairs => do
      let _ ← checkRule6InitialDirectedPair? (mol := mol) aux fuel roots sorted adjacent
        pair.1 pair.2
      checkRule6InitialDirectedPairs? aux fuel roots sorted adjacent pairs

/-- Proof-relevant traversal retaining a `Rule45Evaluation` for every checked directed pair. -/
inductive Rule6InitialDirectedPairsDerivation (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (sorted : List Nat)
    (adjacent : List (Option Ordering)) : List (Nat × Nat) → Prop
  | nil : Rule6InitialDirectedPairsDerivation aux fuel roots sorted adjacent []
  | cons (leftRank rightRank : Nat) (pairs : List (Nat × Nat))
      (evaluation : Rule6InitialDirectedPairEvaluation (mol := mol) aux fuel roots sorted adjacent
        leftRank rightRank)
      (tail : Rule6InitialDirectedPairsDerivation aux fuel roots sorted adjacent pairs) :
      Rule6InitialDirectedPairsDerivation aux fuel roots sorted adjacent
        ((leftRank, rightRank) :: pairs)

theorem Rule6InitialDirectedPairsDerivation.production_eq
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor} {sorted : List Nat}
    {adjacent : List (Option Ordering)} {pairs : List (Nat × Nat)}
    (derived : Rule6InitialDirectedPairsDerivation (mol := mol) aux fuel roots sorted adjacent
      pairs) :
    checkRule6InitialDirectedPairs? (mol := mol) aux fuel roots sorted adjacent pairs = some () := by
  induction derived with
  | nil => rfl
  | cons leftRank rightRank pairs evaluation tail inductionHypothesis =>
      simp [checkRule6InitialDirectedPairs?, evaluation.production_eq, inductionHypothesis]

def rule6InitialDirectedPairsDerivation_of_production
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (sorted : List Nat)
    (adjacent : List (Option Ordering)) (pairs : List (Nat × Nat))
    (computed : checkRule6InitialDirectedPairs? (mol := mol) aux fuel roots sorted adjacent pairs =
      some ()) :
    Rule6InitialDirectedPairsDerivation (mol := mol) aux fuel roots sorted adjacent pairs := by
  induction pairs with
  | nil => exact .nil
  | cons pair pairs inductionHypothesis =>
      rcases pair with ⟨leftRank, rightRank⟩
      simp only [checkRule6InitialDirectedPairs?] at computed
      cases pairEq : checkRule6InitialDirectedPair? (mol := mol) aux fuel roots sorted adjacent
          leftRank rightRank with
      | none => simp [pairEq] at computed
      | some gate =>
          cases gate
          have tailEq : checkRule6InitialDirectedPairs? (mol := mol) aux fuel roots sorted adjacent
              pairs = some () := by
            simpa [pairEq] using computed
          exact .cons leftRank rightRank pairs
            (rule6InitialDirectedPairEvaluation_of_production aux fuel roots sorted adjacent
              leftRank rightRank pairEq)
            (inductionHypothesis tailEq)

/-- Complete structural certificate for all sixteen directed pairs. -/
abbrev Rule6InitialCompletePartitionCertificate
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (sorted : List Nat)
    (adjacent : List (Option Ordering)) :=
  Rule6InitialDirectedPairsDerivation (mol := mol) aux fuel roots sorted adjacent
    rule6InitialDirectedRankPairs

theorem Rule6InitialDirectedPairsDerivation.evaluation_of_mem
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor} {sorted : List Nat}
    {adjacent : List (Option Ordering)} {pairs : List (Nat × Nat)}
    (derived : Rule6InitialDirectedPairsDerivation (mol := mol) aux fuel roots sorted adjacent
      pairs) {leftRank rightRank : Nat} (member : (leftRank, rightRank) ∈ pairs) :
    Nonempty (Rule6InitialDirectedPairEvaluation (mol := mol) aux fuel roots sorted adjacent
      leftRank rightRank) := by
  induction derived with
  | nil => simp at member
  | cons headLeft headRight pairs evaluation tail inductionHypothesis =>
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩ | member
      · exact ⟨evaluation⟩
      · exact inductionHypothesis member

theorem Rule6InitialCompletePartitionCertificate.comparison_eq_of_bounds
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor} {sorted : List Nat}
    {adjacent : List (Option Ordering)}
    (certificate : Rule6InitialCompletePartitionCertificate (mol := mol) aux fuel roots sorted
      adjacent) {leftRank rightRank : Nat} (left_bound : leftRank < 4)
    (right_bound : rightRank < 4) :
    compareRule6InitialRanks? (mol := mol) aux fuel roots sorted leftRank rightRank =
      some (rule6ExpectedPartitionOrdering adjacent leftRank rightRank) := by
  have member : (leftRank, rightRank) ∈ rule6InitialDirectedRankPairs := by
    simp [rule6InitialDirectedRankPairs, left_bound, right_bound]
  rcases certificate.evaluation_of_mem member with ⟨evaluation⟩
  exact evaluation.comparison_eq

/-- Among the exact four sorted ranks, the semantic admissible-reference class is the
Rules-1--5 group containing rank 1. -/
def Rule6RankOneAdmissibleReferencePosition (sorted : List Nat)
    (adjacent : List (Option Ordering)) (position : Nat) : Prop :=
  (position = sorted.getD 0 0 ∧
      rule6InitialGroupIndex adjacent 0 = rule6InitialGroupIndex adjacent 1) ∨
  position = sorted.getD 1 0 ∨
  (position = sorted.getD 2 0 ∧
      rule6InitialGroupIndex adjacent 2 = rule6InitialGroupIndex adjacent 1) ∨
  (position = sorted.getD 3 0 ∧
      rule6InitialGroupIndex adjacent 3 = rule6InitialGroupIndex adjacent 1)

/-- Rules-1--5 comparison used to form the complete four-position Rule-6 carrier. -/
def rule6CompareAt? (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (left right : Nat) : Option Ordering := do
  let leftRoot ← roots[left]?
  let rightRoot ← roots[right]?
  (compareOccurrenceBranches? mol aux fuel leftRoot rightRoot).map OccurrenceComparison.ordering

/-- Legacy Boolean Rules-1--5 order retained for comparison with the raw production path.
The occurrence-level Rule-6 result below uses `sortRule6InitialPositions?`, which fails rather
than interpreting an inconclusive comparison as a successful `before` decision. -/
def rule6SortedPositions (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) : List Nat :=
  sortDescBy
    (fun left right => rule6CompareAt? (mol := mol) aux fuel roots left right != some Ordering.lt)
    (List.range 4)

/-- All three adjacent Rules-1--5 outcomes of the promoted four-position frame. -/
def rule6AdjacentOutcomes (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (sorted : List Nat) : List (Option Ordering) :=
  (List.range 3).map fun index => do
    let left ← sorted[index]?
    let right ← sorted[index + 1]?
    rule6CompareAt? (mol := mol) aux fuel roots left right

/- rule6GroupCount is re-exported from Rule6PartitionGroupCount. -/

/-- For a complete two-group partition, production enumerates exactly the semantic group
containing sorted rank 1. The semantic side is defined by group indices, independently of the
shape-specific executable enumeration. -/
theorem mem_rule6EquivalentReferencePositions_iff_rankOneGroup
    (sorted : List Nat) (adjacent : List (Option Ordering))
    (adjacent_length : adjacent.length = 3)
    (adjacent_complete : ∀ entry ∈ adjacent,
      entry = some Ordering.eq ∨ entry = some Ordering.gt)
    (group_two : rule6GroupCount adjacent = 2) (position : Nat) :
    position ∈ rule6EquivalentReferencePositions sorted adjacent ↔
      Rule6RankOneAdmissibleReferencePosition sorted adjacent position := by
  rcases List.length_eq_three.mp adjacent_length with ⟨first, second, third, rfl⟩
  have firstComplete := adjacent_complete first (by simp)
  have secondComplete := adjacent_complete second (by simp)
  have thirdComplete := adjacent_complete third (by simp)
  rcases firstComplete with rfl | rfl <;>
    rcases secondComplete with rfl | rfl <;>
    rcases thirdComplete with rfl | rfl <;>
    simp [rule6GroupCount, rule6EquivalentReferencePositions,
      Rule6RankOneAdmissibleReferencePosition, rule6InitialGroupIndex] at group_two ⊢ <;>
    aesop

/-- Full four-ligand Rule-6 calculation.  It is reached only when ordinary Rules 4b/5 did not
produce a strict label. -/
def rule6Result? (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (roots : List CanonicalRerootCursor) :
    Option OccurrenceRule6Result := do
  let spec ← mol.atomAt? node.atom
  let parity ← spec.tetrahedral?
  let ligands := mol.ligandsWithLonePair node.atom
  if ligands.length != 4 || roots.length != 4 then none else
  let sorted ← sortRule6InitialPositions? (mol := mol) aux fuel roots (List.range 4)
  let adjacent ← compareRule6InitialAdjacent? (mol := mol) aux fuel roots sorted
  if adjacent.contains (some Ordering.lt) then none else
  let _ ← checkRule6InitialDirectedPairs? (mol := mol) aux fuel roots sorted adjacent
    rule6InitialDirectedRankPairs
  let groupCount := rule6GroupCount adjacent
  let oddTopology? := hasOddConstitutionAutomorphismAtCenter mol node.atom ligands fun left right =>
    rule6CompareAt? (mol := mol) aux fuel roots left right == some Ordering.eq
  if oddTopology? != some false then none else
  if groupCount == 1 then
    let agreement ← rankOccurrenceFourWayReferences? (mol := mol) aux fuel roots parity ligands sorted
    some
      { fact :=
          { key := canonicalOccurrenceKey node
            atom := node.atom
            descriptor := agreement.descriptor
            uppercase := agreement.secondRanking.pseudoComparisons != 1
            priorityPositions := agreement.secondRanking.positions }
        parity := parity
        ligands := ligands
        roots := roots
        sorted := sorted
        adjacent := adjacent
        groupCount := groupCount
        oddTopology? := oddTopology?
        carrier := .fourWay agreement }
  else if groupCount == 2 then
    let references := rule6EquivalentReferencePositions sorted adjacent
    let ranking ← rankOccurrenceEquivalentReferences? (mol := mol) aux fuel roots parity ligands
      sorted references
    if !ranking.unique then none else
    some
      { fact :=
          { key := canonicalOccurrenceKey node
            atom := node.atom
            descriptor := RawMolecule.descriptorOfParity parity
              (RawMolecule.permutationIsEven ranking.positions)
            uppercase := ranking.pseudoComparisons != 1
            priorityPositions := ranking.positions }
        parity := parity
        ligands := ligands
        roots := roots
        sorted := sorted
        adjacent := adjacent
        groupCount := groupCount
        oddTopology? := oddTopology?
        carrier := .twoGroup references ranking }
  else if groupCount == 3 then
    let reference := sorted[1]?.getD 0
    let referenceRoot ← roots[reference]?
    if adjacent[1]?.getD none != some Ordering.eq ||
        !occurrenceBranchHasLocalReference (mol := mol) aux fuel [referenceRoot] then none else
    let ranking ← rankOccurrenceEquivalentReferences? (mol := mol) aux fuel roots parity ligands
      sorted [reference]
    if !ranking.unique then none else
    some
      { fact :=
          { key := canonicalOccurrenceKey node
            atom := node.atom
            descriptor := RS.swap (RawMolecule.descriptorOfParity parity
              (RawMolecule.permutationIsEven ranking.positions))
            uppercase := true
            priorityPositions := ranking.positions }
        parity := parity
        ligands := ligands
        roots := roots
        sorted := sorted
        adjacent := adjacent
        groupCount := groupCount
        oddTopology? := oddTopology?
        carrier := .threeGroup reference ranking }
  else none

/-! ### Independent descriptor-level Rule-6 derivation -/

/-- Primitive equations shared by all three admitted Rule-6 carrier shapes. -/
structure Rule6FrameCertificate (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (roots : List CanonicalRerootCursor) where
  spec : AtomSpec
  parity : TetrahedralInputParity
  ligands : List Nat
  sorted : List Nat
  adjacent : List (Option Ordering)
  groupCount : Nat
  atom_spec : mol.atomAt? node.atom = some spec
  tetrahedral : spec.tetrahedral? = some parity
  ligands_eq : ligands = mol.ligandsWithLonePair node.atom
  ligands_length : ligands.length = 4
  roots_length : roots.length = 4
  ranking : SortRule6InitialDerivation (mol := mol) aux fuel roots (List.range 4) sorted
  comparisons : Rule6InitialAdjacentDerivation (mol := mol) aux fuel roots sorted adjacent
  adjacent_not_lt : some Ordering.lt ∉ adjacent
  partition : Rule6InitialCompletePartitionCertificate (mol := mol) aux fuel roots sorted adjacent
  groupCount_eq : groupCount = rule6GroupCount adjacent
  odd_false : hasOddConstitutionAutomorphismAtCenter mol node.atom ligands
      (fun left right =>
        rule6CompareAt? (mol := mol) aux fuel roots left right == some Ordering.eq) = some false

/-! ### A chemically structural completeness class -/

/-- A tetrahedral production frame whose four ligand digraphs terminate at their root atoms.

Unlike `CIPAdmissibleFrame` below, this structure contains no successful comparator calls.  Its
hypotheses are chemical/frame facts and unary facts about each generated ligand occurrence:

* the raw molecule satisfies the parser admission and valence contracts;
* `node` is a tetrahedrally annotated atom and `roots` is its exact four-ligand production frame;
* each root is terminal and acyclic at the selected production fuel;
* each root has an exact Rule-1a label supported by the current labeler; and
* no root itself carries an auxiliary Rule-4/5 descriptor fact.

This includes ordinary tetrahedral centers directly bonded to four terminal substituent atoms
(and the analogous three-coordinate N/P/S frames with a canonical lone-pair phantom). -/
structure TerminalAcyclicCIPFrame (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (roots : List CanonicalRerootCursor) where
  spec : AtomSpec
  parity : TetrahedralInputParity
  admissible : mol.Admissible
  valence_ok : mol.ValenceOK
  atom_spec : mol.atomAt? node.atom = some spec
  tetrahedral : spec.tetrahedral? = some parity
  ligand_frame : occurrenceLigandFrame? mol node = some roots
  roots_length : roots.length = 4
  terminal : ∀ root, root ∈ roots → cursorTerminal mol root = true
  acyclic : ∀ root, root ∈ roots → mol.atomLiesInCycle fuel root.node.atom = false
  rule1a_supported : ∀ root, root ∈ roots →
    ∃ label, mol.canonicalRule1aLabel? root.node = some label
  descriptor_silent : ∀ root, root ∈ roots → aux.factAt? root.node = none

/-- Every directed pair in a `TerminalAcyclicCIPFrame` succeeds in the actual production
Rules-1--5 comparator.  The successful result is additionally identified with the raw
constitutional ordering, so the theorem establishes both totality and absence of a spurious
descriptor/pseudoasymmetric decision on this structural class. -/
theorem TerminalAcyclicCIPFrame.comparison_eq_raw_of_mem
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : TerminalAcyclicCIPFrame (mol := mol) aux fuel node roots)
    {left right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (right_mem : right ∈ roots) :
    ∃ ordering,
      compareCursorBranchAt mol fuel .rule2 left right = some ordering ∧
      compareOccurrenceBranches? mol aux fuel left right =
        some { ordering := ordering } := by
  exact
    compareOccurrenceBranches?_terminal_supported_silent_of_left_acyclic
      mol aux fuel left right
        (frame.terminal left left_mem) (frame.terminal right right_mem)
        (frame.acyclic left left_mem)
        (frame.rule1a_supported left left_mem)
        (frame.rule1a_supported right right_mem)
        (frame.descriptor_silent left left_mem)
        (frame.descriptor_silent right right_mem)

/-- Pairwise production completeness extracted from chemical/frame support rather than from an
all-pairs executable comparison certificate. -/
theorem TerminalAcyclicCIPFrame.comparison_exists
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : TerminalAcyclicCIPFrame (mol := mol) aux fuel node roots)
    {left right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (right_mem : right ∈ roots) :
    ∃ decision, compareOccurrenceBranches? mol aux fuel left right = some decision := by
  rcases frame.comparison_eq_raw_of_mem left_mem right_mem with ⟨ordering, _, comparison⟩
  exact ⟨{ ordering := ordering }, comparison⟩

/-- The requested two-success endpoint theorem on a non-circular chemically structural class.

The two premise calls and their defined composition determine the endpoint value.  Endpoint
*existence* is supplied independently by terminal/acyclic/label/descriptor support, not by an
all-pairs list of successful calls. -/
theorem TerminalAcyclicCIPFrame.endpoint_of_two_success
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : TerminalAcyclicCIPFrame (mol := mol) aux fuel node roots)
    {left middle right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (_middle_mem : middle ∈ roots) (right_mem : right ∈ roots)
    {leftMiddle middleRight : OccurrenceComparison} {composed : Ordering}
    (left_middle : compareOccurrenceBranches? mol aux fuel left middle = some leftMiddle)
    (middle_right : compareOccurrenceBranches? mol aux fuel middle right = some middleRight)
    (composition :
      composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering = some composed) :
    ∃ leftRight,
      compareOccurrenceBranches? mol aux fuel left right = some leftRight ∧
        leftRight.ordering = composed := by
  rcases frame.comparison_exists left_mem right_mem with ⟨leftRight, left_right⟩
  refine ⟨leftRight, left_right, ?_⟩
  exact compareOccurrenceBranches_ordering_compose_failClosed_of_three_success
    mol aux fuel left_middle middle_right left_right composition

/-! ### Bounded acyclic linear ligand digraphs -/

/-- A strictly broader structural completeness class allowing nonterminal ligand chains.

Each exact generated root carries a recursive `AcyclicLinearCursorSupport`: every visited cursor
has an exact Rule-1a label, is acyclic at the selected production fuel, and is either terminal or
has exactly one recursively supported forward child.  Consequently no sibling comparison is ever
needed, every active sphere contains at most one nonterminal pair plus two phantom-padding pairs,
and the production frontier width is at most three.  The empty auxiliary state records that this
class is constitution-only; Rules 4a--5 must traverse successfully but cannot decide priority. -/
structure LinearAcyclicCIPFrame (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (roots : List CanonicalRerootCursor) where
  spec : AtomSpec
  parity : TetrahedralInputParity
  admissible : mol.Admissible
  valence_ok : mol.ValenceOK
  atom_spec : mol.atomAt? node.atom = some spec
  tetrahedral : spec.tetrahedral? = some parity
  ligand_frame : occurrenceLigandFrame? mol node = some roots
  roots_length : roots.length = 4
  support : ∀ root, root ∈ roots → AcyclicLinearCursorSupport mol fuel root

/-- The earlier terminal theorem embeds into the linear theorem when the auxiliary state is empty.
This makes `LinearAcyclicCIPFrame` an actual extension rather than an unrelated special case. -/
def TerminalAcyclicCIPFrame.toLinearAcyclic
    {fuel : Nat} {node : RawMolecule.CanonicalBranchNode}
    {roots : List CanonicalRerootCursor}
    (frame : TerminalAcyclicCIPFrame (mol := mol) [] fuel node roots) :
    LinearAcyclicCIPFrame (mol := mol) fuel node roots where
  spec := frame.spec
  parity := frame.parity
  admissible := frame.admissible
  valence_ok := frame.valence_ok
  atom_spec := frame.atom_spec
  tetrahedral := frame.tetrahedral
  ligand_frame := frame.ligand_frame
  roots_length := frame.roots_length
  support := by
    intro root member
    exact
      { linear := .terminal fuel root (frame.rule1a_supported root member)
          (frame.terminal root member)
        acyclic := .terminal root (frame.acyclic root member) (frame.terminal root member) }

/-- Every directed Rules-1--5 comparison in a bounded acyclic linear frame succeeds and is exactly
its raw constitutional ordering.  No pairwise success or capacity certificate is assumed. -/
theorem LinearAcyclicCIPFrame.comparison_eq_raw_of_mem
    {fuel : Nat} {node : RawMolecule.CanonicalBranchNode}
    {roots : List CanonicalRerootCursor}
    (frame : LinearAcyclicCIPFrame (mol := mol) fuel node roots)
    {left right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (right_mem : right ∈ roots) :
    ∃ ordering,
      compareCursorBranchAt mol fuel .rule2 left right = some ordering ∧
      compareOccurrenceBranches? mol [] fuel left right = some { ordering := ordering } := by
  exact compareOccurrenceBranches?_acyclic_linear_empty_eq_raw
    mol fuel left right (frame.support left left_mem) (frame.support right right_mem)

theorem LinearAcyclicCIPFrame.comparison_exists
    {fuel : Nat} {node : RawMolecule.CanonicalBranchNode}
    {roots : List CanonicalRerootCursor}
    (frame : LinearAcyclicCIPFrame (mol := mol) fuel node roots)
    {left right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (right_mem : right ∈ roots) :
    ∃ decision, compareOccurrenceBranches? mol [] fuel left right = some decision := by
  rcases frame.comparison_eq_raw_of_mem left_mem right_mem with ⟨ordering, _, comparison⟩
  exact ⟨{ ordering := ordering }, comparison⟩

/-- Two-success endpoint closure on bounded acyclic linear CIP ligand digraphs.  Endpoint success
is derived from recursive unary molecular support, not checked all-pairs evidence. -/
theorem LinearAcyclicCIPFrame.endpoint_of_two_success
    {fuel : Nat} {node : RawMolecule.CanonicalBranchNode}
    {roots : List CanonicalRerootCursor}
    (frame : LinearAcyclicCIPFrame (mol := mol) fuel node roots)
    {left middle right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (_middle_mem : middle ∈ roots) (right_mem : right ∈ roots)
    {leftMiddle middleRight : OccurrenceComparison} {composed : Ordering}
    (left_middle : compareOccurrenceBranches? mol [] fuel left middle = some leftMiddle)
    (middle_right : compareOccurrenceBranches? mol [] fuel middle right = some middleRight)
    (composition :
      composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering = some composed) :
    ∃ leftRight,
      compareOccurrenceBranches? mol [] fuel left right = some leftRight ∧
        leftRight.ordering = composed := by
  rcases frame.comparison_exists left_mem right_mem with ⟨leftRight, left_right⟩
  refine ⟨leftRight, left_right, ?_⟩
  exact compareOccurrenceBranches_ordering_compose_failClosed_of_three_success
    mol [] fuel left_middle middle_right left_right composition

/-! ### Bounded acyclic branching ligand trees -/

/-- Structural completeness frame for genuine branching CIP ligand trees.

Every exact generated ligand root carries recursive branching support: at each visited cursor the
Rule-1a label exists, there are at most three forward children, and every child is supported at the
next smaller depth.  Recursive acyclicity disables the constitutional conflict gate.  The global
ternary envelope proves that every possible paired frontier fits below the production width cap.
No successful root-pair comparison is stored in this structure. -/
structure BranchingAcyclicCIPFrame (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (roots : List CanonicalRerootCursor) where
  spec : AtomSpec
  parity : TetrahedralInputParity
  admissible : mol.Admissible
  valence_ok : mol.ValenceOK
  atom_spec : mol.atomAt? node.atom = some spec
  tetrahedral : spec.tetrahedral? = some parity
  ligand_frame : occurrenceLigandFrame? mol node = some roots
  roots_length : roots.length = 4
  frontier_envelope : 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap
  support : ∀ root, root ∈ roots → AcyclicBranchingCursorSupport mol fuel root

/-- The linear theorem embeds into the branching theorem whenever its ternary fuel envelope fits
the production cap. -/
def LinearAcyclicCIPFrame.toBranchingAcyclic
    {fuel : Nat} {node : RawMolecule.CanonicalBranchNode}
    {roots : List CanonicalRerootCursor}
    (frame : LinearAcyclicCIPFrame (mol := mol) fuel node roots)
    (frontier_envelope : 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap) :
    BranchingAcyclicCIPFrame (mol := mol) fuel node roots where
  spec := frame.spec
  parity := frame.parity
  admissible := frame.admissible
  valence_ok := frame.valence_ok
  atom_spec := frame.atom_spec
  tetrahedral := frame.tetrahedral
  ligand_frame := frame.ligand_frame
  roots_length := frame.roots_length
  frontier_envelope := frontier_envelope
  support := by
    intro root member
    have supported := frame.support root member
    exact
      { branching := supported.linear.toBranching
        acyclic :=
          ProductionCIPBranchingOccurrenceComparatorCompleteness.LinearCursorAcyclic.toBranching
            supported.acyclic }

/-- Every directed Rules-1--5 comparison in an acyclic branching frame succeeds and equals its
raw constitutional ordering.  Sibling-ranking calls and width safety are proved structurally. -/
theorem BranchingAcyclicCIPFrame.comparison_eq_raw_of_mem
    {fuel : Nat} {node : RawMolecule.CanonicalBranchNode}
    {roots : List CanonicalRerootCursor}
    (frame : BranchingAcyclicCIPFrame (mol := mol) fuel node roots)
    {left right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (right_mem : right ∈ roots) :
    ∃ ordering,
      compareCursorBranchAt mol fuel .rule2 left right = some ordering ∧
      compareOccurrenceBranches? mol [] fuel left right = some { ordering := ordering } := by
  exact compareOccurrenceBranches?_acyclic_branching_empty_eq_raw mol fuel left right
    frame.frontier_envelope (frame.support left left_mem) (frame.support right right_mem)

theorem BranchingAcyclicCIPFrame.comparison_exists
    {fuel : Nat} {node : RawMolecule.CanonicalBranchNode}
    {roots : List CanonicalRerootCursor}
    (frame : BranchingAcyclicCIPFrame (mol := mol) fuel node roots)
    {left right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (right_mem : right ∈ roots) :
    ∃ decision, compareOccurrenceBranches? mol [] fuel left right = some decision := by
  rcases frame.comparison_eq_raw_of_mem left_mem right_mem with ⟨ordering, _, comparison⟩
  exact ⟨{ ordering := ordering }, comparison⟩

/-- Two-success endpoint closure on bounded acyclic branching CIP ligand trees.  Endpoint success
comes from recursive subtree support and the ternary frontier envelope, not an all-pairs table. -/
theorem BranchingAcyclicCIPFrame.endpoint_of_two_success
    {fuel : Nat} {node : RawMolecule.CanonicalBranchNode}
    {roots : List CanonicalRerootCursor}
    (frame : BranchingAcyclicCIPFrame (mol := mol) fuel node roots)
    {left middle right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (_middle_mem : middle ∈ roots) (right_mem : right ∈ roots)
    {leftMiddle middleRight : OccurrenceComparison} {composed : Ordering}
    (left_middle : compareOccurrenceBranches? mol [] fuel left middle = some leftMiddle)
    (middle_right : compareOccurrenceBranches? mol [] fuel middle right = some middleRight)
    (composition :
      composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering = some composed) :
    ∃ leftRight,
      compareOccurrenceBranches? mol [] fuel left right = some leftRight ∧
        leftRight.ordering = composed := by
  rcases frame.comparison_exists left_mem right_mem with ⟨leftRight, left_right⟩
  refine ⟨leftRight, left_right, ?_⟩
  exact compareOccurrenceBranches_ordering_compose_failClosed_of_three_success
    mol [] fuel left_middle middle_right left_right composition

/-! ### Descriptor-bearing and cyclic branching frames -/

/-- Exact production frame for bounded descriptor-bearing branching trees.

The unary `gate_neutral` field records a root-relative reason why the legacy cyclic-automorphism
conflict cannot fire.  Rule 4b's executable domain is represented by one common reference arity
for all four roots; unlike an all-pairs comparison table, this is a unary descriptor signature. -/
structure DescriptorBranchingCIPFrame (state : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (roots : List CanonicalRerootCursor) where
  spec : AtomSpec
  parity : TetrahedralInputParity
  admissible : mol.Admissible
  valence_ok : mol.ValenceOK
  atom_spec : mol.atomAt? node.atom = some spec
  tetrahedral : spec.tetrahedral? = some parity
  ligand_frame : occurrenceLigandFrame? mol node = some roots
  roots_length : roots.length = 4
  frontier_envelope : 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap
  support : ∀ root, root ∈ roots → BranchingCursorSupport mol fuel root
  gate_neutral : ∀ root, root ∈ roots → RootRelativeGateNeutral mol fuel root
  rule4b_arity : Nat
  rule4b_arity_le : rule4b_arity ≤ 2
  rule4b_uniform : ∀ root, root ∈ roots →
    (occurrenceRule4bReferences mol state fuel [root]).length = rule4b_arity

/-- Pairwise production completeness from recursive descriptor/tree support.  The returned result
may be descriptor-decided, pseudoasymmetric, and carry a Rule-4c witness. -/
theorem DescriptorBranchingCIPFrame.comparison_exists
    {state : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingCIPFrame (mol := mol) state fuel node roots)
    {left right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (right_mem : right ∈ roots) :
    ∃ comparison, compareOccurrenceBranches? mol state fuel left right = some comparison := by
  exact compareOccurrenceBranches?_descriptor_branching_exists mol state fuel frame.rule4b_arity
    left right frame.frontier_envelope (frame.support left left_mem)
      (frame.support right right_mem) (frame.gate_neutral left left_mem)
      frame.rule4b_arity_le (frame.rule4b_uniform left left_mem)
      (frame.rule4b_uniform right right_mem)

/-- Two-success endpoint closure for descriptor-bearing branching trees. -/
theorem DescriptorBranchingCIPFrame.endpoint_of_two_success
    {state : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingCIPFrame (mol := mol) state fuel node roots)
    {left middle right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (_middle_mem : middle ∈ roots) (right_mem : right ∈ roots)
    {leftMiddle middleRight : OccurrenceComparison} {composed : Ordering}
    (left_middle : compareOccurrenceBranches? mol state fuel left middle = some leftMiddle)
    (middle_right : compareOccurrenceBranches? mol state fuel middle right = some middleRight)
    (composition :
      composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering = some composed) :
    ∃ leftRight,
      compareOccurrenceBranches? mol state fuel left right = some leftRight ∧
        leftRight.ordering = composed := by
  rcases frame.comparison_exists left_mem right_mem with ⟨leftRight, left_right⟩
  refine ⟨leftRight, left_right, ?_⟩
  exact compareOccurrenceBranches_ordering_compose_failClosed_of_three_success
    mol state fuel left_middle middle_right left_right composition

/-- A cyclic incoming occurrence frame.  Every generated ligand root has the same cyclic incoming
center, which definitionally disables the legacy gate's required `incoming root is acyclic`
condition even when the ligand roots themselves lie in rings. -/
structure CyclicIncomingDescriptorBranchingCIPFrame
    (state : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (roots : List CanonicalRerootCursor) where
  spec : AtomSpec
  parity : TetrahedralInputParity
  admissible : mol.Admissible
  valence_ok : mol.ValenceOK
  atom_spec : mol.atomAt? node.atom = some spec
  tetrahedral : spec.tetrahedral? = some parity
  ligand_frame : occurrenceLigandFrame? mol node = some roots
  roots_length : roots.length = 4
  frontier_envelope : 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap
  support : ∀ root, root ∈ roots → BranchingCursorSupport mol fuel root
  center_cyclic : mol.atomLiesInCycle fuel node.atom = true
  incoming_frame : ∀ root, root ∈ roots → root.previous? = some node
  rule4b_arity : Nat
  rule4b_arity_le : rule4b_arity ≤ 2
  rule4b_uniform : ∀ root, root ∈ roots →
    (occurrenceRule4bReferences mol state fuel [root]).length = rule4b_arity

def CyclicIncomingDescriptorBranchingCIPFrame.toDescriptorBranching
    {state : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : CyclicIncomingDescriptorBranchingCIPFrame
      (mol := mol) state fuel node roots) :
    DescriptorBranchingCIPFrame (mol := mol) state fuel node roots where
  spec := frame.spec
  parity := frame.parity
  admissible := frame.admissible
  valence_ok := frame.valence_ok
  atom_spec := frame.atom_spec
  tetrahedral := frame.tetrahedral
  ligand_frame := frame.ligand_frame
  roots_length := frame.roots_length
  frontier_envelope := frame.frontier_envelope
  support := frame.support
  gate_neutral := by
    intro root member
    exact .incomingCyclic root node (frame.incoming_frame root member) frame.center_cyclic
  rule4b_arity := frame.rule4b_arity
  rule4b_arity_le := frame.rule4b_arity_le
  rule4b_uniform := frame.rule4b_uniform

theorem CyclicIncomingDescriptorBranchingCIPFrame.comparison_exists
    {state : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : CyclicIncomingDescriptorBranchingCIPFrame
      (mol := mol) state fuel node roots)
    {left right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (right_mem : right ∈ roots) :
    ∃ comparison, compareOccurrenceBranches? mol state fuel left right = some comparison :=
  frame.toDescriptorBranching.comparison_exists left_mem right_mem

theorem CyclicIncomingDescriptorBranchingCIPFrame.endpoint_of_two_success
    {state : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : CyclicIncomingDescriptorBranchingCIPFrame
      (mol := mol) state fuel node roots)
    {left middle right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (middle_mem : middle ∈ roots) (right_mem : right ∈ roots)
    {leftMiddle middleRight : OccurrenceComparison} {composed : Ordering}
    (left_middle : compareOccurrenceBranches? mol state fuel left middle = some leftMiddle)
    (middle_right : compareOccurrenceBranches? mol state fuel middle right = some middleRight)
    (composition :
      composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering = some composed) :
    ∃ leftRight,
      compareOccurrenceBranches? mol state fuel left right = some leftRight ∧
        leftRight.ordering = composed :=
  frame.toDescriptorBranching.endpoint_of_two_success left_mem middle_mem right_mem
    left_middle middle_right composition

/-- Chemically and operationally admissible occurrence frame for the two-success endpoint law.

The inherited certificate supplies a tetrahedrally annotated center, four molecular ligands,
four executable roots, and successful checked comparisons for all sixteen directed pairs.  The
additional equation prevents callers from supplying an unrelated four-element cursor list: the
roots must be the exact production frame generated at this occurrence (including the canonical
lone-pair phantom when applicable).

This is deliberately proof-relevant support.  Chemical frame validity alone cannot imply that the
bounded optional comparator has enough label, traversal, fuel, and frontier capacity. -/
structure CIPAdmissibleFrame (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    extends Rule6FrameCertificate (mol := mol) aux fuel node roots where
  ligand_frame : occurrenceLigandFrame? mol node = some roots

def CIPAdmissibleFrame.ofRule6FrameCertificate
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : Rule6FrameCertificate (mol := mol) aux fuel node roots)
    (ligand_frame : occurrenceLigandFrame? mol node = some roots) :
    CIPAdmissibleFrame (mol := mol) aux fuel node roots :=
  { frame with ligand_frame := ligand_frame }

theorem Rule6FrameCertificate.sorted_perm
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : Rule6FrameCertificate (mol := mol) aux fuel node roots) :
    frame.sorted.Perm (List.range 4) :=
  frame.ranking.perm

theorem Rule6FrameCertificate.sorted_length
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : Rule6FrameCertificate (mol := mol) aux fuel node roots) :
    frame.sorted.length = 4 := by
  have lengths := frame.sorted_perm.length_eq
  simpa using lengths

/-- Complete partition evidence supplies an actual successful production comparison for any two
cursor values belonging to the certified four-root list, independently of their sorted ranks. -/
theorem Rule6FrameCertificate.comparison_exists_of_mem
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : Rule6FrameCertificate (mol := mol) aux fuel node roots)
    {left right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (right_mem : right ∈ roots) :
    ∃ decision,
      compareOccurrenceBranches? mol aux fuel left right = some decision := by
  rcases List.mem_iff_getElem?.mp left_mem with ⟨leftPosition, leftPositionEq⟩
  rcases List.mem_iff_getElem?.mp right_mem with ⟨rightPosition, rightPositionEq⟩
  have leftPositionBound : leftPosition < 4 := by
    have bound := (List.getElem?_eq_some_iff.mp leftPositionEq).1
    simpa [frame.roots_length] using bound
  have rightPositionBound : rightPosition < 4 := by
    have bound := (List.getElem?_eq_some_iff.mp rightPositionEq).1
    simpa [frame.roots_length] using bound
  have leftPositionSorted : leftPosition ∈ frame.sorted :=
    frame.sorted_perm.mem_iff.mpr (by simp [leftPositionBound])
  have rightPositionSorted : rightPosition ∈ frame.sorted :=
    frame.sorted_perm.mem_iff.mpr (by simp [rightPositionBound])
  rcases List.mem_iff_getElem?.mp leftPositionSorted with ⟨leftRank, leftRankEq⟩
  rcases List.mem_iff_getElem?.mp rightPositionSorted with ⟨rightRank, rightRankEq⟩
  have leftRankBound : leftRank < 4 := by
    have bound := (List.getElem?_eq_some_iff.mp leftRankEq).1
    simpa [frame.sorted_length] using bound
  have rightRankBound : rightRank < 4 := by
    have bound := (List.getElem?_eq_some_iff.mp rightRankEq).1
    simpa [frame.sorted_length] using bound
  have certified :=
    frame.partition.comparison_eq_of_bounds leftRankBound rightRankBound
  cases comparisonEq : compareOccurrenceBranches? mol aux fuel left right with
  | none =>
      simp [compareRule6InitialRanks?, compareRule6InitialPositions?, leftRankEq,
        rightRankEq, leftPositionEq, rightPositionEq, comparisonEq] at certified
  | some decision => exact ⟨decision, rfl⟩

theorem Rule6FrameCertificate.adjacent_length
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : Rule6FrameCertificate (mol := mol) aux fuel node roots) :
    frame.adjacent.length = 3 := by
  rw [frame.comparisons.length_eq_pred, frame.sorted_length]

theorem Rule6FrameCertificate.adjacent_eq_or_gt
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : Rule6FrameCertificate (mol := mol) aux fuel node roots)
    (entry : Option Ordering) (member : entry ∈ frame.adjacent) :
    entry = some Ordering.eq ∨ entry = some Ordering.gt := by
  rcases frame.comparisons.mem_some member with ⟨ordering, rfl⟩
  cases ordering with
  | lt => exact (frame.adjacent_not_lt member).elim
  | eq => exact Or.inl rfl
  | gt => exact Or.inr rfl

/-- On a certified two-group frame, the executable reference list is exactly the semantic
Rules-1--5 group containing rank 1. -/
theorem Rule6FrameCertificate.twoGroup_references_iff_rankOneGroup
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : Rule6FrameCertificate (mol := mol) aux fuel node roots)
    (group_two : frame.groupCount = 2) (position : Nat) :
    position ∈ rule6EquivalentReferencePositions frame.sorted frame.adjacent ↔
      Rule6RankOneAdmissibleReferencePosition frame.sorted frame.adjacent position := by
  apply mem_rule6EquivalentReferencePositions_iff_rankOneGroup frame.sorted frame.adjacent
    frame.adjacent_length frame.adjacent_eq_or_gt
  exact frame.groupCount_eq.symm.trans group_two

/-- Actual production Rule-6 initial-comparator transitivity on the certified four-ligand frame.
For every three bounded ranks, both premise comparisons are actual checked Rules-4b/5 calls. If
their partial ordering composition is defined, the checked endpoint comparison is exactly that
composition. This theorem deliberately does not claim arbitrary-cursor transitivity. -/
theorem productionRule6InitialComparator_transitive_on_certified_frame
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : Rule6FrameCertificate (mol := mol) aux fuel node roots)
    (left middle right : Nat) (left_bound : left < 4) (middle_bound : middle < 4)
    (right_bound : right < 4) :
    frame.sorted.Perm (List.range 4) ∧
    compareRule6InitialRanks? (mol := mol) aux fuel roots frame.sorted left middle =
      some (rule6ExpectedPartitionOrdering frame.adjacent left middle) ∧
    compareRule6InitialRanks? (mol := mol) aux fuel roots frame.sorted middle right =
      some (rule6ExpectedPartitionOrdering frame.adjacent middle right) ∧
    ∀ composed,
      composeOrdering? (rule6ExpectedPartitionOrdering frame.adjacent left middle)
          (rule6ExpectedPartitionOrdering frame.adjacent middle right) = some composed →
        compareRule6InitialRanks? (mol := mol) aux fuel roots frame.sorted left right =
          some composed := by
  refine ⟨frame.sorted_perm,
    frame.partition.comparison_eq_of_bounds left_bound middle_bound,
    frame.partition.comparison_eq_of_bounds middle_bound right_bound, ?_⟩
  intro composed composition
  have endpoint := frame.partition.comparison_eq_of_bounds left_bound right_bound
  have expected : rule6ExpectedPartitionOrdering frame.adjacent left right = composed := by
    apply rule6GroupOrdering_compose
    exact composition
  simpa [expected] using endpoint

/-- Endpoint-success form of certified-frame transitivity.  Unlike the arbitrary-cursor
comparator, a `Rule6FrameCertificate` contains checked results for all sixteen directed pairs.
Consequently two successful composable observations inside the frame determine an actually
successful endpoint call; no third-success premise is required. -/
theorem productionRule6InitialComparator_endpoint_of_two_success_on_certified_frame
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : Rule6FrameCertificate (mol := mol) aux fuel node roots)
    {left middle right : Nat} (left_bound : left < 4) (middle_bound : middle < 4)
    (right_bound : right < 4) {leftMiddle middleRight composed : Ordering}
    (left_middle : compareRule6InitialRanks? (mol := mol) aux fuel roots frame.sorted
      left middle = some leftMiddle)
    (middle_right : compareRule6InitialRanks? (mol := mol) aux fuel roots frame.sorted
      middle right = some middleRight)
    (composition : composeOrdering? leftMiddle middleRight = some composed) :
    compareRule6InitialRanks? (mol := mol) aux fuel roots frame.sorted left right =
      some composed := by
  have leftMiddleCertified :=
    frame.partition.comparison_eq_of_bounds left_bound middle_bound
  have middleRightCertified :=
    frame.partition.comparison_eq_of_bounds middle_bound right_bound
  have leftMiddleExpected :
      leftMiddle = rule6ExpectedPartitionOrdering frame.adjacent left middle :=
    Option.some.inj (left_middle.symm.trans leftMiddleCertified)
  have middleRightExpected :
      middleRight = rule6ExpectedPartitionOrdering frame.adjacent middle right :=
    Option.some.inj (middle_right.symm.trans middleRightCertified)
  have expectedComposition :
      composeOrdering? (rule6ExpectedPartitionOrdering frame.adjacent left middle)
          (rule6ExpectedPartitionOrdering frame.adjacent middle right) = some composed := by
    simpa [leftMiddleExpected, middleRightExpected] using composition
  exact
    (productionRule6InitialComparator_transitive_on_certified_frame frame
      left middle right left_bound middle_bound right_bound).2.2.2 composed expectedComposition

/-- Every pair of exact generated ligand roots in an admissible CIP frame is executable.  This is
the explicit completeness premise missing from the false arbitrary-cursor two-success law. -/
theorem CIPAdmissibleFrame.comparison_exists
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : CIPAdmissibleFrame (mol := mol) aux fuel node roots)
    {left right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (right_mem : right ∈ roots) :
    ∃ decision,
      compareOccurrenceBranches? mol aux fuel left right = some decision :=
  frame.toRule6FrameCertificate.comparison_exists_of_mem left_mem right_mem

/-- Chemically scoped two-success endpoint theorem.

The three cursors are literal members of one tetrahedral four-ligand production frame.  Executable
endpoint success comes from the admissibility certificate; the endpoint value then follows from
the intrinsic successful-result CIP ordering theorem. -/
theorem CIPAdmissibleFrame.endpoint_of_two_success
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : CIPAdmissibleFrame (mol := mol) aux fuel node roots)
    {left middle right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (_middle_mem : middle ∈ roots) (right_mem : right ∈ roots)
    {leftMiddle middleRight : OccurrenceComparison} {composed : Ordering}
    (left_middle : compareOccurrenceBranches? mol aux fuel left middle = some leftMiddle)
    (middle_right : compareOccurrenceBranches? mol aux fuel middle right = some middleRight)
    (composition :
      composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering = some composed) :
    ∃ leftRight,
      compareOccurrenceBranches? mol aux fuel left right = some leftRight ∧
        leftRight.ordering = composed := by
  rcases frame.comparison_exists left_mem right_mem with ⟨leftRight, left_right⟩
  refine ⟨leftRight, left_right, ?_⟩
  exact compareOccurrenceBranches_ordering_compose_failClosed_of_three_success
    mol aux fuel left_middle middle_right left_right composition

/-- Senior-or-equal comparison on the actual certified frame is a preorder: if neither checked
premise is `lt`, the checked endpoint is not `lt`. -/
theorem productionRule6InitialComparator_senior_preorder_on_certified_frame
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : Rule6FrameCertificate (mol := mol) aux fuel node roots)
    (left middle right : Nat) (left_bound : left < 4) (middle_bound : middle < 4)
    (right_bound : right < 4)
    (left_middle : compareRule6InitialRanks? (mol := mol) aux fuel roots frame.sorted
      left middle ≠ some Ordering.lt)
    (middle_right : compareRule6InitialRanks? (mol := mol) aux fuel roots frame.sorted
      middle right ≠ some Ordering.lt) :
    compareRule6InitialRanks? (mol := mol) aux fuel roots frame.sorted left right ≠
      some Ordering.lt := by
  have leftMiddleEq := frame.partition.comparison_eq_of_bounds left_bound middle_bound
  have middleRightEq := frame.partition.comparison_eq_of_bounds middle_bound right_bound
  have leftMiddleExpected :
      rule6ExpectedPartitionOrdering frame.adjacent left middle ≠ Ordering.lt := by
    intro equal
    apply left_middle
    simpa [equal] using leftMiddleEq
  have middleRightExpected :
      rule6ExpectedPartitionOrdering frame.adjacent middle right ≠ Ordering.lt := by
    intro equal
    apply middle_right
    simpa [equal] using middleRightEq
  have endpointExpected :
      rule6ExpectedPartitionOrdering frame.adjacent left right ≠ Ordering.lt := by
    apply rule6GroupOrdering_senior_preorder leftMiddleExpected middleRightExpected
  intro endpointLt
  have endpointEq := frame.partition.comparison_eq_of_bounds left_bound right_bound
  have equal : rule6ExpectedPartitionOrdering frame.adjacent left right = Ordering.lt := by
    exact Option.some.inj (endpointEq.symm.trans endpointLt)
  exact endpointExpected equal

/-- Independent Rule-6 result relation.  Each constructor states a full four-ligand carrier,
admissible production reference judgment (or S4 agreement certificate), parity, topology gate,
and exact final ranking payload without mentioning `rule6Result?`. -/
inductive Rule6ResultDerivation (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (roots : List CanonicalRerootCursor) :
    OccurrenceRule6Result → Prop
  | fourWay {result : OccurrenceRule6Result}
      (frame : Rule6FrameCertificate (mol := mol) aux fuel node roots)
      (group_one : frame.groupCount = 1)
      (agreement : Rule6FourWayAgreement)
      (trace : OccurrenceFourWayTrace (mol := mol) aux fuel roots frame.parity
        frame.ligands frame.sorted agreement)
      (result_eq : result =
        { fact :=
            { key := canonicalOccurrenceKey node
              atom := node.atom
              descriptor := agreement.descriptor
              uppercase := agreement.secondRanking.pseudoComparisons != 1
              priorityPositions := agreement.secondRanking.positions }
          parity := frame.parity
          ligands := frame.ligands
          roots := roots
          sorted := frame.sorted
          adjacent := frame.adjacent
          groupCount := frame.groupCount
          oddTopology? := some false
          carrier := .fourWay agreement }) :
      Rule6ResultDerivation aux fuel node roots result

  | twoGroup {result : OccurrenceRule6Result}
      (frame : Rule6FrameCertificate (mol := mol) aux fuel node roots)
      (group_two : frame.groupCount = 2)
      (references : List Nat)
      (references_eq : references =
        rule6EquivalentReferencePositions frame.sorted frame.adjacent)
      (ranking : Rule6TrackedRanking)
      (trace : OccurrenceEquivalentReferencesTrace (mol := mol) aux fuel roots frame.parity
        frame.ligands frame.sorted references ranking)
      (result_eq : result =
        { fact :=
            { key := canonicalOccurrenceKey node
              atom := node.atom
              descriptor := RawMolecule.descriptorOfParity frame.parity
                (RawMolecule.permutationIsEven ranking.positions)
              uppercase := ranking.pseudoComparisons != 1
              priorityPositions := ranking.positions }
          parity := frame.parity
          ligands := frame.ligands
          roots := roots
          sorted := frame.sorted
          adjacent := frame.adjacent
          groupCount := frame.groupCount
          oddTopology? := some false
          carrier := .twoGroup references ranking }) :
      Rule6ResultDerivation aux fuel node roots result
  | threeGroup {result : OccurrenceRule6Result}
      (frame : Rule6FrameCertificate (mol := mol) aux fuel node roots)
      (group_three : frame.groupCount = 3)
      (reference : Nat) (reference_eq : reference = frame.sorted[1]?.getD 0)
      (referenceRoot : CanonicalRerootCursor)
      (reference_root : roots[reference]? = some referenceRoot)
      (middle_tie : frame.adjacent[1]?.getD none = some Ordering.eq)
      (local_reference : occurrenceBranchHasLocalReference (mol := mol) aux fuel
        [referenceRoot] = true)
      (ranking : Rule6TrackedRanking)
      (trace : OccurrenceEquivalentReferencesTrace (mol := mol) aux fuel roots frame.parity
        frame.ligands frame.sorted [reference] ranking)
      (result_eq : result =
        { fact :=
            { key := canonicalOccurrenceKey node
              atom := node.atom
              descriptor := RS.swap (RawMolecule.descriptorOfParity frame.parity
                (RawMolecule.permutationIsEven ranking.positions))
              uppercase := true
              priorityPositions := ranking.positions }
          parity := frame.parity
          ligands := frame.ligands
          roots := roots
          sorted := frame.sorted
          adjacent := frame.adjacent
          groupCount := frame.groupCount
          oddTopology? := some false
          carrier := .threeGroup reference ranking }) :
      Rule6ResultDerivation aux fuel node roots result

/-- Independent Rule-6 clauses imply the executable four-ligand production result. -/
theorem Rule6ResultDerivation.production_eq {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    {result : OccurrenceRule6Result}
    (derived : Rule6ResultDerivation (mol := mol) aux fuel node roots result) :
    rule6Result? (mol := mol) aux fuel node roots = some result := by
  cases derived with
  | fourWay frame groupOne agreement trace resultEq =>
      subst result
      have ranked := trace.sound
      have filteredLength :
          (frame.adjacent.filter fun decision => decision == some Ordering.gt).length = 0 := by
        have addEq : 1 +
              (frame.adjacent.filter fun decision => decision == some Ordering.gt).length =
            1 + 0 := by
          have countEq : rule6GroupCount frame.adjacent = 1 :=
            frame.groupCount_eq.symm.trans groupOne
          simpa [rule6GroupCount] using countEq
        exact Nat.add_left_cancel addEq
      have filterEmpty :
          frame.adjacent.filter (fun decision => decision == some Ordering.gt) = [] :=
        List.eq_nil_of_length_eq_zero filteredLength
      have noGreater : some Ordering.gt ∉ frame.adjacent := by
        intro member
        have retained : some Ordering.gt ∈
            frame.adjacent.filter (fun decision => decision == some Ordering.gt) :=
          List.mem_filter.mpr ⟨member, by simp⟩
        rw [filterEmpty] at retained
        simp at retained
      simp [rule6Result?, frame.atom_spec, frame.tetrahedral, ← frame.ligands_eq,
        frame.ligands_length, frame.roots_length, frame.ranking.production_eq,
        frame.comparisons.production_eq, frame.adjacent_not_lt, frame.partition.production_eq,
        ← frame.groupCount_eq, frame.odd_false, groupOne, ranked]
  | twoGroup frame groupTwo references referencesEq ranking trace resultEq =>
      subst result
      subst references
      have notOne : frame.groupCount ≠ 1 := by
        intro equal
        exact (by decide : (2 : Nat) ≠ 1) (groupTwo.symm.trans equal)
      have ranked : rankOccurrenceEquivalentReferences? (mol := mol) aux fuel roots frame.parity
          frame.ligands frame.sorted
            (rule6EquivalentReferencePositions frame.sorted frame.adjacent) = some ranking := by
        exact trace.sound
      simp [rule6Result?, frame.atom_spec, frame.tetrahedral, ← frame.ligands_eq,
        frame.ligands_length, frame.roots_length, frame.ranking.production_eq,
        frame.comparisons.production_eq, frame.adjacent_not_lt, frame.partition.production_eq,
        ← frame.groupCount_eq, frame.odd_false, groupTwo,
        ranked, trace.first_unique]
  | threeGroup frame groupThree reference referenceEq referenceRoot referenceRootEq middleTie
      localReference ranking trace resultEq =>
      subst result
      have ranked : rankOccurrenceEquivalentReferences? (mol := mol) aux fuel roots frame.parity
          frame.ligands frame.sorted [reference] = some ranking := by
        exact trace.sound
      have referenceEq' : frame.sorted[1]?.getD 0 = reference := by
        simpa using referenceEq.symm
      have middleTie' : frame.adjacent[1]?.getD none = some Ordering.eq := by
        simpa using middleTie
      have notOne : frame.groupCount ≠ 1 := by
        intro equal
        exact (by decide : (3 : Nat) ≠ 1) (groupThree.symm.trans equal)
      have notTwo : frame.groupCount ≠ 2 := by
        intro equal
        exact (by decide : (3 : Nat) ≠ 2) (groupThree.symm.trans equal)
      simp [rule6Result?, frame.atom_spec, frame.tetrahedral, ← frame.ligands_eq,
        frame.ligands_length, frame.roots_length, frame.ranking.production_eq,
        frame.comparisons.production_eq, frame.adjacent_not_lt, frame.partition.production_eq,
        ← frame.groupCount_eq, frame.odd_false, groupThree]
      rw [referenceEq', referenceRootEq]
      simp [middleTie', localReference, ranked, trace.first_unique]

/-- Every successful executable Rule-6 result has an independently constructed carrier
derivation and a shared production descriptor certificate. -/
theorem rule6ResultDerivation_of_production {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    {result : OccurrenceRule6Result}
    (computed : rule6Result? (mol := mol) aux fuel node roots = some result) :
    Rule6ResultDerivation (mol := mol) aux fuel node roots result := by
  cases atomEq : mol.atomAt? node.atom with
  | none => simp [rule6Result?, atomEq] at computed
  | some spec =>
      cases parityEq : spec.tetrahedral? with
      | none => simp [rule6Result?, atomEq, parityEq] at computed
      | some parity =>
          let ligands := mol.ligandsWithLonePair node.atom
          by_cases ligandsLength : ligands.length = 4
          · by_cases rootsLength : roots.length = 4
            · cases sortedEq : sortRule6InitialPositions? (mol := mol) aux fuel roots
                  (List.range 4) with
              | none =>
                  simp [rule6Result?, atomEq, ligands, ligandsLength,
                    rootsLength, sortedEq] at computed
              | some sorted =>
                cases adjacentEq : compareRule6InitialAdjacent? (mol := mol) aux fuel roots
                    sorted with
                | none =>
                    simp [rule6Result?, atomEq, ligands, ligandsLength,
                      rootsLength, sortedEq, adjacentEq] at computed
                | some adjacent =>
                  by_cases adjacentNotLt : some Ordering.lt ∉ adjacent
                  · have partitionEq : checkRule6InitialDirectedPairs? (mol := mol) aux fuel roots
                        sorted adjacent rule6InitialDirectedRankPairs = some () := by
                      cases equation : checkRule6InitialDirectedPairs? (mol := mol) aux fuel roots
                          sorted adjacent rule6InitialDirectedRankPairs with
                      | none =>
                          simp [rule6Result?, atomEq, ligands, ligandsLength,
                            rootsLength, sortedEq, adjacentEq, adjacentNotLt, equation] at computed
                      | some gate =>
                          cases gate
                          rfl
                    let groupCount := rule6GroupCount adjacent
                    let oddTopology? := hasOddConstitutionAutomorphismAtCenter mol node.atom ligands
                      (fun left right =>
                        rule6CompareAt? (mol := mol) aux fuel roots left right == some Ordering.eq)
                    by_cases oddFalse : oddTopology? = some false
                    · let frame : Rule6FrameCertificate (mol := mol) aux fuel node roots :=
                        { spec := spec
                          parity := parity
                          ligands := ligands
                          sorted := sorted
                          adjacent := adjacent
                          groupCount := groupCount
                          atom_spec := atomEq
                          tetrahedral := parityEq
                          ligands_eq := rfl
                          ligands_length := ligandsLength
                          roots_length := rootsLength
                          ranking := sortRule6InitialDerivation_of_production aux fuel roots
                            (List.range 4) sorted sortedEq
                          comparisons := rule6InitialAdjacentDerivation_of_production aux fuel roots
                            sorted adjacent adjacentEq
                          adjacent_not_lt := adjacentNotLt
                          partition := rule6InitialDirectedPairsDerivation_of_production aux fuel
                            roots sorted adjacent rule6InitialDirectedRankPairs partitionEq
                          groupCount_eq := rfl
                          odd_false := oddFalse }
                      by_cases groupOne : groupCount = 1
                      · cases rankedEq : rankOccurrenceFourWayReferences? (mol := mol) aux fuel roots
                            parity ligands sorted with
                        | none =>
                            simp [rule6Result?, atomEq, parityEq, ligands, ligandsLength,
                              rootsLength, sortedEq, adjacentEq, adjacentNotLt, partitionEq, groupCount,
                              oddTopology?, oddFalse, groupOne, rankedEq] at computed
                        | some agreement =>
                            have resultEq : result =
                                { fact :=
                                    { key := canonicalOccurrenceKey node
                                      atom := node.atom
                                      descriptor := agreement.descriptor
                                      uppercase := agreement.secondRanking.pseudoComparisons != 1
                                      priorityPositions := agreement.secondRanking.positions }
                                  parity := parity
                                  ligands := ligands
                                  roots := roots
                                  sorted := sorted
                                  adjacent := adjacent
                                  groupCount := groupCount
                                  oddTopology? := some false
                                  carrier := .fourWay agreement } := by
                              simpa [rule6Result?, atomEq, parityEq, ligands, ligandsLength,
                                rootsLength, sortedEq, adjacentEq, adjacentNotLt, partitionEq, groupCount,
                                oddTopology?, oddFalse, groupOne, rankedEq] using computed.symm
                            rcases occurrenceFourWayTrace_complete aux fuel roots parity ligands
                              sorted agreement rankedEq with ⟨trace⟩
                            exact .fourWay frame groupOne agreement
                              (by simpa [frame] using trace)
                              (by simpa [frame] using resultEq)
                      · by_cases groupTwo : groupCount = 2
                        · let references := rule6EquivalentReferencePositions sorted adjacent
                          cases rankedEq : rankOccurrenceEquivalentReferences? (mol := mol) aux fuel
                              roots parity ligands sorted references with
                          | none =>
                              simp [rule6Result?, atomEq, parityEq, ligands, ligandsLength,
                                rootsLength, sortedEq, adjacentEq, adjacentNotLt, partitionEq, groupCount,
                                oddTopology?, oddFalse, groupTwo, references, rankedEq]
                                at computed
                          | some ranking =>
                              by_cases unique : ranking.unique = true
                              · rcases occurrenceEquivalentReferencesTrace_complete aux fuel roots
                                    parity ligands sorted references ranking rankedEq with ⟨trace⟩
                                have resultEq : result =
                                    { fact :=
                                        { key := canonicalOccurrenceKey node
                                          atom := node.atom
                                          descriptor := RawMolecule.descriptorOfParity parity
                                            (RawMolecule.permutationIsEven ranking.positions)
                                          uppercase := ranking.pseudoComparisons != 1
                                          priorityPositions := ranking.positions }
                                      parity := parity
                                      ligands := ligands
                                      roots := roots
                                      sorted := sorted
                                      adjacent := adjacent
                                      groupCount := groupCount
                                      oddTopology? := some false
                                      carrier := .twoGroup references ranking } := by
                                  simpa [rule6Result?, atomEq, parityEq, ligands, ligandsLength,
                                    rootsLength, sortedEq, adjacentEq, adjacentNotLt, partitionEq, groupCount,
                                    oddTopology?, oddFalse, groupOne, groupTwo, references, rankedEq,
                                    unique] using computed.symm
                                exact .twoGroup frame groupTwo references rfl ranking
                                  (by simpa [frame] using trace)
                                  (by simpa [frame] using resultEq)
                              · simp [rule6Result?, atomEq, parityEq, ligands, ligandsLength,
                                  rootsLength, sortedEq, adjacentEq, adjacentNotLt, partitionEq, groupCount,
                                  oddTopology?, oddFalse, groupTwo, references, rankedEq,
                                  unique] at computed
                        · by_cases groupThree : groupCount = 3
                          · let reference := sorted[1]?.getD 0
                            cases referenceRootEq : roots[reference]? with
                            | none =>
                                simp [rule6Result?, atomEq, ligands, ligandsLength,
                                  rootsLength, sortedEq, adjacentEq, adjacentNotLt, partitionEq, groupCount,
                                  oddTopology?, oddFalse, groupThree, reference,
                                  referenceRootEq] at computed
                            | some referenceRoot =>
                                by_cases middleTie : adjacent[1]?.getD none = some Ordering.eq
                                · by_cases localReference : occurrenceBranchHasLocalReference
                                    (mol := mol) aux fuel [referenceRoot] = true
                                  · cases rankedEq : rankOccurrenceEquivalentReferences? (mol := mol)
                                        aux fuel roots parity ligands sorted [reference] with
                                    | none =>
                                        simp [rule6Result?, atomEq, parityEq, ligands,
                                          ligandsLength, rootsLength, sortedEq, adjacentEq,
                                          adjacentNotLt, partitionEq, groupCount, oddTopology?, oddFalse,
                                          groupThree, reference, referenceRootEq,
                                          middleTie, localReference, rankedEq] at computed
                                    | some ranking =>
                                        by_cases unique : ranking.unique = true
                                        · rcases occurrenceEquivalentReferencesTrace_complete
                                              aux fuel roots parity ligands sorted [reference]
                                                ranking rankedEq with ⟨trace⟩
                                          have resultEq : result =
                                              { fact :=
                                                  { key := canonicalOccurrenceKey node
                                                    atom := node.atom
                                                    descriptor := RS.swap
                                                      (RawMolecule.descriptorOfParity parity
                                                        (RawMolecule.permutationIsEven
                                                          ranking.positions))
                                                    uppercase := true
                                                    priorityPositions := ranking.positions }
                                                parity := parity
                                                ligands := ligands
                                                roots := roots
                                                sorted := sorted
                                                adjacent := adjacent
                                                groupCount := groupCount
                                                oddTopology? := some false
                                                carrier := .threeGroup reference ranking } := by
                                            simpa [rule6Result?, atomEq, parityEq, ligands,
                                              ligandsLength, rootsLength, sortedEq, adjacentEq,
                                              adjacentNotLt, partitionEq, groupCount, oddTopology?, oddFalse,
                                              groupOne, groupTwo, groupThree, reference,
                                              referenceRootEq, middleTie, localReference, rankedEq,
                                              unique] using computed.symm
                                          exact .threeGroup frame groupThree reference rfl referenceRoot
                                            referenceRootEq middleTie localReference ranking
                                            (by simpa [frame] using trace)
                                            (by simpa [frame] using resultEq)
                                        · simp [rule6Result?, atomEq, parityEq, ligands,
                                            ligandsLength, rootsLength, sortedEq, adjacentEq,
                                            adjacentNotLt, partitionEq, groupCount, oddTopology?, oddFalse,
                                            groupThree, reference,
                                            referenceRootEq, middleTie, localReference, rankedEq,
                                            unique] at computed
                                  · simp [rule6Result?, atomEq, ligands, ligandsLength,
                                      rootsLength, sortedEq, adjacentEq, adjacentNotLt, partitionEq, groupCount,
                                      oddTopology?, oddFalse, groupThree,
                                      reference, referenceRootEq, localReference] at computed
                                · simp [rule6Result?, atomEq, ligands, ligandsLength,
                                    rootsLength, sortedEq, adjacentEq, adjacentNotLt, partitionEq, groupCount,
                                    oddTopology?, oddFalse, groupThree, reference,
                                    referenceRootEq, middleTie] at computed
                          · change ¬(1 + (adjacent.filter fun decision =>
                                decision == some Ordering.gt).length = 1) at groupOne
                            have simplified := computed
                            simp [rule6Result?, atomEq, parityEq, ligands, ligandsLength,
                              rootsLength, sortedEq, adjacentEq, adjacentNotLt, partitionEq, groupCount,
                              oddTopology?, oddFalse, groupTwo, groupThree] at simplified
                            exact (groupOne (by simpa [rule6GroupCount] using simplified.1)).elim
                    · simp [rule6Result?, atomEq, ligands, ligandsLength, rootsLength, sortedEq,
                        oddTopology?, oddFalse]
                        at computed
                  · simp [rule6Result?, atomEq, parityEq, ligands, ligandsLength, rootsLength, sortedEq, adjacentEq,
                    adjacentNotLt] at computed
            · simp [rule6Result?, atomEq, ligands, ligandsLength, rootsLength]
                at computed
          · simp [rule6Result?, atomEq, ligands, ligandsLength] at computed

/-- A successful production Rule-6 calculation on the exact generated ligand frame yields the
chemically scoped admissibility certificate.  In particular, all label/traversal/fuel/capacity
checks needed by every directed pair have already succeeded. -/
theorem cipAdmissibleFrame_of_rule6Result
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    {result : OccurrenceRule6Result}
    (ligand_frame : occurrenceLigandFrame? mol node = some roots)
    (computed : rule6Result? (mol := mol) aux fuel node roots = some result) :
    Nonempty (CIPAdmissibleFrame (mol := mol) aux fuel node roots) := by
  have derived := rule6ResultDerivation_of_production computed
  cases derived with
  | fourWay frame groupOne agreement trace resultEq =>
      exact ⟨CIPAdmissibleFrame.ofRule6FrameCertificate frame ligand_frame⟩
  | twoGroup frame groupTwo references referencesEq ranking trace resultEq =>
      exact ⟨CIPAdmissibleFrame.ofRule6FrameCertificate frame ligand_frame⟩
  | threeGroup frame groupThree reference referenceEq referenceRoot referenceRootEq middleTie
      localReference ranking trace resultEq =>
      exact ⟨CIPAdmissibleFrame.ofRule6FrameCertificate frame ligand_frame⟩

/-- Production-facing endpoint law requiring no manually assembled all-pairs certificate.  A
successful Rule-6 result on the exact occurrence ligand frame supplies admissibility internally. -/
theorem rule6Result_endpoint_of_two_success
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    {result : OccurrenceRule6Result}
    (ligand_frame : occurrenceLigandFrame? mol node = some roots)
    (computed : rule6Result? (mol := mol) aux fuel node roots = some result)
    {left middle right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (middle_mem : middle ∈ roots) (right_mem : right ∈ roots)
    {leftMiddle middleRight : OccurrenceComparison} {composed : Ordering}
    (left_middle : compareOccurrenceBranches? mol aux fuel left middle = some leftMiddle)
    (middle_right : compareOccurrenceBranches? mol aux fuel middle right = some middleRight)
    (composition :
      composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering = some composed) :
    ∃ leftRight,
      compareOccurrenceBranches? mol aux fuel left right = some leftRight ∧
        leftRight.ordering = composed := by
  rcases cipAdmissibleFrame_of_rule6Result ligand_frame computed with ⟨frame⟩
  exact frame.endpoint_of_two_success left_mem middle_mem right_mem
    left_middle middle_right composition

theorem rule6ResultDerivation_iff_production (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (result : OccurrenceRule6Result) :
    Rule6ResultDerivation (mol := mol) aux fuel node roots result ↔
      rule6Result? (mol := mol) aux fuel node roots = some result :=
  ⟨Rule6ResultDerivation.production_eq, rule6ResultDerivation_of_production⟩

/-- Final occurrences are the only frames for which production ligand positions are definitionally
aligned with the molecule's written ligand list. -/
def FinalTarget {discovery : Discovery mol} (target : Occurrence discovery) : Prop :=
  ∃ marker : Unit, target.node = Sum.inl marker

/-- Declarative failure of the ordinary clauses.  This is intentionally stated against the
independent relation; its equivalence with executable failure is proved below. -/
def NoOrdinaryDerivation (discovery : Discovery mol) (fuel : Nat) (state : State discovery)
    (target : Occurrence discovery) : Prop :=
  ∀ label, ¬ OrdinaryDerivation discovery fuel state target label

theorem noOrdinaryDerivation_iff (discovery : Discovery mol) (fuel : Nat)
    (state : State discovery) (target : Occurrence discovery) :
    NoOrdinaryDerivation discovery fuel state target ↔
      ordinaryLabel? discovery fuel state target = none := by
  constructor
  · intro absent
    cases equation : ordinaryLabel? discovery fuel state target with
    | none => rfl
    | some label =>
        exact (absent label
          ((ordinaryDerivation_iff discovery fuel state target label).2 equation)).elim
  · intro equation label derived
    have accepted := (ordinaryDerivation_iff discovery fuel state target label).1 derived
    rw [equation] at accepted
    simp at accepted

/-- Rule-6 label over the same root-local collision-safe state as ordinary derivation. -/
def rule6Label? (discovery : Discovery mol) (fuel : Nat) (state : State discovery)
    (target : Occurrence discovery) : Option (Label discovery) := do
  match frameEq : target.node with
  | .inr _ => none
  | .inl marker =>
      let aux ← executableStateFor? discovery state target
      let roots ← targetLigandFrame? discovery target
      let result ← rule6Result? (mol := mol) aux fuel
        (sourceNode discovery target) roots
      some (labelOfFinalFact discovery target result.fact marker frameEq)

/-- Decomposed Rule-6 derivation with the full carrier, admissible-reference, odd-topology, and
parity clauses exposed independently of the combined executable step. -/
inductive Rule6Derivation (discovery : Discovery mol) (fuel : Nat) (state : State discovery)
    (target : Occurrence discovery) (label : Label discovery) : Prop
  | intro (ordinary_absent : NoOrdinaryDerivation discovery fuel state target)
      (marker : Unit) (frame_eq : target.node = Sum.inl marker)
      (aux : OneCenter.OccurrenceAuxState) (roots : List CanonicalRerootCursor)
      (result : OccurrenceRule6Result)
      (aux_eq : executableStateFor? discovery state target = some aux)
      (roots_eq : targetLigandFrame? discovery target = some roots)
      (result_derivation : Rule6ResultDerivation (mol := mol) aux fuel
        (sourceNode discovery target) roots result)
      (label_eq : labelOfFinalFact discovery target result.fact marker frame_eq = label) :
      Rule6Derivation discovery fuel state target label

theorem rule6Label?_eq_some_iff (discovery : Discovery mol) (fuel : Nat)
    (state : State discovery) (target : Occurrence discovery) (label : Label discovery) :
    rule6Label? discovery fuel state target = some label ↔
      ∃ marker,
        ∃ frameEq : target.node = Sum.inl marker,
          ∃ aux roots result,
            executableStateFor? discovery state target = some aux ∧
            targetLigandFrame? discovery target = some roots ∧
            rule6Result? (mol := mol) aux fuel (sourceNode discovery target) roots =
              some result ∧
            labelOfFinalFact discovery target result.fact marker frameEq = label := by
  rcases target with ⟨root, node⟩
  rcases node with marker | branch
  · cases auxEq : executableStateFor? discovery state { root := root, node := Sum.inl marker } with
    | none => simp [rule6Label?, auxEq]
    | some aux =>
        cases rootsEq : targetLigandFrame? discovery
            { root := root, node := Sum.inl marker } with
        | none => simp [rule6Label?, auxEq, rootsEq]
        | some roots =>
            cases resultEq : rule6Result? (mol := mol) aux fuel
                (sourceNode discovery { root := root, node := Sum.inl marker }) roots with
            | none => simp [rule6Label?, auxEq, rootsEq, resultEq]
            | some result =>
                have finalEquation : rule6Label? discovery fuel state
                    { root := root, node := Sum.inl marker } =
                      some (labelOfFinalFact discovery
                        { root := root, node := Sum.inl marker } result.fact marker rfl) := by
                  simp [rule6Label?, auxEq, rootsEq, resultEq]
                constructor
                · intro accepted
                  have labelEq := Option.some.inj (finalEquation.symm.trans accepted)
                  exact ⟨marker, rfl, aux, roots, result, rfl, rfl, resultEq, labelEq⟩
                · rintro ⟨otherMarker, frameEq, otherAux, otherRoots, otherResult,
                    otherAuxEq, otherRootsEq, otherResultEq, labelEq⟩
                  have auxEqual := Option.some.inj otherAuxEq
                  subst otherAux
                  have rootsEqual := Option.some.inj otherRootsEq
                  subst otherRoots
                  have resultEqual := Option.some.inj (otherResultEq.symm.trans resultEq)
                  subst otherResult
                  have markerEq : otherMarker = marker := Subsingleton.elim _ _
                  subst otherMarker
                  exact finalEquation.trans (congrArg some labelEq)
  · simp [rule6Label?]

theorem rule6Derivation_iff (discovery : Discovery mol) (fuel : Nat)
    (state : State discovery) (target : Occurrence discovery) (label : Label discovery) :
    Rule6Derivation discovery fuel state target label ↔
      NoOrdinaryDerivation discovery fuel state target ∧
        rule6Label? discovery fuel state target = some label := by
  constructor
  · rintro ⟨ordinaryAbsent, marker, frameEq, aux, roots, result, auxEq, rootsEq,
      resultDerivation, labelEq⟩
    refine ⟨ordinaryAbsent, ?_⟩
    apply (rule6Label?_eq_some_iff discovery fuel state target label).2
    exact ⟨marker, frameEq, aux, roots, result, auxEq, rootsEq,
      resultDerivation.production_eq, labelEq⟩
  · rintro ⟨ordinaryAbsent, accepted⟩
    rcases (rule6Label?_eq_some_iff discovery fuel state target label).1 accepted with
      ⟨marker, frameEq, aux, roots, result, auxEq, rootsEq, resultEq, labelEq⟩
    exact .intro ordinaryAbsent marker frameEq aux roots result auxEq rootsEq
      (rule6ResultDerivation_of_production resultEq) labelEq

/-- Declarative failure of Rule 6, including its ordinary-precedence premise. -/
def NoRule6Derivation (discovery : Discovery mol) (fuel : Nat) (state : State discovery)
    (target : Occurrence discovery) : Prop :=
  ∀ label, ¬ Rule6Derivation discovery fuel state target label

/-! ## Combined executable and independent derivation -/

/-- Production precedence: Rule 6 is evaluated only after ordinary Rules 4b/5 return `none`. -/
def derive? (discovery : Discovery mol) (fuel : Nat) (state : State discovery)
    (target : Occurrence discovery) : Option (Label discovery) :=
  match ordinaryLabel? discovery fuel state target with
  | some label => some label
  | none => rule6Label? discovery fuel state target

theorem ordinaryLabel?_eq_of_depth_agree (discovery : Discovery mol) (fuel : Nat)
    {left right : State discovery} (target : Occurrence discovery)
    (agree : ∀ source, DepthDependency source target → left source = right source) :
    ordinaryLabel? discovery fuel left target = ordinaryLabel? discovery fuel right target := by
  unfold ordinaryLabel?
  rw [executableStateFor?_eq_of_depth_agree discovery target agree]

theorem rule6Label?_eq_of_depth_agree (discovery : Discovery mol) (fuel : Nat)
    {left right : State discovery} (target : Occurrence discovery)
    (agree : ∀ source, DepthDependency source target → left source = right source) :
    rule6Label? discovery fuel left target = rule6Label? discovery fuel right target := by
  unfold rule6Label?
  rw [executableStateFor?_eq_of_depth_agree discovery target agree]

theorem derive?_eq_of_depth_agree (discovery : Discovery mol) (fuel : Nat)
    {left right : State discovery} (target : Occurrence discovery)
    (agree : ∀ source, DepthDependency source target → left source = right source) :
    derive? discovery fuel left target = derive? discovery fuel right target := by
  have ordinaryEq := ordinaryLabel?_eq_of_depth_agree discovery fuel target agree
  have rule6Eq := rule6Label?_eq_of_depth_agree discovery fuel target agree
  unfold derive?
  rw [ordinaryEq]
  cases ordinaryLabel? discovery fuel right target <;> simp [rule6Eq]

/-- Independent declarative clauses for the complete optional production outcome. -/
inductive Derivation (discovery : Discovery mol) (fuel : Nat) (state : State discovery)
    (target : Occurrence discovery) : Option (Label discovery) → Prop
  | ordinary {label : Label discovery} :
      OrdinaryDerivation (mol := mol) discovery fuel state target label →
      Derivation discovery fuel state target (some label)
  | rule6 {label : Label discovery} :
      Rule6Derivation (mol := mol) discovery fuel state target label →
      Derivation discovery fuel state target (some label)
  | noLabel : NoOrdinaryDerivation discovery fuel state target →
      NoRule6Derivation discovery fuel state target →
      Derivation discovery fuel state target none

theorem derivation_iff_derive? (discovery : Discovery mol) (fuel : Nat)
    (state : State discovery) (target : Occurrence discovery)
    (outcome : Option (Label discovery)) :
    Derivation discovery fuel state target outcome ↔
      derive? discovery fuel state target = outcome := by
  constructor
  · intro derived
    cases derived with
    | ordinary ordinary =>
        have accepted := (ordinaryDerivation_iff discovery fuel state target _).1 ordinary
        simp [derive?, accepted]
    | rule6 rule6 =>
        have clauses := (rule6Derivation_iff discovery fuel state target _).1 rule6
        have ordinaryNone :=
          (noOrdinaryDerivation_iff discovery fuel state target).1 clauses.1
        simp [derive?, ordinaryNone, clauses.2]
    | noLabel ordinaryAbsent rule6Absent =>
        have ordinaryNone :=
          (noOrdinaryDerivation_iff discovery fuel state target).1 ordinaryAbsent
        have rule6None : rule6Label? discovery fuel state target = none := by
          cases equation : rule6Label? discovery fuel state target with
          | none => rfl
          | some label =>
              exact (rule6Absent label
                ((rule6Derivation_iff discovery fuel state target label).2
                  ⟨ordinaryAbsent, equation⟩)).elim
        simp [derive?, ordinaryNone, rule6None]
  · intro equation
    cases ordinaryEq : ordinaryLabel? discovery fuel state target with
    | some label =>
        have ordinary :=
          (ordinaryDerivation_iff discovery fuel state target label).2 ordinaryEq
        have derived : Derivation discovery fuel state target (some label) := .ordinary ordinary
        rwa [← equation, derive?, ordinaryEq]
    | none =>
        have ordinaryAbsent : NoOrdinaryDerivation discovery fuel state target :=
          (noOrdinaryDerivation_iff discovery fuel state target).2 ordinaryEq
        cases rule6Eq : rule6Label? discovery fuel state target with
        | some label =>
            have rule6 :=
              (rule6Derivation_iff discovery fuel state target label).2
                ⟨ordinaryAbsent, rule6Eq⟩
            have derived : Derivation discovery fuel state target (some label) := .rule6 rule6
            rwa [← equation, derive?, ordinaryEq, rule6Eq]
        | none =>
            have rule6Absent : NoRule6Derivation discovery fuel state target := by
              intro label derived
              have accepted :=
                (rule6Derivation_iff discovery fuel state target label).1 derived |>.2
              rw [rule6Eq] at accepted
              simp at accepted
            have derived : Derivation discovery fuel state target none :=
              .noLabel ordinaryAbsent rule6Absent
            rwa [← equation, derive?, ordinaryEq, rule6Eq]

theorem derivation_functional (discovery : Discovery mol) (fuel : Nat)
    (state : State discovery) (target : Occurrence discovery)
    {first second : Option (Label discovery)}
    (hfirst : Derivation discovery fuel state target first)
    (hsecond : Derivation discovery fuel state target second) : first = second := by
  have firstEq := (derivation_iff_derive? discovery fuel state target first).1 hfirst
  have secondEq := (derivation_iff_derive? discovery fuel state target second).1 hsecond
  exact firstEq.symm.trans secondEq

/-! ## Production instantiation of the generic occurrence fixed-point core -/

/-- The production occurrence system connects the proof-relevant Rule-4b/5/6 derivation above
to the separately executable combined evaluator. -/
def occurrenceSystem (discovery : Discovery mol) (fuel : Nat) :
    OccurrenceSystem (FinalUnit mol) (Occurrence discovery) (Label discovery) where
  finalOccurrence := finalOccurrence discovery
  descriptorOf := Label.descriptor
  DeclarativeDerivation := fun state target outcome =>
    Derivation (mol := mol) discovery fuel state target outcome
  executableStep := fun state target => derive? (mol := mol) discovery fuel state target

/-- Package a concrete one-coordinate perturbation of the actual production evaluator as the
semantic essential-input relation without re-elaborating the system implementation at each
molecular witness. -/
theorem essentialInput_of_derive_ne (discovery : Discovery mol) (fuel : Nat)
    (left right : State discovery) (source target : Occurrence discovery)
    (differs : OccurrenceSystem.DiffersOnlyAt left right source)
    (changes : derive? discovery fuel left target ≠ derive? discovery fuel right target) :
    (occurrenceSystem discovery fuel).EssentialInput source target :=
  ⟨left, right, differs, changes⟩

/-- Independent derivation and executable evaluation agree on every complete optional outcome. -/
theorem derivationStepCorrespondence (discovery : Discovery mol) (fuel : Nat) :
    (occurrenceSystem discovery fuel).DerivationStepCorrespondence := by
  intro state target outcome
  exact derivation_iff_derive? discovery fuel state target outcome

/-- The concrete production model is equivalent to regeneration by the actual Rules-4b/5/6
evaluator.  This is the specialized fixed-point soundness/completeness theorem. -/
theorem cipModel_iff_regenerates (discovery : Discovery mol) (fuel : Nat)
    (state : State discovery) :
    (occurrenceSystem discovery fuel).CIPModel state ↔
      (occurrenceSystem discovery fuel).Regenerates state state :=
  (occurrenceSystem discovery fuel).cipModel_iff_regenerates
    (derivationStepCorrespondence discovery fuel) state

/-- Production evaluation consults only strict deeper occurrences of the same discovered root. -/
theorem evaluatorLocalFor_depthDependency (discovery : Discovery mol) (fuel : Nat) :
    (occurrenceSystem discovery fuel).EvaluatorLocalFor
      (@DepthDependency mol discovery) := by
  intro left right target agree
  exact derive?_eq_of_depth_agree discovery fuel target agree

/-- Every semantically essential production input is a strict deeper predecessor at the same
root.  Thus the declared depth relation is connected to, and bounds, the exact local view. -/
theorem essentialInput_depthDependency (discovery : Discovery mol) (fuel : Nat)
    {source target : Occurrence discovery}
    (essential : (occurrenceSystem discovery fuel).EssentialInput source target) :
    DepthDependency source target :=
  (occurrenceSystem discovery fuel).essentialInput_minimal
    (@DepthDependency mol discovery)
    (evaluatorLocalFor_depthDependency discovery fuel) essential

/-- The exact semantic essential-input relation is local and is the least such relation; in
particular it is contained in the strict root-relative depth relation above. -/
theorem essentialInput_isLeast_and_depthBounded (discovery : Discovery mol) (fuel : Nat) :
    (occurrenceSystem discovery fuel).EvaluatorLocalFor
        (occurrenceSystem discovery fuel).EssentialInput ∧
      (∀ source target,
        (occurrenceSystem discovery fuel).EssentialInput source target →
          DepthDependency source target) := by
  constructor
  · exact (occurrenceSystem discovery fuel).evaluatorLocalFor_essential
  · intro source target essential
    exact essentialInput_depthDependency discovery fuel essential

/-- The complete production occurrence state exists and is unique.  The proof uses strict
root-relative depth well-foundedness, evaluator locality, and the independently proved
derivation/evaluator correspondence. -/
theorem existsUnique_cipModel (discovery : Discovery mol) (fuel : Nat) :
    ∃! state, (occurrenceSystem discovery fuel).CIPModel state :=
  (occurrenceSystem discovery fuel).existsUnique_cipModel_of_wellFounded
    (derivationStepCorrespondence discovery fuel)
    (@DepthDependency mol discovery)
    (depthDependency_wellFounded discovery)
    (evaluatorLocalFor_depthDependency discovery fuel)

/-- The concrete monotone dependency-ready scheduler decodes to the production Rules-4b/5/6
model.  This specializes the scheduler simulation to the actual root-relative depth equations. -/
theorem schedulerClosure_cipModel (discovery : Discovery mol) (fuel : Nat) :
    (occurrenceSystem discovery fuel).CIPModel
      (OccurrenceScheduler.decode (occurrenceSystem discovery fuel)
        (@DepthDependency mol discovery)
        (OccurrenceScheduler.closure (occurrenceSystem discovery fuel)
          (@DepthDependency mol discovery))) := by
  exact OccurrenceScheduler.decode_closure_cipModel
    (occurrenceSystem discovery fuel)
    (derivationStepCorrespondence discovery fuel)
    (@DepthDependency mol discovery)
    (depthDependency_wellFounded discovery)
    (evaluatorLocalFor_depthDependency discovery fuel)

/-- Every production model is exactly the decoded monotone scheduler closure. -/
theorem schedulerClosure_eq_model (discovery : Discovery mol) (fuel : Nat)
    {state : State discovery}
    (model : (occurrenceSystem discovery fuel).CIPModel state) :
    OccurrenceScheduler.decode (occurrenceSystem discovery fuel)
        (@DepthDependency mol discovery)
        (OccurrenceScheduler.closure (occurrenceSystem discovery fuel)
          (@DepthDependency mol discovery)) = state := by
  exact OccurrenceScheduler.decode_closure_eq_model
    (occurrenceSystem discovery fuel)
    (derivationStepCorrespondence discovery fuel)
    (@DepthDependency mol discovery)
    (depthDependency_wellFounded discovery)
    (evaluatorLocalFor_depthDependency discovery fuel)
    model

/-- The state-sensitive production descriptor judgment crosses the occurrence model boundary.
It requires the literal root-local state encoding and then either the actual production
`occurrenceFact?` result, or ordinary production failure followed by the complete four-ligand
Rule-6 executable.  It is not defined in terms of `Derivation`. -/
def ProductionDescriptorJudgment (discovery : Discovery mol) (fuel : Nat)
    (state : State discovery) (unit : FinalUnit mol) (descriptor : Descriptor) : Prop :=
  let target := finalOccurrence discovery unit
  ∃ aux : OneCenter.OccurrenceAuxState,
    executableStateFor? discovery state target = some aux ∧
      ((∃ fact : OccurrenceAuxFact,
          occurrenceFact? mol fuel aux (sourceNode discovery target) = some fact ∧
            descriptorOfFact fact = descriptor) ∨
        (occurrenceFact? mol fuel aux (sourceNode discovery target) = none ∧
          ∃ roots : List CanonicalRerootCursor, ∃ result : OccurrenceRule6Result,
            targetLigandFrame? discovery target = some roots ∧
              rule6Result? (mol := mol) aux fuel (sourceNode discovery target) roots =
                some result ∧
              descriptorOfFact result.fact = descriptor))

/-- The independently defined final derivation is sound and complete for the state-sensitive
production boundary.  The proof crosses both literal production evaluators. -/
theorem productionDescriptorJudgment_iff_finalDescriptorJudgment
    (discovery : Discovery mol) (fuel : Nat) (state : State discovery)
    (unit : FinalUnit mol) (descriptor : Descriptor) :
    ProductionDescriptorJudgment discovery fuel state unit descriptor ↔
      (occurrenceSystem discovery fuel).FinalDescriptorJudgment state unit descriptor := by
  constructor
  · rintro ⟨aux, auxEq, ordinary | rule6⟩
    · rcases ordinary with ⟨fact, productionEq, descriptorEq⟩
      let target := finalOccurrence discovery unit
      let label := labelOfOrdinaryFact discovery target fact fuel aux
        (sourceNode_bind_occurrenceFact_eq discovery target fuel aux fact productionEq)
      have ordinaryDerivation : OrdinaryDerivation discovery fuel state target label :=
        .intro aux fact auxEq (ordinaryFactClauses_of_production productionEq) rfl
      exact ⟨label, .ordinary ordinaryDerivation, descriptorEq⟩
    · rcases rule6 with ⟨ordinaryNone, roots, result, rootsEq, resultEq, descriptorEq⟩
      let target := finalOccurrence discovery unit
      have ordinaryLabelNone : ordinaryLabel? discovery fuel state target = none :=
        (ordinaryLabel?_eq_none_iff_of_aux_eq discovery fuel state target aux auxEq).2
          ordinaryNone
      have ordinaryAbsent : NoOrdinaryDerivation discovery fuel state target :=
        (noOrdinaryDerivation_iff discovery fuel state target).2 ordinaryLabelNone
      let label := labelOfFinalFact discovery target result.fact () rfl
      have rule6Derivation : Rule6Derivation discovery fuel state target label :=
        .intro ordinaryAbsent () rfl aux roots result auxEq rootsEq
          (rule6ResultDerivation_of_production resultEq) rfl
      exact ⟨label, .rule6 rule6Derivation, descriptorEq⟩
  · rintro ⟨label, derived, descriptorEq⟩
    cases derived with
    | ordinary ordinary =>
        rcases ordinary with ⟨aux, fact, auxEq, clauses, labelEq⟩
        subst label
        exact ⟨aux, auxEq, Or.inl ⟨fact, clauses.production_eq, descriptorEq⟩⟩
    | rule6 rule6 =>
        rcases rule6 with
          ⟨ordinaryAbsent, marker, frameEq, aux, roots, result, auxEq, rootsEq,
            resultDerivation, labelEq⟩
        subst label
        have ordinaryLabelNone :=
          (noOrdinaryDerivation_iff discovery fuel state
            (finalOccurrence discovery unit)).1 ordinaryAbsent
        have ordinaryNone :=
          (ordinaryLabel?_eq_none_iff_of_aux_eq discovery fuel state
            (finalOccurrence discovery unit) aux auxEq).1 ordinaryLabelNone
        exact ⟨aux, auxEq, Or.inr ⟨ordinaryNone, roots, result, rootsEq,
          resultDerivation.production_eq, descriptorEq⟩⟩

/-- Automatic one-way production bridge: a complete model assignment at a final occurrence
yields the literal state-sensitive production descriptor judgment.  This is a theorem, not a
structure containing a caller-supplied soundness implication. -/
theorem ProductionBridge
    (discovery : Discovery mol) (fuel : Nat) {state : State discovery}
    (model : (occurrenceSystem discovery fuel).CIPModel state)
    (unit : FinalUnit mol) (label : Label discovery)
    (assigned : state (finalOccurrence discovery unit) = some label) :
    ProductionDescriptorJudgment discovery fuel state unit label.descriptor := by
  apply (productionDescriptorJudgment_iff_finalDescriptorJudgment
    discovery fuel state unit label.descriptor).2
  exact (occurrenceSystem discovery fuel).finalDescriptorJudgment_of_model_assignment
    model unit label assigned

theorem productionDescriptorJudgment_of_model_assignment
    (discovery : Discovery mol) (fuel : Nat) {state : State discovery}
    (model : (occurrenceSystem discovery fuel).CIPModel state)
    (unit : FinalUnit mol) (label : Label discovery)
    (assigned : state (finalOccurrence discovery unit) = some label) :
    ProductionDescriptorJudgment discovery fuel state unit label.descriptor :=
  ProductionBridge discovery fuel model unit label assigned

/-- Every `some` assignment in a complete model carries a decomposed production derivation.  Thus
`priorityPositions`, uppercase/lowercase class, descriptor sense, and reference-frame data in a
model are computed conclusions rather than unchecked candidate payloads. -/
theorem model_assignment_certified_at
    (discovery : Discovery mol) (fuel : Nat) {state : State discovery}
    (model : (occurrenceSystem discovery fuel).CIPModel state)
    (target : Occurrence discovery) (label : Label discovery)
    (assigned : state target = some label) :
    OrdinaryDerivation discovery fuel state target label ∨
      Rule6Derivation discovery fuel state target label := by
  have derived : Derivation discovery fuel state target (some label) := by
    simpa [occurrenceSystem, assigned] using
      model target
  cases derived with
  | ordinary ordinary => exact Or.inl ordinary
  | rule6 rule6 => exact Or.inr rule6

/-- A final model assignment is the final-occurrence specialization of complete assignment
certification. -/
theorem model_assignment_certified
    (discovery : Discovery mol) (fuel : Nat) {state : State discovery}
    (model : (occurrenceSystem discovery fuel).CIPModel state)
    (unit : FinalUnit mol) (label : Label discovery)
    (assigned : state (finalOccurrence discovery unit) = some label) :
    OrdinaryDerivation discovery fuel state (finalOccurrence discovery unit) label ∨
      Rule6Derivation discovery fuel state (finalOccurrence discovery unit) label :=
  model_assignment_certified_at discovery fuel model (finalOccurrence discovery unit) label assigned

/-- Final descriptors are only the projection of the solved occurrence state. -/
theorem finalDescriptorProjection_eq_some_of_assignment
    (discovery : Discovery mol) (fuel : Nat) (state : State discovery)
    (unit : FinalUnit mol) (label : Label discovery)
    (assigned : state (finalOccurrence discovery unit) = some label) :
    (occurrenceSystem discovery fuel).finalDescriptorProjection state unit =
      some label.descriptor := by
  exact (occurrenceSystem discovery fuel).finalDescriptorProjection_eq_some_of_assignment
    state unit label assigned

end ProductionOccurrenceRules456

end DeclarativeCIP
end OneCenter
end TetraStereo
