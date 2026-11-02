import TetraStereo.OneCenter.P93MolecularFullereneRelationalSymmetry

set_option autoImplicit false

/-!
# Executable exact fullerene flag symmetries

The deduplicated flag search already proves that every reached dart has a source word, but its
existing certificate recovers that word with classical choice.  This module reconstructs one
word deterministically by walking the finite reachability recurrence backwards.  It is the
missing executable bridge between the quadratic-state topology theorem and concrete P-93.5.6
symmetry classification.
-/

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

abbrev MolecularFullereneDirectedCarrierEdge
    (input : MolecularFullereneConfigurationInput) :=
  MolecularFullereneCarrierAtom input × MolecularFullereneCarrierAtom input

/-- Canonical lexicographic list representation of a finite directed-edge set.  The `Lex`
wrapper avoids the componentwise order on products. -/
def molecularFullereneSortedDirectedEdges
    (input : MolecularFullereneConfigurationInput)
    (edges : Finset (MolecularFullereneDirectedCarrierEdge input)) :
    List (MolecularFullereneDirectedCarrierEdge input) :=
  ((edges.image fun edge => (toLex edge :
      MolecularFullereneCarrierAtom input ×ₗ MolecularFullereneCarrierAtom input)).sort
        (· ≤ ·)).map ofLex

@[simp] theorem mem_molecularFullereneSortedDirectedEdges_iff
    (input : MolecularFullereneConfigurationInput)
    (edges : Finset (MolecularFullereneDirectedCarrierEdge input))
    (edge : MolecularFullereneDirectedCarrierEdge input) :
    edge ∈ molecularFullereneSortedDirectedEdges input edges ↔ edge ∈ edges := by
  constructor
  · intro present
    rcases List.mem_map.mp present with ⟨lexEdge, lexPresent, unwrapped⟩
    have imagePresent : lexEdge ∈ edges.image (fun candidate => (toLex candidate :
        MolecularFullereneCarrierAtom input ×ₗ MolecularFullereneCarrierAtom input)) := by
      simpa [molecularFullereneSortedDirectedEdges] using lexPresent
    rcases Finset.mem_image.mp imagePresent with ⟨original, originalPresent, wrapped⟩
    have originalEq : ofLex lexEdge = original := by
      rw [← wrapped]
      rfl
    rw [← unwrapped, originalEq]
    exact originalPresent
  · intro present
    unfold molecularFullereneSortedDirectedEdges
    apply List.mem_map.mpr
    refine ⟨toLex edge, ?_, rfl⟩
    simp only [Finset.mem_sort]
    exact Finset.mem_image.mpr ⟨edge, present, rfl⟩

/-- Canonically ordered predecessor candidates.  Carrier atoms inherit their order from source
atom indices; the two flag moves are written explicitly. -/
def molecularFullereneFlagPredecessorCandidates
    (input : MolecularFullereneConfigurationInput)
    (previous : Finset (MolecularFullereneDirectedCarrierEdge input)) :
    List (MolecularFullereneFlagMove × MolecularFullereneDirectedCarrierEdge input) :=
  (molecularFullereneSortedDirectedEdges input previous).flatMap fun edge =>
    [(.reverseEdge, edge), (.continueLeftFace, edge)]

@[simp] theorem mem_molecularFullereneFlagPredecessorCandidates_iff
    (input : MolecularFullereneConfigurationInput)
    (previous : Finset (MolecularFullereneDirectedCarrierEdge input))
    (state : MolecularFullereneFlagMove × MolecularFullereneDirectedCarrierEdge input) :
    state ∈ molecularFullereneFlagPredecessorCandidates input previous ↔
      state.2 ∈ previous := by
  rcases state with ⟨move, edge⟩
  cases move <;> simp [molecularFullereneFlagPredecessorCandidates]

/-- Deterministically select a flag move and previously reached dart producing `target`. -/
def molecularFullereneFlagPredecessor?
    (input : MolecularFullereneConfigurationInput)
    (previous : Finset (MolecularFullereneDirectedCarrierEdge input))
    (target : MolecularFullereneDirectedCarrierEdge input) :
    Option (MolecularFullereneFlagMove × MolecularFullereneDirectedCarrierEdge input) :=
  (molecularFullereneFlagPredecessorCandidates input previous).find? fun state =>
    molecularFullereneFlagStep
      (molecularFullereneContinueForwardFace input) state.1 state.2 = target

theorem molecularFullereneFlagPredecessor?_eq_some_sound
    (input : MolecularFullereneConfigurationInput)
    (previous : Finset (MolecularFullereneDirectedCarrierEdge input))
    (target : MolecularFullereneDirectedCarrierEdge input)
    (state : MolecularFullereneFlagMove × MolecularFullereneDirectedCarrierEdge input)
    (selected : molecularFullereneFlagPredecessor? input previous target = some state) :
    state.2 ∈ previous ∧
      molecularFullereneFlagStep
        (molecularFullereneContinueForwardFace input) state.1 state.2 = target := by
  unfold molecularFullereneFlagPredecessor? at selected
  have statePresent := List.mem_of_find?_eq_some selected
  have stateJudgedBool := List.find?_some selected
  exact ⟨(mem_molecularFullereneFlagPredecessorCandidates_iff
    input previous state).mp statePresent, of_decide_eq_true stateJudgedBool⟩

theorem molecularFullereneFlagPredecessor?_isSome_of_mem_image
    (input : MolecularFullereneConfigurationInput)
    (previous : Finset (MolecularFullereneDirectedCarrierEdge input))
    (target : MolecularFullereneDirectedCarrierEdge input)
    (generated : target ∈
      ((Finset.univ : Finset MolecularFullereneFlagMove) ×ˢ previous).image
        (fun state => molecularFullereneFlagStep
          (molecularFullereneContinueForwardFace input) state.1 state.2)) :
    (molecularFullereneFlagPredecessor? input previous target).isSome := by
  rcases Finset.mem_image.mp generated with ⟨state, statePresent, stateEq⟩
  apply List.find?_isSome.mpr
  exact ⟨state,
    (mem_molecularFullereneFlagPredecessorCandidates_iff
      input previous state).mpr (Finset.mem_product.mp statePresent).2,
    by simpa using stateEq⟩

/-- Recover one source word without enumerating words.  Each recursive step either reuses the
previous layer's address or selects a predecessor from the previous deduplicated dart set. -/
def molecularFullereneFlagReachableAddress?
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (source target : MolecularFullereneDirectedCarrierEdge input) :
    Nat → Option (List MolecularFullereneFlagMove)
  | 0 => if source = target then some [] else none
  | fuel + 1 =>
      match molecularFullereneFlagReachableAddress? molecule input source target fuel with
      | some moves => some moves
      | none =>
          match molecularFullereneFlagPredecessor? input
              (molecularFullereneFlagReachableEdges molecule input source fuel) target with
          | none => none
          | some predecessor =>
              match molecularFullereneFlagReachableAddress?
                  molecule input source predecessor.2 fuel with
              | none => none
              | some moves => some (moves ++ [predecessor.1])

theorem molecularFullereneFlagReachableAddress?_sound
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (source target : MolecularFullereneDirectedCarrierEdge input) :
    ∀ fuel moves,
      molecularFullereneFlagReachableAddress? molecule input source target fuel = some moves →
        walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
          source moves = target := by
  intro fuel
  induction fuel generalizing target with
  | zero =>
      intro moves computed
      by_cases equal : source = target
      · simp [molecularFullereneFlagReachableAddress?, equal] at computed
        subst moves
        simpa using equal
      · simp [molecularFullereneFlagReachableAddress?, equal] at computed
  | succ fuel inductionHypothesis =>
      intro moves computed
      cases priorEq : molecularFullereneFlagReachableAddress?
          molecule input source target fuel with
      | some priorMoves =>
          simp [molecularFullereneFlagReachableAddress?, priorEq] at computed
          subst moves
          exact inductionHypothesis target priorMoves priorEq
      | none =>
          cases predecessorEq : molecularFullereneFlagPredecessor? input
              (molecularFullereneFlagReachableEdges molecule input source fuel) target with
          | none =>
              simp [molecularFullereneFlagReachableAddress?, priorEq, predecessorEq] at computed
          | some predecessor =>
              cases pathEq : molecularFullereneFlagReachableAddress?
                  molecule input source predecessor.2 fuel with
              | none =>
                  simp [molecularFullereneFlagReachableAddress?, priorEq,
                    predecessorEq, pathEq] at computed
              | some pathPrefix =>
                  simp [molecularFullereneFlagReachableAddress?, priorEq,
                    predecessorEq, pathEq] at computed
                  subst moves
                  rw [walkMolecularFullereneFlag_append,
                    inductionHypothesis predecessor.2 pathPrefix pathEq]
                  exact (molecularFullereneFlagPredecessor?_eq_some_sound
                    input _ target predecessor predecessorEq).2

theorem molecularFullereneFlagReachableAddress?_complete
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneDirectedCarrierEdge input) :
    ∀ fuel target,
      target ∈ molecularFullereneFlagReachableEdges molecule input source fuel →
        ∃ moves,
          molecularFullereneFlagReachableAddress? molecule input source target fuel = some moves := by
  intro fuel
  induction fuel with
  | zero =>
      intro target present
      simp only [molecularFullereneFlagReachableEdges, Finset.mem_singleton] at present
      subst target
      exact ⟨[], by simp [molecularFullereneFlagReachableAddress?]⟩
  | succ fuel inductionHypothesis =>
      intro target present
      simp only [molecularFullereneFlagReachableEdges, Finset.mem_union] at present
      rcases present with previous | generated
      · obtain ⟨moves, computed⟩ := inductionHypothesis target previous
        exact ⟨moves, by simp [molecularFullereneFlagReachableAddress?, computed]⟩
      · have generatedImage := (Finset.mem_filter.mp generated).1
        have predecessorSome := molecularFullereneFlagPredecessor?_isSome_of_mem_image
          input (molecularFullereneFlagReachableEdges molecule input source fuel)
            target generatedImage
        cases predecessorEq : molecularFullereneFlagPredecessor? input
            (molecularFullereneFlagReachableEdges molecule input source fuel) target with
        | none => simp [predecessorEq] at predecessorSome
        | some predecessor =>
            have predecessorPresent :=
              (molecularFullereneFlagPredecessor?_eq_some_sound input _ target predecessor
                predecessorEq).1
            obtain ⟨pathPrefix, pathEq⟩ :=
              inductionHypothesis predecessor.2 predecessorPresent
            by_cases oldComputed : ∃ old,
                molecularFullereneFlagReachableAddress?
                  molecule input source target fuel = some old
            · obtain ⟨old, oldEq⟩ := oldComputed
              exact ⟨old, by simp [molecularFullereneFlagReachableAddress?, oldEq]⟩
            · have oldNone : molecularFullereneFlagReachableAddress?
                  molecule input source target fuel = none := by
                cases oldResult : molecularFullereneFlagReachableAddress?
                    molecule input source target fuel with
                | none => rfl
                | some old => exact False.elim (oldComputed ⟨old, oldResult⟩)
              exact ⟨pathPrefix ++ [predecessor.1], by
                simp [molecularFullereneFlagReachableAddress?, oldNone,
                  predecessorEq, pathEq]⟩

/-- Deterministically choose a reached dart whose first endpoint is `atom`. -/
def molecularFullereneExecutableReachedEdge?
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (source : MolecularFullereneDirectedCarrierEdge input) (fuel : Nat)
    (atom : MolecularFullereneCarrierAtom input) :
    Option (MolecularFullereneDirectedCarrierEdge input) :=
  molecularFullereneSortedDirectedEdges input
    (molecularFullereneFlagReachableEdges molecule input source fuel) |>.find? fun edge =>
    edge.1 = atom

/-- Fully executable source word for one carrier atom, with empty fallback only outside the
proved spanning domain. -/
def molecularFullereneExecutableFlagAddress
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input)
    (atom : MolecularFullereneCarrierAtom input) : List MolecularFullereneFlagMove :=
  let fuel := molecularFullereneFlagStateBound molecule input
  match molecularFullereneExecutableReachedEdge?
      molecule input certificate.source fuel atom with
  | none => []
  | some edge =>
      (molecularFullereneFlagReachableAddress?
        molecule input certificate.source edge fuel).getD []

theorem molecularFullereneExecutableFlagAddress_recovers
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input)
    (atom : MolecularFullereneCarrierAtom input) :
    (walkMolecularFullereneFlag (molecularFullereneContinueForwardFace input)
      certificate.source
      (molecularFullereneExecutableFlagAddress molecule input certificate atom)).1 = atom := by
  let fuel := molecularFullereneFlagStateBound molecule input
  have reachedExists : (molecularFullereneExecutableReachedEdge?
      molecule input certificate.source fuel atom).isSome := by
    rcases certificate.spanning atom with ⟨edge, edgePresent, firstEq⟩
    apply List.find?_isSome.mpr
    exact ⟨edge, by simpa using edgePresent, by simpa using firstEq⟩
  cases edgeEq : molecularFullereneExecutableReachedEdge?
      molecule input certificate.source fuel atom with
  | none => simp [edgeEq] at reachedExists
  | some edge =>
      have edgePresent : edge ∈ molecularFullereneFlagReachableEdges
          molecule input certificate.source fuel := by
        have selected := List.mem_of_find?_eq_some edgeEq
        simpa [molecularFullereneExecutableReachedEdge?] using selected
      have firstEq : edge.1 = atom := by
        exact of_decide_eq_true (List.find?_some
          (p := fun candidate : MolecularFullereneDirectedCarrierEdge input =>
            candidate.1 = atom) (a := edge) edgeEq)
      obtain ⟨moves, movesEq⟩ := molecularFullereneFlagReachableAddress?_complete
        molecule input certificate.source fuel edge edgePresent
      have recovered := molecularFullereneFlagReachableAddress?_sound
        molecule input certificate.source edge fuel moves movesEq
      simp [molecularFullereneExecutableFlagAddress, fuel, edgeEq, movesEq,
        recovered, firstEq]

/-- Materialize every recovered source address once.  The reversing corpus reuses this table for
all proposed image darts instead of repeating the bounded BFS recovery for every candidate. -/
def molecularFullereneExecutableFlagAddressTable
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input) :
    List (MolecularFullereneCarrierAtom input × List MolecularFullereneFlagMove) :=
  (Finset.univ : Finset (MolecularFullereneCarrierAtom input)).sort (· ≤ ·) |>.map
    fun atom => (atom, molecularFullereneExecutableFlagAddress molecule input certificate atom)

/-- Deterministic lookup in the materialized address table. -/
def molecularFullereneExecutableFlagAddressTableLookup
    {input : MolecularFullereneConfigurationInput}
    (table : List (MolecularFullereneCarrierAtom input × List MolecularFullereneFlagMove))
    (atom : MolecularFullereneCarrierAtom input) : List MolecularFullereneFlagMove :=
  (table.find? fun entry => entry.1 = atom).map Prod.snd |>.getD []

@[simp] theorem molecularFullereneExecutableFlagAddressTableLookup_materialized
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input)
    (atom : MolecularFullereneCarrierAtom input) :
    molecularFullereneExecutableFlagAddressTableLookup
        (molecularFullereneExecutableFlagAddressTable molecule input certificate) atom =
      molecularFullereneExecutableFlagAddress molecule input certificate atom := by
  let address := molecularFullereneExecutableFlagAddress molecule input certificate atom
  cases foundEq : ((Finset.univ : Finset (MolecularFullereneCarrierAtom input)).sort
      (· ≤ ·) |>.map fun candidate =>
        (candidate, molecularFullereneExecutableFlagAddress molecule input certificate candidate))
      |>.find? (fun entry => entry.1 = atom) with
  | none =>
      have rejects := List.find?_eq_none.mp foundEq (atom, address) (by simp [address])
      exact False.elim (rejects (by simp))
  | some selected =>
      have selectedPresent := List.mem_of_find?_eq_some foundEq
      rcases List.mem_map.mp selectedPresent with ⟨candidate, _, candidateEq⟩
      have selectedAtom : selected.1 = atom :=
        of_decide_eq_true (List.find?_some
          (p := fun entry : MolecularFullereneCarrierAtom input ×
            List MolecularFullereneFlagMove => entry.1 = atom)
          (a := selected) foundEq)
      subst selected
      have candidateAtom : candidate = atom := by simpa using selectedAtom
      subst candidate
      unfold molecularFullereneExecutableFlagAddressTableLookup
      change ((List.find? (fun entry => decide (entry.1 = atom))
        ((Finset.univ : Finset (MolecularFullereneCarrierAtom input)).sort
          (· ≤ ·) |>.map fun candidate =>
            (candidate, molecularFullereneExecutableFlagAddress molecule input certificate candidate))).map
              Prod.snd).getD [] =
        molecularFullereneExecutableFlagAddress molecule input certificate atom
      rw [foundEq]
      rfl

/-- Executable addresses instantiate the already proved concrete flag-extension interface. -/
def MolecularFullereneDeduplicatedFlagSpanningCertificate.toExecutableConcreteFlagExtension
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input) :
    MolecularFullereneConcreteFlagExtensionCertificate molecule input where
  address :=
    let table := molecularFullereneExecutableFlagAddressTable molecule input certificate
    molecularFullereneExecutableFlagAddressTableLookup table
  oriented := certificate.oriented
  source := certificate.source
  sourceBond := certificate.sourceBond
  recovers := by
    intro atom
    rw [molecularFullereneExecutableFlagAddressTableLookup_materialized]
    exact molecularFullereneExecutableFlagAddress_recovers molecule input certificate atom

/-! ## Executable generated permutations -/

/-- Materialize a finite self-map once.  In the fullerene application this prevents each
injectivity comparison from replaying the same flag address. -/
def molecularFullereneFiniteSelfMapTable
    {Alpha : Type*} [Fintype Alpha] [LinearOrder Alpha]
    (map : Alpha → Alpha) : List (Alpha × Alpha) :=
  (Finset.univ : Finset Alpha).sort (· ≤ ·) |>.map fun source => (source, map source)

/-- Deterministic lookup in a materialized self-map.  The identity fallback is unreachable for
tables produced by `molecularFullereneFiniteSelfMapTable`. -/
def molecularFullereneFiniteSelfMapTableLookup
    {Alpha : Type*} [DecidableEq Alpha]
    (table : List (Alpha × Alpha)) (source : Alpha) : Alpha :=
  (table.find? fun entry => entry.1 = source).map Prod.snd |>.getD source

@[simp] theorem molecularFullereneFiniteSelfMapTableLookup_materialized
    {Alpha : Type*} [Fintype Alpha] [LinearOrder Alpha]
    (map : Alpha → Alpha) (source : Alpha) :
    molecularFullereneFiniteSelfMapTableLookup
        (molecularFullereneFiniteSelfMapTable map) source = map source := by
  have foundSome : (((Finset.univ : Finset Alpha).sort (· ≤ ·) |>.map
      fun candidate => (candidate, map candidate)).find?
        fun entry => entry.1 = source).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨(source, map source), by simp, by simp⟩
  cases foundEq : ((Finset.univ : Finset Alpha).sort (· ≤ ·) |>.map
      fun candidate => (candidate, map candidate)).find?
        (fun entry => entry.1 = source) with
  | none => simp [foundEq] at foundSome
  | some selected =>
      have selectedPresent := List.mem_of_find?_eq_some foundEq
      rcases List.mem_map.mp selectedPresent with ⟨candidate, _, candidateEq⟩
      have selectedSource : selected.1 = source :=
        of_decide_eq_true (List.find?_some
          (p := fun entry : Alpha × Alpha => entry.1 = source)
          (a := selected) foundEq)
      subst selected
      have candidateSource : candidate = source := by simpa using selectedSource
      subst candidate
      simp [molecularFullereneFiniteSelfMapTableLookup,
        molecularFullereneFiniteSelfMapTable, foundEq]

/-- Search the finite domain for a preimage.  This is executable data, not a use of classical
choice.  The fallback is unreachable for a surjective map. -/
def molecularFullereneFiniteSelfMapInverse
    {Alpha : Type*} [Fintype Alpha] [LinearOrder Alpha]
    (map : Alpha → Alpha) (target : Alpha) : Alpha :=
  ((Finset.univ : Finset Alpha).sort (· ≤ ·) |>.find?
    fun source => map source = target).getD target

theorem molecularFullereneFiniteSelfMapInverse_right
    {Alpha : Type*} [Fintype Alpha] [LinearOrder Alpha]
    (map : Alpha → Alpha) (surjective : Function.Surjective map) (target : Alpha) :
    map (molecularFullereneFiniteSelfMapInverse map target) = target := by
  obtain ⟨source, sourceEq⟩ := surjective target
  have foundSome : ((Finset.univ : Finset Alpha).sort (· ≤ ·) |>.find?
      fun candidate => map candidate = target).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨source, by simp, by simpa using sourceEq⟩
  cases foundEq : (Finset.univ : Finset Alpha).sort (· ≤ ·) |>.find?
      (fun candidate => map candidate = target) with
  | none => simp [foundEq] at foundSome
  | some selected =>
      have selectedEq : map selected = target :=
        of_decide_eq_true (List.find?_some
          (p := fun candidate : Alpha => map candidate = target)
          (a := selected) foundEq)
      unfold molecularFullereneFiniteSelfMapInverse
      rw [foundEq]
      exact selectedEq

theorem molecularFullereneFiniteSelfMapInverse_left
    {Alpha : Type*} [Fintype Alpha] [LinearOrder Alpha]
    (map : Alpha → Alpha) (injective : Function.Injective map)
    (surjective : Function.Surjective map) (source : Alpha) :
    molecularFullereneFiniteSelfMapInverse map (map source) = source := by
  apply injective
  exact molecularFullereneFiniteSelfMapInverse_right map surjective (map source)

/-- Quadratic finite check for injectivity of a self-map. -/
def molecularFullereneFiniteSelfMapInjectiveChecked
    {Alpha : Type*} [Fintype Alpha] [LinearOrder Alpha] (map : Alpha → Alpha) : Bool :=
  (Finset.univ : Finset Alpha).sort (· ≤ ·) |>.all fun first =>
    (Finset.univ : Finset Alpha).sort (· ≤ ·) |>.all fun second =>
      decide (map first = map second → first = second)

@[simp] theorem molecularFullereneFiniteSelfMapInjectiveChecked_eq_true_iff
    {Alpha : Type*} [Fintype Alpha] [LinearOrder Alpha] (map : Alpha → Alpha) :
    molecularFullereneFiniteSelfMapInjectiveChecked map = true ↔
      Function.Injective map := by
  simp only [molecularFullereneFiniteSelfMapInjectiveChecked, List.all_eq_true,
    Finset.mem_sort, Finset.mem_univ, decide_eq_true_eq, true_implies,
    Function.Injective]

/-- Build an executable permutation from a successful finite injectivity check.  Both the
forward and inverse functions are explicit finite searches. -/
def molecularFullereneExecutablePermutationOfChecked
    {Alpha : Type*} [Fintype Alpha] [LinearOrder Alpha]
    (map : Alpha → Alpha)
    (checked : molecularFullereneFiniteSelfMapInjectiveChecked map = true) :
    Equiv.Perm Alpha :=
  let injective :=
    (molecularFullereneFiniteSelfMapInjectiveChecked_eq_true_iff map).mp checked
  let surjective := Finite.injective_iff_surjective.mp injective
  { toFun := map
    invFun := molecularFullereneFiniteSelfMapInverse map
    left_inv := molecularFullereneFiniteSelfMapInverse_left map injective surjective
    right_inv := molecularFullereneFiniteSelfMapInverse_right map surjective }

/-- Turn the executable generated vertex map into a permutation exactly when the finite
injectivity check succeeds.  Its forward map contains no classical choice. -/
def molecularFullereneExecutableGeneratedExtension
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneConcreteFlagExtensionCertificate molecule input)
    (target : MolecularFullereneDirectedCarrierEdge input) :
    Equiv.Perm (MolecularFullereneCarrierAtom input) :=
  let propagation := certificate.toReversingPropagation molecule input
  let generated := molecularFullereneGeneratedVertexMap propagation target
  let table := molecularFullereneFiniteSelfMapTable generated
  let materialized := molecularFullereneFiniteSelfMapTableLookup table
  if checked : molecularFullereneFiniteSelfMapInjectiveChecked materialized = true then
    molecularFullereneExecutablePermutationOfChecked materialized checked
  else
    Equiv.refl _

/-- At the image of the source dart, the executable extension is exactly the admissible
orientation-reversing automorphism that supplied that image. -/
theorem molecularFullereneExecutableGeneratedExtension_imageSource
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneConcreteFlagExtensionCertificate molecule input)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (automorphism : MolecularFullereneCarrierAutomorphism molecule input symmetry)
    (reversing : MolecularFullereneFaceOrientationReversing input symmetry) :
    molecularFullereneExecutableGeneratedExtension molecule input certificate
        (mapMolecularFullereneDirectedEdge symmetry certificate.source) = symmetry := by
  let propagation := certificate.toReversingPropagation molecule input
  have generatedEq : molecularFullereneGeneratedVertexMap propagation
        (mapMolecularFullereneDirectedEdge symmetry certificate.source) = symmetry :=
    molecularFullereneGeneratedVertexMap_imageSource propagation symmetry
      ⟨automorphism, reversing⟩
  have checked : molecularFullereneFiniteSelfMapInjectiveChecked
      (molecularFullereneFiniteSelfMapTableLookup
        (molecularFullereneFiniteSelfMapTable
          (molecularFullereneGeneratedVertexMap propagation
            (mapMolecularFullereneDirectedEdge symmetry certificate.source)))) = true := by
    apply (molecularFullereneFiniteSelfMapInjectiveChecked_eq_true_iff _).2
    intro left right equal
    simp only [molecularFullereneFiniteSelfMapTableLookup_materialized] at equal
    rw [generatedEq] at equal
    exact symmetry.injective equal
  unfold molecularFullereneExecutableGeneratedExtension
  simp only [propagation, checked, dite_true,
    molecularFullereneExecutablePermutationOfChecked]
  apply Equiv.ext
  intro atom
  change molecularFullereneFiniteSelfMapTableLookup
      (molecularFullereneFiniteSelfMapTable
        (molecularFullereneGeneratedVertexMap propagation
          (mapMolecularFullereneDirectedEdge symmetry certificate.source))) atom = symmetry atom
  rw [molecularFullereneFiniteSelfMapTableLookup_materialized]
  exact congrFun generatedEq atom

/-! ## Exact executable symmetry predicates -/

/-- Executable universal adjacency check for one candidate carrier permutation. -/
def molecularFullereneCarrierAutomorphismChecked
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) : Bool :=
  (Finset.univ : Finset (MolecularFullereneCarrierAtom input)).sort (· ≤ ·) |>.all fun left =>
    (Finset.univ : Finset (MolecularFullereneCarrierAtom input)).sort (· ≤ ·) |>.all fun right =>
      decide ((0 < molecule.bondOrder left.1 right.1) ↔
        0 < molecule.bondOrder (symmetry left).1 (symmetry right).1)

@[simp] theorem molecularFullereneCarrierAutomorphismChecked_eq_true_iff
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) :
    molecularFullereneCarrierAutomorphismChecked molecule input symmetry = true ↔
      MolecularFullereneCarrierAutomorphism molecule input symmetry := by
  simp [molecularFullereneCarrierAutomorphismChecked,
    MolecularFullereneCarrierAutomorphism]

/-- Executable all-faces/existing-target test for orientation reversal. -/
def molecularFullereneFaceOrientationReversingChecked
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) : Bool :=
  input.faces.all fun face =>
    input.faces.any fun target =>
      decide (List.IsRotated
        (mapMolecularFullereneFace input symmetry face).reverse target)

@[simp] theorem molecularFullereneFaceOrientationReversingChecked_eq_true_iff
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) :
    molecularFullereneFaceOrientationReversingChecked input symmetry = true ↔
      MolecularFullereneFaceOrientationReversing input symmetry := by
  simp [molecularFullereneFaceOrientationReversingChecked,
    MolecularFullereneFaceOrientationReversing]

/-- Exact finite reversing corpus generated from the images of one source dart. -/
def molecularFullereneExecutableReversingAutomorphisms
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input) :
    Finset (Equiv.Perm (MolecularFullereneCarrierAtom input)) :=
  let concrete := certificate.toExecutableConcreteFlagExtension molecule input
  ((molecularFullereneBondedDirectedEdges molecule input).image
      (molecularFullereneExecutableGeneratedExtension molecule input concrete)).filter fun symmetry =>
    molecularFullereneCarrierAutomorphismChecked molecule input symmetry &&
      molecularFullereneFaceOrientationReversingChecked input symmetry

/-- The executable corpus is a complete certificate for the original independent reversing
automorphism relation. -/
def MolecularFullereneDeduplicatedFlagSpanningCertificate.toExecutableReversingCertificate
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input) :
    MolecularFullereneReversingAutomorphismCertificate molecule input where
  members := molecularFullereneExecutableReversingAutomorphisms molecule input certificate
  sound := by
    intro symmetry present
    have filtered := Finset.mem_filter.mp present
    have checks :
        molecularFullereneCarrierAutomorphismChecked molecule input symmetry = true ∧
          molecularFullereneFaceOrientationReversingChecked input symmetry = true := by
      simpa only [Bool.and_eq_true] using filtered.2
    exact ⟨
      (molecularFullereneCarrierAutomorphismChecked_eq_true_iff
        molecule input symmetry).1 checks.1,
      (molecularFullereneFaceOrientationReversingChecked_eq_true_iff
        input symmetry).1 checks.2⟩
  complete := by
    intro symmetry automorphism reversing
    let concrete := certificate.toExecutableConcreteFlagExtension molecule input
    have generated : molecularFullereneExecutableGeneratedExtension molecule input concrete
        (mapMolecularFullereneDirectedEdge symmetry concrete.source) = symmetry :=
      molecularFullereneExecutableGeneratedExtension_imageSource molecule input concrete
        symmetry automorphism reversing
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_image.mpr
      exact ⟨mapMolecularFullereneDirectedEdge symmetry concrete.source,
        by
          simp only [molecularFullereneBondedDirectedEdges, Finset.mem_filter,
            Finset.mem_univ, true_and, decide_eq_true_eq]
          exact (automorphism concrete.source.1 concrete.source.2).mp concrete.sourceBond,
        generated⟩
    · have checks :
          molecularFullereneCarrierAutomorphismChecked molecule input symmetry = true ∧
            molecularFullereneFaceOrientationReversingChecked input symmetry = true :=
        ⟨(molecularFullereneCarrierAutomorphismChecked_eq_true_iff
            molecule input symmetry).2 automorphism,
          (molecularFullereneFaceOrientationReversingChecked_eq_true_iff
            input symmetry).2 reversing⟩
      simpa only [Bool.and_eq_true] using checks

/-- The independent relational chirality judgment is exactly rejection of the executable,
complete reversing corpus. -/
theorem molecularFullereneRelationalChiral_iff_executableFlagSymmetry
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (preserved : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input) :
    MolecularFullereneRelationalChiral molecule input preserved ↔
      OrientedMolecularFullereneFaceMapJudgment molecule input ∧
        ∀ symmetry ∈ molecularFullereneExecutableReversingAutomorphisms
            molecule input certificate,
          ¬preserved symmetry :=
  molecularFullereneRelationalChiral_iff_certificate molecule input preserved
    (certificate.toExecutableReversingCertificate molecule input)

end BlueBookP93.Cyclic
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneExecutableFlagAddress_recovers
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.MolecularFullereneDeduplicatedFlagSpanningCertificate.toExecutableReversingCertificate
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneRelationalChiral_iff_executableFlagSymmetry
