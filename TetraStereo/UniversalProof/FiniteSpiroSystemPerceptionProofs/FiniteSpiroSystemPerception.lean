import TetraStereo.OneCenter.IUPACP93SpiroAuthorityCarrier

set_option autoImplicit false

/-!
# Finite exhaustive spiro-frame perception over the encoded source graph

`IUPACP93SpiroAuthorityCarrier` states `MechanicallyValidFor` as a Prop over a
`P93AuthoritySpiroSystem` whose two ring interiors the caller supplies by hand.  This module removes
that hand supply: it enumerates every candidate frame from the *finite* atom carrier of an
`AuthoritativeChemicalInput` and proves that the computable check lands on `MechanicallyValidFor`
exactly.

What is (and is not) established here:

* The enumeration is exhaustive over the encoded constitution: a candidate is one shared center
  atom plus two ordered, duplicate-free atom lists drawn from `List.range atomCount`.  There is no
  handpicked list, no ring-size cutoff and no ring-basis heuristic; completeness is proved by
  deriving the candidate from the `Nodup`/bounded clauses of `MechanicallyValidFor`
  (`mem_spiroCandidates_of_mechanicallyValid`).
* `spiroMechanicalValidityCheck` is a literal, computable Boolean mirror of the encoded clauses —
  `Nodup`, `P93AuthorityAtomsBounded`, both ring-size lower bounds, and both closed-path
  connectedness clauses over `P93AuthorityBinaryBond`.  Its reflection theorem
  (`spiroMechanicalValidityCheck_eq_true_iff`) is proved by unwinding the two definitions, so no
  opaque checker stands between the Boolean and the Prop.
* Only encoded binary constitution is consumed.  `P93AuthorityMulticenterIncidence` (coordination),
  physical coordination frames, ligand-pattern occurrence ranking, spatial geometry and source
  policy are deliberately *not* touched: mechanical validity is a statement about the encoded
  molecular graph, and the separation theorems below keep it from being read as stereogenicity,
  observation or source approval.
* Scalability is explicit: `List.range atomCount` has `atomCount` entries, so
  `spiroAtomLists` (`sublists` then `permutations`) and hence `spiroCandidates` grow like
  `Θ(atomCount · (#ordered lists)²)`, which has factorial growth in `atomCount`.  The enumeration is
  exact and intended as an authority/completeness boundary, not as a scalable production detector.
  The ordered-list count is Θ(n!), so the raw candidate count is Θ(n · (n!)²); this
  asymptotic description is documentation, not an additional kernel theorem.

Mechanical validity does not exclude chords, cross-edges or additional cycles. Exactness here is
against the existing represented-frame predicate, not independently established chemical source
semantics. Different orders and ring swaps remain distinct frames; no chemical-unit deduplication
or exact-once stereogenic-unit claim is made.
-/

namespace TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs

open TetraStereo.OneCenter

/-! ## A computable mirror of the encoded binary-bond relation -/

/-- Computable form of `P93AuthorityBinaryInteractionKind`.  Multicenter, ionic, metallic,
hydrogen-bond and arbitrary `other` interactions are rejected exactly as the Prop does. -/
def authorityBinaryInteractionKind? : SemanticInteractionKind → Bool
  | .unspecifiedCovalent | .covalent _ | .aromatic | .delocalized _ | .coordinate => true
  | _ => false

@[simp] theorem authorityBinaryInteractionKind?_eq_true_iff
    (kind : SemanticInteractionKind) :
    authorityBinaryInteractionKind? kind = true ↔
      P93AuthorityBinaryInteractionKind kind := by
  cases kind <;> simp [authorityBinaryInteractionKind?, P93AuthorityBinaryInteractionKind]

/-- Executable check for one exact encoded binary bond between two distinct atoms. -/
def authorityBinaryBondCheck
    (source : AuthoritativeChemicalInput) (left right : Nat) : Bool :=
  decide (left ≠ right) &&
    source.molecule.interactions.any (fun interaction =>
      authorityBinaryInteractionKind? interaction.kind &&
        (decide (interaction.participants = [left, right]) ||
          decide (interaction.participants = [right, left])))

theorem authorityBinaryBondCheck_eq_true_iff
    (source : AuthoritativeChemicalInput) (left right : Nat) :
    authorityBinaryBondCheck source left right = true ↔
      P93AuthorityBinaryBond source left right := by
  unfold authorityBinaryBondCheck P93AuthorityBinaryBond
  simp [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    authorityBinaryInteractionKind?_eq_true_iff, and_left_comm, and_comm]

/-- Computable mirror of `P93AuthorityConnectedPath`: a directed walk whose consecutive steps are
encoded binary bonds. -/
def authorityConnectedPathCheck
    (source : AuthoritativeChemicalInput) : List Nat → Bool
  | [] | [_] => true
  | first :: second :: rest =>
      authorityBinaryBondCheck source first second &&
        authorityConnectedPathCheck source (second :: rest)

theorem authorityConnectedPathCheck_eq_true_iff
    (source : AuthoritativeChemicalInput) (path : List Nat) :
    authorityConnectedPathCheck source path = true ↔
      P93AuthorityConnectedPath source path := by
  induction path with
  | nil => simp [authorityConnectedPathCheck, P93AuthorityConnectedPath]
  | cons first tail ih =>
      cases tail with
      | nil => simp [authorityConnectedPathCheck, P93AuthorityConnectedPath]
      | cons second rest =>
          simp [authorityConnectedPathCheck, P93AuthorityConnectedPath,
            authorityBinaryBondCheck_eq_true_iff, ih]

/-- Computable mirror of `P93AuthorityAtomsBounded`. -/
def authorityAtomsBoundedCheck
    (source : AuthoritativeChemicalInput) (atoms : List Nat) : Bool :=
  atoms.all fun atom => decide (atom < source.molecule.atomCount)

theorem authorityAtomsBoundedCheck_eq_true_iff
    (source : AuthoritativeChemicalInput) (atoms : List Nat) :
    authorityAtomsBoundedCheck source atoms = true ↔
      P93AuthorityAtomsBounded source atoms := by
  simp [authorityAtomsBoundedCheck, P93AuthorityAtomsBounded, List.all_eq_true]

/-! ## The exact computable mechanical-validity check -/

/-- Literal Boolean evaluation of every encoded clause of
`P93AuthoritySpiroSystem.MechanicallyValidFor`.  This is a transparent definition, not an opaque
oracle; `spiroMechanicalValidityCheck_eq_true_iff` reflects it back. -/
def spiroMechanicalValidityCheck
    (source : AuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) : Bool :=
  decide system.atoms.Nodup &&
    authorityAtomsBoundedCheck source system.atoms &&
    decide (2 ≤ system.firstRingInternal.length) &&
    decide (2 ≤ system.secondRingInternal.length) &&
    authorityConnectedPathCheck source (system.closedPath system.firstRingInternal) &&
    authorityConnectedPathCheck source (system.closedPath system.secondRingInternal)

/-- Reflection: the executable check is true exactly for the existing mechanical-validity Prop. -/
theorem spiroMechanicalValidityCheck_eq_true_iff
    (source : AuthoritativeChemicalInput) (system : P93AuthoritySpiroSystem) :
    spiroMechanicalValidityCheck source system = true ↔
      system.MechanicallyValidFor source := by
  unfold spiroMechanicalValidityCheck P93AuthoritySpiroSystem.MechanicallyValidFor
  simp [Bool.and_eq_true, decide_eq_true_eq, authorityAtomsBoundedCheck_eq_true_iff,
    authorityConnectedPathCheck_eq_true_iff, and_assoc, and_left_comm, and_comm]

/-! ## Exhaustive candidate enumeration from the finite atom carrier -/

/-- Every source atom, once, in deterministic index order. -/
def spiroAtomUniverse (source : AuthoritativeChemicalInput) : List Nat :=
  List.range source.molecule.atomCount

@[simp] theorem mem_spiroAtomUniverse
    (source : AuthoritativeChemicalInput) (atom : Nat) :
    atom ∈ spiroAtomUniverse source ↔ atom < source.molecule.atomCount :=
  List.mem_range

theorem spiroAtomUniverse_nodup (source : AuthoritativeChemicalInput) :
    (spiroAtomUniverse source).Nodup :=
  List.nodup_range

/-- Every ordered duplicate-free atom list over the finite source carrier: take every sublist of
the universe and every permutation of that sublist.  Factorial in `atomCount`, and exact. -/
def spiroAtomLists (source : AuthoritativeChemicalInput) : List (List Nat) :=
  (spiroAtomUniverse source).sublists.flatMap List.permutations

/-- Extensional exactness of the atom-list enumeration: membership is precisely being
duplicate-free and bounded by the source atom count. -/
theorem mem_spiroAtomLists_iff
    (source : AuthoritativeChemicalInput) (candidate : List Nat) :
    candidate ∈ spiroAtomLists source ↔
      candidate.Nodup ∧ ∀ atom ∈ candidate, atom < source.molecule.atomCount := by
  unfold spiroAtomLists
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨base, baseSublist, candidatePerm⟩
    have baseNodup : base.Nodup :=
      (List.mem_sublists.mp baseSublist).nodup (spiroAtomUniverse_nodup source)
    refine ⟨(List.mem_permutations.mp candidatePerm).symm.nodup baseNodup, ?_⟩
    intro atom atomMem
    have inBase : atom ∈ base :=
      (List.mem_permutations.mp candidatePerm).mem_iff.mp atomMem
    have inUniverse : atom ∈ spiroAtomUniverse source :=
      (List.mem_sublists.mp baseSublist).subset inBase
    exact (mem_spiroAtomUniverse source atom).mp inUniverse
  · rintro ⟨candidateNodup, candidateBounded⟩
    have subset : candidate ⊆ spiroAtomUniverse source :=
      fun atom member => (mem_spiroAtomUniverse source atom).mpr (candidateBounded atom member)
    rcases List.subperm_of_subset candidateNodup subset with
      ⟨base, basePerm, baseSublist⟩
    exact ⟨base, List.mem_sublists.mpr baseSublist,
      List.mem_permutations.mpr basePerm.symm⟩

/-- The exhaustive finite set of candidate spiro frames: one bounded center atom and two ordered
duplicate-free bounded atom lists.  No chemically valid frame is assumed to be present; membership
is what the following theorems derive and characterise. -/
def spiroCandidates (source : AuthoritativeChemicalInput) : List P93AuthoritySpiroSystem :=
  (spiroAtomUniverse source).flatMap fun center =>
    (spiroAtomLists source).flatMap fun first =>
      (spiroAtomLists source).map fun second =>
        (⟨center, first, second⟩ : P93AuthoritySpiroSystem)

/-- Exact membership characterisation of the candidate enumeration: a frame is a candidate exactly
when its center is bounded and each interior is duplicate-free and bounded.  This is a statement
about the encoded graph alone; it says nothing about stereogenicity. -/
theorem mem_spiroCandidates_iff
    (source : AuthoritativeChemicalInput) (system : P93AuthoritySpiroSystem) :
    system ∈ spiroCandidates source ↔
      system.center < source.molecule.atomCount ∧
      system.firstRingInternal.Nodup ∧
      (∀ atom ∈ system.firstRingInternal, atom < source.molecule.atomCount) ∧
      system.secondRingInternal.Nodup ∧
      (∀ atom ∈ system.secondRingInternal, atom < source.molecule.atomCount) := by
  unfold spiroCandidates
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨center, centerMem, first, firstMem, second, secondMem, heq⟩
    rw [← heq]
    dsimp only
    obtain ⟨firstNodup, firstBound⟩ := (mem_spiroAtomLists_iff source first).mp firstMem
    obtain ⟨secondNodup, secondBound⟩ := (mem_spiroAtomLists_iff source second).mp secondMem
    exact ⟨(mem_spiroAtomUniverse source center).mp centerMem,
      firstNodup, firstBound, secondNodup, secondBound⟩
  · rintro ⟨centerBound, firstNodup, firstBound, secondNodup, secondBound⟩
    exact ⟨system.center, (mem_spiroAtomUniverse source system.center).mpr centerBound,
      system.firstRingInternal,
      (mem_spiroAtomLists_iff source system.firstRingInternal).mpr
        ⟨firstNodup, firstBound⟩,
      system.secondRingInternal,
      (mem_spiroAtomLists_iff source system.secondRingInternal).mpr
        ⟨secondNodup, secondBound⟩,
      rfl⟩

/-! ## Exact soundness and completeness against `MechanicallyValidFor`

Completeness is the load-bearing direction: an arbitrary mechanically valid frame is *derived* to
be a candidate, so the enumeration is not a handpicked list that silently omits valid frames. -/

theorem mem_spiroCandidates_of_mechanicallyValid
    (source : AuthoritativeChemicalInput) (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor source) :
    system ∈ spiroCandidates source := by
  rw [mem_spiroCandidates_iff]
  have nodupAtoms : system.atoms.Nodup := valid.1
  have bounded : P93AuthorityAtomsBounded source system.atoms := valid.2.1
  rw [P93AuthoritySpiroSystem.atoms_eq_center_cons_append system] at nodupAtoms
  have appendNodup : (system.firstRingInternal ++ system.secondRingInternal).Nodup :=
    (List.nodup_cons.mp nodupAtoms).2
  refine ⟨bounded system.center
      ((P93AuthoritySpiroSystem.mem_atoms_iff system system.center).mpr (Or.inl rfl)),
    (List.nodup_append.mp appendNodup).1, ?_,
    (List.nodup_append.mp appendNodup).2.1, ?_⟩
  · intro atom atomMem
    exact bounded atom
      ((P93AuthoritySpiroSystem.mem_atoms_iff system atom).mpr (Or.inr (Or.inl atomMem)))
  · intro atom atomMem
    exact bounded atom
      ((P93AuthoritySpiroSystem.mem_atoms_iff system atom).mpr (Or.inr (Or.inr atomMem)))

/-- Soundness: everything the exhaustive enumeration accepts is mechanically valid. -/
theorem spiroCandidates_sound
    (source : AuthoritativeChemicalInput) (system : P93AuthoritySpiroSystem)
    (accepted : system ∈ spiroCandidates source ∧
      spiroMechanicalValidityCheck source system = true) :
    system.MechanicallyValidFor source :=
  (spiroMechanicalValidityCheck_eq_true_iff source system).mp accepted.2

/-- Completeness: every mechanically valid frame is enumerated and passes the check. -/
theorem spiroCandidates_complete
    (source : AuthoritativeChemicalInput) (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor source) :
    system ∈ spiroCandidates source ∧ spiroMechanicalValidityCheck source system = true :=
  ⟨mem_spiroCandidates_of_mechanicallyValid source system valid,
    (spiroMechanicalValidityCheck_eq_true_iff source system).mpr valid⟩

/-- Exact characterisation: the finite enumeration plus the computable check is logically
equivalent to the existing mechanical-validity Prop, with no handpicked candidate list. -/
theorem spiroCandidates_mechanical_exact
    (source : AuthoritativeChemicalInput) (system : P93AuthoritySpiroSystem) :
    system ∈ spiroCandidates source ∧ spiroMechanicalValidityCheck source system = true ↔
      system.MechanicallyValidFor source :=
  ⟨spiroCandidates_sound source system, spiroCandidates_complete source system⟩

/-- Literal finite detector for the represented mechanically valid ring frames. -/
def perceivedSpiroSystems (source : AuthoritativeChemicalInput) : List P93AuthoritySpiroSystem :=
  (spiroCandidates source).filter (spiroMechanicalValidityCheck source)

/-- Every and only mechanically valid represented frame occurs in the detector output. -/
theorem mem_perceivedSpiroSystems_iff
    (source : AuthoritativeChemicalInput) (system : P93AuthoritySpiroSystem) :
    system ∈ perceivedSpiroSystems source ↔ system.MechanicallyValidFor source := by
  simpa only [perceivedSpiroSystems, List.mem_filter] using
    spiroCandidates_mechanical_exact source system

/-! ## Finite bounds derived from unique/bounded atoms -/

/-- Every mechanically valid frame is a frame of bounded, duplicate-free atoms, so its atom list is
no longer than the source atom count. -/
theorem atoms_length_le_atomCount_of_mechanicallyValid
    {source : AuthoritativeChemicalInput} {system : P93AuthoritySpiroSystem}
    (valid : system.MechanicallyValidFor source) :
    system.atoms.length ≤ source.molecule.atomCount := by
  have bounded : P93AuthorityAtomsBounded source system.atoms := valid.2.1
  have subset : system.atoms.toFinset ⊆ Finset.range source.molecule.atomCount := by
    intro atom member
    rw [Finset.mem_range]
    exact bounded atom (by simpa using member)
  calc
    system.atoms.length = system.atoms.toFinset.card :=
      (List.toFinset_card_of_nodup valid.1).symm
    _ ≤ (Finset.range source.molecule.atomCount).card := Finset.card_le_card subset
    _ = source.molecule.atomCount := Finset.card_range _

/-- A spiro frame needs one shared atom plus two distinct ring interiors of length at least two, so
any mechanically valid frame forces the source to contain at least five atoms. -/
theorem atomCount_ge_five_of_mechanicallyValid
    {source : AuthoritativeChemicalInput} {system : P93AuthoritySpiroSystem}
    (valid : system.MechanicallyValidFor source) :
    5 ≤ source.molecule.atomCount := by
  have lengthLower : 5 ≤ system.atoms.length := by
    simp only [P93AuthoritySpiroSystem.atoms, List.length_cons, List.length_append]
    have firstLength : 2 ≤ system.firstRingInternal.length := valid.2.2.1
    have secondLength : 2 ≤ system.secondRingInternal.length := valid.2.2.2.1
    omega
  exact le_trans lengthLower (atoms_length_le_atomCount_of_mechanicallyValid valid)

/-- The same minimum bound read off the executable check alone. -/
theorem atomCount_ge_five_of_check
    (source : AuthoritativeChemicalInput) (system : P93AuthoritySpiroSystem)
    (accepted : spiroMechanicalValidityCheck source system = true) :
    5 ≤ source.molecule.atomCount :=
  atomCount_ge_five_of_mechanicallyValid
    ((spiroMechanicalValidityCheck_eq_true_iff source system).mp accepted)

/-! ## Regression: a proper spiro versus two rings sharing an extra interior atom

The carrier's `not_mechanicallyValid_of_shared_internal` rejects a skeleton whose two named rings
share a non-center atom.  Its computable counterpart below shows the distinction survives the
executable check, *while both skeletons remain enumerated candidates*: candidate membership comes
from boundedness, validity from the check. -/

theorem spiroMechanicalValidityCheck_eq_false_of_sharedInternal
    (source : AuthoritativeChemicalInput) (system : P93AuthoritySpiroSystem)
    (shared : ∃ atom, atom ∈ system.firstRingInternal ∧
      atom ∈ system.secondRingInternal) :
    spiroMechanicalValidityCheck source system = false := by
  cases h : spiroMechanicalValidityCheck source system with
  | false => rfl
  | true =>
      exact False.elim
        ((P93AuthoritySpiroSystem.not_mechanicallyValid_of_shared_internal
            (source := source) shared)
          ((spiroMechanicalValidityCheck_eq_true_iff source system).mp h))

/-- A fused-like skeleton with bounded, duplicate-free interiors is still enumerated as a
candidate; the accompanying check-rejection theorem
(`spiroMechanicalValidityCheck_eq_false_of_sharedInternal`) is what excludes overlapping interiors,
so candidate membership alone never confers validity. -/
theorem fusedLike_candidate_still_enumerated
    (source : AuthoritativeChemicalInput) (system : P93AuthoritySpiroSystem)
    (centerBound : system.center < source.molecule.atomCount)
    (firstNodup : system.firstRingInternal.Nodup)
    (firstBound : ∀ atom ∈ system.firstRingInternal, atom < source.molecule.atomCount)
    (secondNodup : system.secondRingInternal.Nodup)
    (secondBound : ∀ atom ∈ system.secondRingInternal, atom < source.molecule.atomCount) :
    system ∈ spiroCandidates source :=
  (mem_spiroCandidates_iff source system).mpr
    ⟨centerBound, firstNodup, firstBound, secondNodup, secondBound⟩

/-! ## Separation from observation, ligand pattern, coordination and source policy

The enumeration decides encoded-graph validity only.  The policy's `SystemObserved`,
`SpiroPatternObserved`, `CitationAuthorized`, the coordination relation
`P93AuthorityMulticenterIncidence`, and spatial geometry remain independent, still-required
hypotheses: no clause below is replaced by `True`. -/

/-- Under an explicit absent-observation hypothesis, mechanical validity does not imply
policy-valid status. This conditional separation does not construct an unobserved system. -/
theorem mechanicalValid_not_authorityValid_without_observation
    (policy : P93SpiroAuthorityPolicy) (source : AuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (mechanical : system.MechanicallyValidFor source)
    (unobserved : ¬ policy.SystemObserved source system) :
    system.MechanicallyValidFor source ∧ ¬ system.ValidFor policy source :=
  ⟨mechanical, fun valid => unobserved valid.2⟩

/-- Any policy-valid system still carries the source observation as part of its meaning; mechanical
perception cannot conjure it. -/
theorem authorityValid_implies_systemObserved
    (policy : P93SpiroAuthorityPolicy) (source : AuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.ValidFor policy source) :
    policy.SystemObserved source system :=
  valid.2

/-- A valid `Xabcd` authority observation separately requires the ligand-pattern observation, the
family support and the audited descriptor relation; the mechanical layer supplies none of them. -/
theorem xabcdValid_implies_systemObserved
    {policy : P93SpiroAuthorityPolicy} {source : AuthoritativeChemicalInput}
    {observation : P93SpiroXabcdAuthorityObservation policy}
    (valid : observation.ValidFor policy source) :
    policy.SystemObserved source observation.system :=
  valid.1.2

end TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs

assert_kernel_only
  TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.authorityBinaryInteractionKind?_eq_true_iff
assert_kernel_only
  TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.authorityBinaryBondCheck_eq_true_iff
assert_kernel_only
  TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.authorityConnectedPathCheck_eq_true_iff
assert_kernel_only
  TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.authorityAtomsBoundedCheck_eq_true_iff
assert_kernel_only
  TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.spiroMechanicalValidityCheck_eq_true_iff
assert_kernel_only
  TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.mem_spiroAtomLists_iff
assert_kernel_only
  TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.mem_spiroCandidates_iff
assert_kernel_only
  TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.mem_spiroCandidates_of_mechanicallyValid
assert_kernel_only
  TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.spiroCandidates_mechanical_exact
assert_kernel_only
  TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.atoms_length_le_atomCount_of_mechanicallyValid
assert_kernel_only
  TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.atomCount_ge_five_of_mechanicallyValid
assert_kernel_only
  TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.spiroMechanicalValidityCheck_eq_false_of_sharedInternal
assert_kernel_only
  TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.mechanicalValid_not_authorityValid_without_observation

assert_kernel_only TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.mem_perceivedSpiroSystems_iff
