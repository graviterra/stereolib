import TetraStereo.OneCenter.AuthoritativeSemanticMancudeDigraphNormalization
import TetraStereo.OneCenter.AuthoritativeLocalizedTetrahedralDescriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# End-to-end descriptor invariance for canonical mancude digraphs

The source-normalized mancude topology already makes recursively compiled Rules-1a--2 keys
independent of the selected exact Kekule realization.  This module carries that equality through
safe comparison, the explicit Rules-3--5 context boundary, four-ligand ordering, coordinate
lookup, and the final exact rational tetrahedral descriptor.

The functions below deliberately take the center, four ligand roots, later-rule contexts, and
points at the source level.  None of those data changes with a Kekule realization.  The selection
is allowed to influence only the localized graph and its exact Rule-1a observation; the proofs
show that the canonical compiler removes even that apparent dependence.
-/

namespace SemanticMolecule

/-- Executable exact constitutional key for one ligand, using the source-normalized mancude
topology rather than the written single/double placement of the selected Kekule realization. -/
def buildAromaticCanonicalObservedKey (source : SemanticMolecule)
    (selection : List (Nat × Nat)) (fuel : Nat)
    (center ligand : Fin (source.withAromaticKekuleSelection selection).atomCount) :
    Option (ExactOfficialRuleMajorKey
      (Fin (source.withAromaticKekuleSelection selection).atomCount)) :=
  ((source.withAromaticKekuleSelection selection).toLocalizedMoleculeGraph
    ).buildObservedExactOfficialRuleMajorKey
      (source.withAromaticKekuleSelection selection
        ).semanticExactOfficialRule1aObservation
      (source.aromaticCanonicalOfficialCIPChildrenAt
        (source.withAromaticKekuleSelection selection).atomCount)
      fuel (OfficialCIPNode.rootFromEdge center ligand)

/-- The executable canonical ligand key is independent of an arbitrary valid Kekule choice. -/
theorem buildAromaticCanonicalObservedKey_kekule_invariant
    (source : SemanticMolecule)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection leftSelection))
    (rightExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection rightSelection))
    (fuel : Nat)
    (center ligand :
      Fin (source.withAromaticKekuleSelection leftSelection).atomCount) :
    source.buildAromaticCanonicalObservedKey leftSelection fuel center ligand =
      source.buildAromaticCanonicalObservedKey rightSelection fuel center ligand := by
  exact source.buildObservedExactOfficialRuleMajorKey_aromaticCanonical_kekule_invariant
    leftSelection rightSelection leftExact rightExact fuel
      (OfficialCIPNode.rootFromEdge center ligand)

/-- At the finite default depth, canonical key construction succeeds with a complete key.  Thus
the choice-independence theorem cannot be vacuously explained by both sides running out of fuel. -/
theorem buildAromaticCanonicalObservedKey_complete_default
    (source : SemanticMolecule) (selection : List (Nat × Nat))
    {center ligand : Fin (source.withAromaticKekuleSelection selection).atomCount}
    (different : ligand ≠ center) :
    ∃ key,
      source.buildAromaticCanonicalObservedKey selection (source.atomCount + 1)
          center ligand = some key ∧
        key.complete = true := by
  have expansionComplete :
      MoleculeGraph.OfficialExpansionCompleteWithin
        (source.aromaticCanonicalOfficialCIPChildrenAt
          (source.withAromaticKekuleSelection selection).atomCount)
        (source.atomCount + 1) (OfficialCIPNode.rootFromEdge center ligand) := by
    simpa only [source.withAromaticKekuleSelection_atomCount] using
      source.aromaticCanonicalExpansionCompleteWithin_rootFromEdgeAt_default
        (source.withAromaticKekuleSelection selection).atomCount different
  obtain ⟨key, exactComputed, keyComplete⟩ :=
    ((source.withAromaticKekuleSelection selection).toLocalizedMoleculeGraph
      ).buildExactOfficialRuleMajorKey_complete_of_expansionCompleteWithin
      (source.aromaticCanonicalOfficialCIPChildrenAt
        (source.withAromaticKekuleSelection selection).atomCount)
      (source.atomCount + 1) (OfficialCIPNode.rootFromEdge center ligand) expansionComplete
  refine ⟨key, ?_, keyComplete⟩
  unfold buildAromaticCanonicalObservedKey
  rw [((source.withAromaticKekuleSelection selection).toLocalizedMoleculeGraph
      ).buildObservedExactOfficialRuleMajorKey_eq_exact
    (source.withAromaticKekuleSelection selection).semanticExactOfficialRule1aObservation
    (source.withAromaticKekuleSelection selection
      ).semanticExactOfficialRule1aObservation_eq_independent]
  exact exactComputed

/-- Safe comparison of two common exact keys is independent of the localized realization used
to read their Rules-1a--2 observations. -/
theorem compareObserved?_withAromaticKekuleSelection_invariant
    (source : SemanticMolecule)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection leftSelection))
    (rightExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection rightSelection))
    (first second : ExactOfficialRuleMajorKey
      (Fin (source.withAromaticKekuleSelection leftSelection).atomCount)) :
    ExactOfficialRuleMajorKey.compareObserved?
        (source.withAromaticKekuleSelection leftSelection).toLocalizedMoleculeGraph
        (source.withAromaticKekuleSelection leftSelection
          ).semanticExactOfficialRule1aObservation first second =
      ExactOfficialRuleMajorKey.compareObserved?
        (source.withAromaticKekuleSelection rightSelection).toLocalizedMoleculeGraph
        (source.withAromaticKekuleSelection rightSelection
          ).semanticExactOfficialRule1aObservation first second := by
  rw [ExactOfficialRuleMajorKey.compareObserved?_eq_exact
      (source.withAromaticKekuleSelection leftSelection).toLocalizedMoleculeGraph
      (source.withAromaticKekuleSelection leftSelection
        ).semanticExactOfficialRule1aObservation
      (source.withAromaticKekuleSelection leftSelection
        ).semanticExactOfficialRule1aObservation_eq_independent,
    ExactOfficialRuleMajorKey.compareObserved?_eq_exact
      (source.withAromaticKekuleSelection rightSelection).toLocalizedMoleculeGraph
      (source.withAromaticKekuleSelection rightSelection
        ).semanticExactOfficialRule1aObservation
      (source.withAromaticKekuleSelection rightSelection
        ).semanticExactOfficialRule1aObservation_eq_independent]
  exact (source.graphObservationEquivalent_withAromaticKekuleSelection
    leftSelection rightSelection leftExact rightExact).compare? first second

/-- The complete rule-tagged constitutional trace is likewise realization-independent. -/
theorem compareTraceObserved_withAromaticKekuleSelection_invariant
    (source : SemanticMolecule)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection leftSelection))
    (rightExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection rightSelection))
    (first second : ExactOfficialRuleMajorKey
      (Fin (source.withAromaticKekuleSelection leftSelection).atomCount)) :
    ExactOfficialRuleMajorKey.compareTraceObserved
        (source.withAromaticKekuleSelection leftSelection).toLocalizedMoleculeGraph
        (source.withAromaticKekuleSelection leftSelection
          ).semanticExactOfficialRule1aObservation first second =
      ExactOfficialRuleMajorKey.compareTraceObserved
        (source.withAromaticKekuleSelection rightSelection).toLocalizedMoleculeGraph
        (source.withAromaticKekuleSelection rightSelection
          ).semanticExactOfficialRule1aObservation first second := by
  rw [ExactOfficialRuleMajorKey.compareTraceObserved_eq_exact
      (source.withAromaticKekuleSelection leftSelection).toLocalizedMoleculeGraph
      (source.withAromaticKekuleSelection leftSelection
        ).semanticExactOfficialRule1aObservation
      (source.withAromaticKekuleSelection leftSelection
        ).semanticExactOfficialRule1aObservation_eq_independent,
    ExactOfficialRuleMajorKey.compareTraceObserved_eq_exact
      (source.withAromaticKekuleSelection rightSelection).toLocalizedMoleculeGraph
      (source.withAromaticKekuleSelection rightSelection
        ).semanticExactOfficialRule1aObservation
      (source.withAromaticKekuleSelection rightSelection
        ).semanticExactOfficialRule1aObservation_eq_independent]
  exact (source.graphObservationEquivalent_withAromaticKekuleSelection
    leftSelection rightSelection leftExact rightExact).compareTrace first second

/-- Compare two already-built canonical keys and retain the exact rule-tagged trace. -/
def compareAromaticCanonicalKeys? (source : SemanticMolecule)
    (selection : List (Nat × Nat))
    (first second : ExactOfficialRuleMajorKey
      (Fin (source.withAromaticKekuleSelection selection).atomCount)) :
    Option CIPTraceCertificate :=
  let candidate := source.withAromaticKekuleSelection selection
  match ExactOfficialRuleMajorKey.compareObserved? candidate.toLocalizedMoleculeGraph
      candidate.semanticExactOfficialRule1aObservation first second with
  | none => none
  | some _ => some (CIPTraceCertificate.ofTrace
      (ExactOfficialRuleMajorKey.compareTraceObserved candidate.toLocalizedMoleculeGraph
        candidate.semanticExactOfficialRule1aObservation first second))

/-- Safe key-to-certificate interpretation is independent of the exact Kekule realization. -/
theorem compareAromaticCanonicalKeys?_kekule_invariant
    (source : SemanticMolecule)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection leftSelection))
    (rightExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection rightSelection))
    (first second : ExactOfficialRuleMajorKey
      (Fin (source.withAromaticKekuleSelection leftSelection).atomCount)) :
    source.compareAromaticCanonicalKeys? leftSelection first second =
      source.compareAromaticCanonicalKeys? rightSelection first second := by
  unfold compareAromaticCanonicalKeys?
  dsimp only
  rw [source.compareObserved?_withAromaticKekuleSelection_invariant
      leftSelection rightSelection leftExact rightExact first second,
    source.compareTraceObserved_withAromaticKekuleSelection_invariant
      leftSelection rightSelection leftExact rightExact first second]

/-- Proof-carrying constitutional comparison on the canonical mancude digraph.  As in the main
safe analyzer, incomplete equal-prefix keys are refused instead of being guessed. -/
def compareAromaticCanonicalConstitution? (source : SemanticMolecule)
    (selection : List (Nat × Nat)) (fuel : Nat)
    (center : Fin (source.withAromaticKekuleSelection selection).atomCount)
    (ligand : Fin 4 → Fin (source.withAromaticKekuleSelection selection).atomCount)
    (left right : Fin 4) : Option CIPTraceCertificate :=
  match source.buildAromaticCanonicalObservedKey selection fuel center (ligand left),
      source.buildAromaticCanonicalObservedKey selection fuel center (ligand right) with
  | some leftKey, some rightKey =>
      source.compareAromaticCanonicalKeys? selection leftKey rightKey
  | _, _ => none

/-- The complete proof-carrying constitutional result is exactly independent of Kekule choice. -/
theorem compareAromaticCanonicalConstitution?_kekule_invariant
    (source : SemanticMolecule)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection leftSelection))
    (rightExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection rightSelection))
    (fuel : Nat)
    (center : Fin (source.withAromaticKekuleSelection leftSelection).atomCount)
    (ligand : Fin 4 →
      Fin (source.withAromaticKekuleSelection leftSelection).atomCount)
    (left right : Fin 4) :
    source.compareAromaticCanonicalConstitution? leftSelection fuel center ligand left right =
      source.compareAromaticCanonicalConstitution? rightSelection fuel center ligand left right := by
  unfold compareAromaticCanonicalConstitution?
  rw [source.buildAromaticCanonicalObservedKey_kekule_invariant
      leftSelection rightSelection leftExact rightExact fuel center (ligand left),
    source.buildAromaticCanonicalObservedKey_kekule_invariant
      leftSelection rightSelection leftExact rightExact fuel center (ligand right)]
  cases leftComputed : source.buildAromaticCanonicalObservedKey
      rightSelection fuel center (ligand left) with
  | none => rfl
  | some leftKey =>
      cases rightComputed : source.buildAromaticCanonicalObservedKey
          rightSelection fuel center (ligand right) with
      | none => rfl
      | some rightKey =>
          exact source.compareAromaticCanonicalKeys?_kekule_invariant
            leftSelection rightSelection leftExact rightExact leftKey rightKey

/-- At default fuel, constitutional comparison of any two genuine center ligands always returns a
certificate; only chemical ties and later geometry/context checks may still refuse a descriptor. -/
theorem compareAromaticCanonicalConstitution?_isSome_default
    (source : SemanticMolecule) (selection : List (Nat × Nat))
    (center : Fin (source.withAromaticKekuleSelection selection).atomCount)
    (ligand : Fin 4 → Fin (source.withAromaticKekuleSelection selection).atomCount)
    (ligandDifferent : ∀ index, ligand index ≠ center) (left right : Fin 4) :
    (source.compareAromaticCanonicalConstitution? selection (source.atomCount + 1)
      center ligand left right).isSome = true := by
  obtain ⟨leftKey, leftComputed, leftComplete⟩ :=
    source.buildAromaticCanonicalObservedKey_complete_default selection
      (ligandDifferent left)
  obtain ⟨rightKey, rightComputed, rightComplete⟩ :=
    source.buildAromaticCanonicalObservedKey_complete_default selection
      (ligandDifferent right)
  let candidate := source.withAromaticKekuleSelection selection
  have exactComparisonExists := ExactOfficialRuleMajorKey.compare?_isSome_of_complete
    candidate.toLocalizedMoleculeGraph leftKey rightKey leftComplete rightComplete
  have observedComparisonExists :
      (ExactOfficialRuleMajorKey.compareObserved? candidate.toLocalizedMoleculeGraph
        candidate.semanticExactOfficialRule1aObservation leftKey rightKey).isSome = true := by
    rw [ExactOfficialRuleMajorKey.compareObserved?_eq_exact
      candidate.toLocalizedMoleculeGraph candidate.semanticExactOfficialRule1aObservation
      candidate.semanticExactOfficialRule1aObservation_eq_independent]
    exact exactComparisonExists
  obtain ⟨outcome, comparisonComputed⟩ := Option.isSome_iff_exists.mp observedComparisonExists
  dsimp only [candidate] at comparisonComputed
  unfold compareAromaticCanonicalConstitution? compareAromaticCanonicalKeys?
  rw [leftComputed, rightComputed]
  dsimp only
  rw [comparisonComputed]
  rfl

/-- Canonical constitutional comparison followed by the already proved Rules-3--5 context
semantics.  The context is source/perception evidence and is therefore deliberately not recomputed
from an arbitrary written Kekule form here. -/
def compareAromaticCanonical? (source : SemanticMolecule)
    (selection : List (Nat × Nat)) (fuel : Nat)
    (center : Fin (source.withAromaticKekuleSelection selection).atomCount)
    (ligand : Fin 4 → Fin (source.withAromaticKekuleSelection selection).atomCount)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (left right : Fin 4) : Option CIPTraceCertificate := do
  let constitutional ←
    source.compareAromaticCanonicalConstitution? selection fuel center ligand left right
  some (CIPRuleEngine.compareDigraphThenOfficialCertificate constitutional.trace
    (context left) (context right))

/-- Appending fixed, independently perceived Rules-3--5 contexts preserves exact Kekule-choice
independence of every proof-carrying pairwise comparison. -/
theorem compareAromaticCanonical?_kekule_invariant
    (source : SemanticMolecule)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection leftSelection))
    (rightExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection rightSelection))
    (fuel : Nat)
    (center : Fin (source.withAromaticKekuleSelection leftSelection).atomCount)
    (ligand : Fin 4 →
      Fin (source.withAromaticKekuleSelection leftSelection).atomCount)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (left right : Fin 4) :
    source.compareAromaticCanonical? leftSelection fuel center ligand context left right =
      source.compareAromaticCanonical? rightSelection fuel center ligand context left right := by
  unfold compareAromaticCanonical?
  rw [source.compareAromaticCanonicalConstitution?_kekule_invariant
    leftSelection rightSelection leftExact rightExact fuel center ligand left right]

/-- Pointwise form used by every downstream four-ligand combinator. -/
theorem compareAromaticCanonical_function_kekule_invariant
    (source : SemanticMolecule)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection leftSelection))
    (rightExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection rightSelection))
    (fuel : Nat)
    (center : Fin (source.withAromaticKekuleSelection leftSelection).atomCount)
    (ligand : Fin 4 →
      Fin (source.withAromaticKekuleSelection leftSelection).atomCount)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    source.compareAromaticCanonical? leftSelection fuel center ligand context =
      source.compareAromaticCanonical? rightSelection fuel center ligand context := by
  funext left right
  exact source.compareAromaticCanonical?_kekule_invariant
    leftSelection rightSelection leftExact rightExact fuel center ligand context left right

end SemanticMolecule

namespace CanonicalMancudeTetrahedral

/-- A fully proof-carrying pairwise comparison oracle for four ligands. -/
abbrev Comparison := Fin 4 → Fin 4 → Option CIPTraceCertificate

/-- Stable descending-order predicate, matching the main localized rule-major analyzer. -/
def ligandBefore (compare : Comparison) (left right : Fin 4) : Bool :=
  match compare left right with
  | none => decide (left ≤ right)
  | some certificate =>
      match certificate.outcome with
      | .gt => true
      | .lt => false
      | .eq => decide (left ≤ right)

def ligandOrder (compare : Comparison) : List (Fin 4) :=
  (List.finRange 4).mergeSort (ligandBefore compare)

/-- A strict pair must have a successful `gt` certificate. -/
def pairStrict (compare : Comparison) (left right : Fin 4) : Bool :=
  match compare left right with
  | some certificate => certificate.outcome == Ordering.gt
  | none => false

@[simp] theorem pairStrict_eq_true_iff (compare : Comparison) (left right : Fin 4) :
    pairStrict compare left right = true ↔
      ∃ certificate, compare left right = some certificate ∧
        certificate.outcome = Ordering.gt := by
  cases computed : compare left right with
  | none => simp [pairStrict, computed]
  | some certificate => simp [pairStrict, computed]

/-- Check all earlier/later pairs, preventing a cyclic tournament from being emitted as an order. -/
def coherentList (compare : Comparison) : List (Fin 4) → Bool
  | [] => true
  | left :: rest => rest.all (pairStrict compare left) && coherentList compare rest

@[simp] theorem coherentList_eq_true_iff (compare : Comparison) :
    ∀ order : List (Fin 4),
      coherentList compare order = true ↔
        order.Pairwise fun left right =>
          ∃ certificate, compare left right = some certificate ∧
            certificate.outcome = Ordering.gt
  | [] => by simp [coherentList]
  | left :: rest => by
      rw [coherentList, Bool.and_eq_true, List.all_eq_true, List.pairwise_cons,
        coherentList_eq_true_iff]
      constructor
      · rintro ⟨head, tail⟩
        exact ⟨fun right present =>
          (pairStrict_eq_true_iff compare left right).mp (head right present), tail⟩
      · rintro ⟨head, tail⟩
        exact ⟨fun right present =>
          (pairStrict_eq_true_iff compare left right).mpr (head right present), tail⟩

def coherent (compare : Comparison) : Bool :=
  coherentList compare (ligandOrder compare)

/-- Every distinct ligand pair must compare successfully and decisively. -/
def resolved (compare : Comparison) : Bool :=
  (List.finRange 4).all fun left =>
    (List.finRange 4).all fun right =>
      decide (left = right) ||
        match compare left right with
        | some certificate => certificate.outcome != Ordering.eq
        | none => false

/-- Tie-, failure-, and cycle-refusing priority order. -/
def safeLigandOrder? (compare : Comparison) : Option (List (Fin 4)) :=
  if resolved compare && coherent compare then some (ligandOrder compare) else none

/-- A successful safe order contains each of the four ligand positions exactly once and every
earlier/later pair carries a strict proof-producing comparison certificate. -/
theorem safeLigandOrder?_sound (compare : Comparison) (order : List (Fin 4))
    (computed : safeLigandOrder? compare = some order) :
    order.Perm (List.finRange 4) ∧
      order.Pairwise fun left right =>
        ∃ certificate, compare left right = some certificate ∧
          certificate.outcome = Ordering.gt := by
  unfold safeLigandOrder? at computed
  split at computed
  · rename_i accepted
    have orderIdentity : ligandOrder compare = order := Option.some.inj computed
    subst order
    constructor
    · exact List.mergeSort_perm _ _
    · have acceptedParts : resolved compare = true ∧ coherent compare = true := by
        simpa only [Bool.and_eq_true] using accepted
      have coherentAccepted : coherent compare = true := acceptedParts.2
      exact (coherentList_eq_true_iff compare (ligandOrder compare)).mp coherentAccepted
  · contradiction

/-- Independent meaning of a final canonical tetrahedral result.  It mentions only a permutation
of the four ligand positions, strict comparison certificates for all earlier/later pairs, direct
point observations, and the exact rational handedness relation. -/
def DeclarativeSpatialDescriptor (compare : Comparison)
    (point : Fin 4 → Option CartesianPoint3) (descriptor : RS) : Prop :=
  ∃ order points,
    order.Perm (List.finRange 4) ∧
      (order.Pairwise fun left right =>
        ∃ certificate, compare left right = some certificate ∧
          certificate.outcome = Ordering.gt) ∧
      List.Forall₂ (fun index observed => point index = some observed) order points ∧
      CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor points descriptor

private theorem mapM_point_forall₂ (point : Fin 4 → Option CartesianPoint3) :
    ∀ (order : List (Fin 4)) (points : List CartesianPoint3),
      order.mapM point = some points →
        List.Forall₂ (fun index observed => point index = some observed) order points
  | [], points, computed => by
      simp at computed
      subst points
      exact .nil
  | index :: order, points, computed => by
      rw [List.mapM_cons] at computed
      cases pointComputed : point index with
      | none => simp [pointComputed] at computed
      | some observed =>
          cases restComputed : order.mapM point with
          | none => simp [pointComputed, restComputed] at computed
          | some rest =>
              simp [pointComputed, restComputed] at computed
              subst points
              exact .cons pointComputed (mapM_point_forall₂ point order rest restComputed)

/-- Exact spatial descriptor from a source-fixed point lookup and the safe canonical order. -/
def spatialDescriptor? (compare : Comparison)
    (point : Fin 4 → Option CartesianPoint3) : Option RS := do
  let order ← safeLigandOrder? compare
  let points ← order.mapM point
  CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? points

/-- Every emitted canonical descriptor satisfies the independent strict-priority and exact
geometry relation. -/
theorem spatialDescriptor?_sound (compare : Comparison)
    (point : Fin 4 → Option CartesianPoint3) (descriptor : RS)
    (computed : spatialDescriptor? compare point = some descriptor) :
    DeclarativeSpatialDescriptor compare point descriptor := by
  unfold spatialDescriptor? at computed
  cases orderComputed : safeLigandOrder? compare with
  | none => simp [orderComputed] at computed
  | some order =>
      cases pointsComputed : order.mapM point with
      | none => simp [orderComputed, pointsComputed] at computed
      | some points =>
          have geometry :=
            (CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?_eq_some_iff
              points descriptor).mp (by simpa [orderComputed, pointsComputed] using computed)
          have orderSound := safeLigandOrder?_sound compare order orderComputed
          exact ⟨order, points, orderSound.1, orderSound.2,
            mapM_point_forall₂ point order points pointsComputed, geometry⟩

end CanonicalMancudeTetrahedral

namespace SemanticMolecule

/-- Selection-parametric final tetrahedral descriptor on the canonical mancude route. -/
def aromaticCanonicalTetrahedralDescriptor? (source : SemanticMolecule)
    (selection : List (Nat × Nat)) (fuel : Nat)
    (center : Fin (source.withAromaticKekuleSelection selection).atomCount)
    (ligand : Fin 4 → Fin (source.withAromaticKekuleSelection selection).atomCount)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (point : Fin 4 → Option CartesianPoint3) : Option RS :=
  CanonicalMancudeTetrahedral.spatialDescriptor?
    (source.compareAromaticCanonical? selection fuel center ligand context) point

/-- End-to-end theorem: for arbitrary two exact Kekule realizations, every pairwise certificate,
safe priority decision, coordinate sequence, and final emitted `R/S` descriptor is identical.
This is equality of the executable `Option RS`, so it covers success with either descriptor and
all principled refusal cases. -/
theorem aromaticCanonicalTetrahedralDescriptor?_kekule_invariant
    (source : SemanticMolecule)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection leftSelection))
    (rightExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection rightSelection))
    (fuel : Nat)
    (center : Fin (source.withAromaticKekuleSelection leftSelection).atomCount)
    (ligand : Fin 4 →
      Fin (source.withAromaticKekuleSelection leftSelection).atomCount)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (point : Fin 4 → Option CartesianPoint3) :
    source.aromaticCanonicalTetrahedralDescriptor?
        leftSelection fuel center ligand context point =
      source.aromaticCanonicalTetrahedralDescriptor?
        rightSelection fuel center ligand context point := by
  unfold aromaticCanonicalTetrahedralDescriptor?
  rw [source.compareAromaticCanonical_function_kekule_invariant
    leftSelection rightSelection leftExact rightExact fuel center ligand context]

end SemanticMolecule

end TetraStereo.OneCenter
