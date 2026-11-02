import TetraStereo.OneCenter.AuthoritativeLocalizedApplicability
import TetraStereo.OneCenter.DeclarativeCIPRule1aExact
import TetraStereo.OneCenter.ProductionCIPRule1aMatchingRealization
import TetraStereo.OneCenter.ProductionCIPReachability
import TetraStereo.OneCenter.ProductionCIPReachabilityBound
import TetraStereo.OneCenter.SemanticLocalizedMancudeFiniteRealization

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open RawMolecule

/-!
# All-element semantic aromatic/Kekule normalization

This module lifts the complete finite aromatic normalization boundary from parser-shaped raw
molecules to `SemanticMolecule`, whose element vocabulary covers all 118 named elements.  Every
subset of declared aromatic pair edges is generated.  A candidate is accepted only when it enters
the exact localized CIP graph, every declared aromatic edge belongs to the bridge-free localized
mancude graph, and the written double bonds form a maximum matching in every component.

The construction is finite and exhaustive; it has no ring-size, element-vocabulary, or search-fuel
cap.  Interactions that are not aromatic pairs are preserved.  Consequently delocalized,
coordinate, multicentre, radical, missing-mass, duplicate-pair, and otherwise unsupported data
remain visible and fail the downstream graph-readiness condition rather than being erased.
-/

namespace SemanticMolecule

def aromaticPairEdge? (interaction : SemanticInteraction) : Option (Nat × Nat) :=
  match interaction.participants, interaction.kind with
  | [left, right], .aromatic => some (semanticEdgeKey left right)
  | _, _ => none

def aromaticPairEdges (source : SemanticMolecule) : List (Nat × Nat) :=
  source.interactions.filterMap aromaticPairEdge?

def aromaticAtomIndices (source : SemanticMolecule) : List Nat :=
  (source.aromaticPairEdges.flatMap fun edge => [edge.1, edge.2]).eraseDups

def clearAromaticFlagsAt (indices : List Nat) : Nat → List SemanticAtom → List SemanticAtom
  | _index, [] => []
  | index, atom :: atoms =>
      (if indices.contains index then { atom with aromaticInput := false } else atom) ::
        clearAromaticFlagsAt indices (index + 1) atoms

@[simp] theorem clearAromaticFlagsAt_length (indices : List Nat) :
    ∀ (index : Nat) (atoms : List SemanticAtom),
      (clearAromaticFlagsAt indices index atoms).length = atoms.length
  | _index, [] => rfl
  | index, _atom :: atoms => by
      simp [clearAromaticFlagsAt, clearAromaticFlagsAt_length indices (index + 1) atoms]

def withAromaticKekuleSelectionInteraction (selectedDouble : List (Nat × Nat))
    (interaction : SemanticInteraction) : SemanticInteraction :=
  match aromaticPairEdge? interaction with
  | some edge =>
      { interaction with
        kind := .covalent (if selectedDouble.contains edge then 2 else 1) }
  | none => interaction

def withAromaticKekuleSelection (source : SemanticMolecule)
    (selectedDouble : List (Nat × Nat)) : SemanticMolecule :=
  { atoms := clearAromaticFlagsAt source.aromaticAtomIndices 0 source.atoms
    interactions := source.interactions.map
      (withAromaticKekuleSelectionInteraction selectedDouble) }

@[simp] theorem withAromaticKekuleSelection_atoms
    (source : SemanticMolecule) (selectedDouble : List (Nat × Nat)) :
    (source.withAromaticKekuleSelection selectedDouble).atoms =
      clearAromaticFlagsAt source.aromaticAtomIndices 0 source.atoms := rfl

@[simp] theorem withAromaticKekuleSelection_interactions_length
    (source : SemanticMolecule) (selectedDouble : List (Nat × Nat)) :
    (source.withAromaticKekuleSelection selectedDouble).interactions.length =
      source.interactions.length := by
  simp [withAromaticKekuleSelection]

@[simp] theorem withAromaticKekuleSelection_atomCount
    (source : SemanticMolecule) (selectedDouble : List (Nat × Nat)) :
    (source.withAromaticKekuleSelection selectedDouble).atomCount = source.atomCount := by
  simp [withAromaticKekuleSelection, SemanticMolecule.atomCount]

/-- Constitutional key retained by the semantic aromatic normalization.  Aromatic pair edges are
included before localization; an already localized nonaromatic pair contributes its existing key.
All other interaction kinds remain unsupported and contribute no key. -/
def aromaticNormalizedPairKey? (interaction : SemanticInteraction) : Option (Nat × Nat) :=
  match aromaticPairEdge? interaction with
  | some edge => some edge
  | none => interaction.localizedCovalentRecord?.map Prod.fst

def aromaticNormalizedPairKeys (source : SemanticMolecule) : List (Nat × Nat) :=
  source.interactions.filterMap aromaticNormalizedPairKey?

private theorem map_filterMap_option_map
    {α β γ : Type} (items : List α) (select : α → Option β) (mapValue : β → γ) :
    (items.filterMap select).map mapValue =
      items.filterMap (fun item => (select item).map mapValue) := by
  induction items with
  | nil => rfl
  | cons item items inductionHypothesis =>
      cases observed : select item <;> simp [observed, inductionHypothesis]

private theorem localizedRecordKey_after_aromaticSelection
    (selectedDouble : List (Nat × Nat)) (interaction : SemanticInteraction) :
    (SemanticInteraction.localizedCovalentRecord?
        (withAromaticKekuleSelectionInteraction selectedDouble interaction)).map Prod.fst =
      aromaticNormalizedPairKey? interaction := by
  cases participantsObserved : interaction.participants with
  | nil => simp [withAromaticKekuleSelectionInteraction, aromaticPairEdge?,
      SemanticInteraction.localizedCovalentRecord?, aromaticNormalizedPairKey?,
      participantsObserved]
  | cons left rest =>
      cases rest with
      | nil => simp [withAromaticKekuleSelectionInteraction, aromaticPairEdge?,
          SemanticInteraction.localizedCovalentRecord?, aromaticNormalizedPairKey?,
          participantsObserved]
      | cons right tail =>
          cases tail with
          | nil =>
              cases kindObserved : interaction.kind <;>
                simp [withAromaticKekuleSelectionInteraction, aromaticPairEdge?,
                  SemanticInteraction.localizedCovalentRecord?, aromaticNormalizedPairKey?,
                  participantsObserved, kindObserved] ;
                split <;> simp_all
          | cons third tail =>
              simp [withAromaticKekuleSelectionInteraction, aromaticPairEdge?,
                SemanticInteraction.localizedCovalentRecord?, aromaticNormalizedPairKey?,
                participantsObserved]

@[simp] theorem withAromaticKekuleSelection_localizedCovalentKeys
    (source : SemanticMolecule) (selectedDouble : List (Nat × Nat)) :
    (source.withAromaticKekuleSelection selectedDouble).localizedCovalentKeys =
      source.aromaticNormalizedPairKeys := by
  simp only [localizedCovalentKeys, localizedCovalentRecords,
    withAromaticKekuleSelection, List.filterMap_map]
  rw [map_filterMap_option_map]
  unfold aromaticNormalizedPairKeys
  congr 1
  funext interaction
  exact localizedRecordKey_after_aromaticSelection selectedDouble interaction

/-- Every declared aromatic pair occurrence must survive as an edge of the localized conjugated
ring graph.  In particular, an aromatic bridge or acyclic aromatic chain is rejected. -/
def SemanticAromaticBondsLocalized (source candidate : SemanticMolecule) : Prop :=
  ∀ edge, edge ∈ source.aromaticPairEdges →
    containsUndirectedEdge candidate.semanticLocalizedMancudeEdges edge.1 edge.2 = true

/-- Representation-independent form of aromatic localization, stated directly in the independent
finite `MoleculeGraph` relation. -/
def SemanticAromaticBondsGraphLocalized (source candidate : SemanticMolecule) : Prop :=
  ∀ edge, edge ∈ source.aromaticPairEdges →
    ∃ left right : Fin candidate.atomCount,
      left.val = edge.1 ∧ right.val = edge.2 ∧
        candidate.toLocalizedMoleculeGraph.LocalizedMancudeEdge left right

/-- Exact source-level resonance graph for the pair-aromatic branch: the finite localized mancude
edge set is neither missing a declared aromatic pair nor adding a nondeclared edge. -/
def SemanticAromaticMancudeEdgeSetExact (source candidate : SemanticMolecule) : Prop :=
  (∀ edge, edge ∈ source.aromaticPairEdges →
      edge ∈ candidate.semanticLocalizedMancudeEdges) ∧
    ∀ edge, edge ∈ candidate.semanticLocalizedMancudeEdges →
      edge ∈ source.aromaticPairEdges

def semanticAromaticMancudeEdgeSetExact? (source candidate : SemanticMolecule) : Bool :=
  source.aromaticPairEdges.all candidate.semanticLocalizedMancudeEdges.contains &&
    candidate.semanticLocalizedMancudeEdges.all source.aromaticPairEdges.contains

@[simp] theorem semanticAromaticMancudeEdgeSetExact?_eq_true_iff
    (source candidate : SemanticMolecule) :
    source.semanticAromaticMancudeEdgeSetExact? candidate = true ↔
      SemanticAromaticMancudeEdgeSetExact source candidate := by
  simp [semanticAromaticMancudeEdgeSetExact?, SemanticAromaticMancudeEdgeSetExact,
    List.all_eq_true]

/-- Under exact source-edge realization, the independent localized graph is determined solely by
the declared aromatic edge set and is therefore independent of the chosen Kekule matching. -/
theorem localizedMancudeEdge_iff_semanticEdgeKey_mem_aromaticPairEdges
    (source candidate : SemanticMolecule)
    (exact : SemanticAromaticMancudeEdgeSetExact source candidate)
    (left right : Fin candidate.atomCount) :
    candidate.toLocalizedMoleculeGraph.LocalizedMancudeEdge left right ↔
      semanticEdgeKey left.val right.val ∈ source.aromaticPairEdges := by
  constructor
  · intro localized
    have contained :=
      (candidate.containsUndirectedEdge_semanticLocalizedMancudeEdges_iff left right).mpr
        localized
    have pairPresent := (containsUndirectedEdge_eq_true_iff_pair_mem _ _ _).mp contained
    rcases pairPresent with forward | reverse
    · have order :=
        (candidate.pair_mem_semanticLocalizedMancudeEdges_iff left right).mp forward |>.1
      simpa [semanticEdgeKey, Nat.min_eq_left (Nat.le_of_lt order),
        Nat.max_eq_right (Nat.le_of_lt order)] using exact.2 _ forward
    · have order :=
        (candidate.pair_mem_semanticLocalizedMancudeEdges_iff right left).mp reverse |>.1
      simpa [semanticEdgeKey, Nat.min_eq_right (Nat.le_of_lt order),
        Nat.max_eq_left (Nat.le_of_lt order)] using exact.2 _ reverse
  · intro sourcePresent
    by_cases order : left.val < right.val
    · have keyIdentity : semanticEdgeKey left.val right.val = (left.val, right.val) := by
        simp [semanticEdgeKey, Nat.min_eq_left (Nat.le_of_lt order),
          Nat.max_eq_right (Nat.le_of_lt order)]
      have localizedPresent :
          (left.val, right.val) ∈ candidate.semanticLocalizedMancudeEdges :=
        exact.1 _ (by simpa [keyIdentity] using sourcePresent)
      exact (candidate.pair_mem_semanticLocalizedMancudeEdges_iff left right).mp
        localizedPresent |>.2
    · have notEqual : left.val ≠ right.val := by
        intro equality
        have finEquality : left = right := Fin.ext equality
        subst right
        have selfKey : semanticEdgeKey left.val left.val = (left.val, left.val) := by
          simp [semanticEdgeKey]
        have sourceSelf : (left.val, left.val) ∈ source.aromaticPairEdges := by
          simpa [selfKey] using sourcePresent
        have candidateSelf := exact.1 _ sourceSelf
        have orderSelf :=
          (candidate.pair_mem_semanticLocalizedMancudeEdges_iff left left).mp candidateSelf |>.1
        exact (Nat.lt_irrefl _ orderSelf)
      have reverseOrder : right.val < left.val := Nat.lt_of_le_of_ne
        (Nat.le_of_not_gt order) (Ne.symm notEqual)
      have keyIdentity : semanticEdgeKey left.val right.val = (right.val, left.val) := by
        simp [semanticEdgeKey, Nat.min_eq_right (Nat.le_of_lt reverseOrder),
          Nat.max_eq_left (Nat.le_of_lt reverseOrder)]
      have localizedPresent :
          (right.val, left.val) ∈ candidate.semanticLocalizedMancudeEdges :=
        exact.1 _ (by simpa [keyIdentity] using sourcePresent)
      exact localizedMancudeEdge_reverse candidate.toLocalizedMoleculeGraph
        ((candidate.pair_mem_semanticLocalizedMancudeEdges_iff right left).mp
          localizedPresent |>.2)

theorem semanticAromaticBondsLocalized_iff_graphLocalized
    (source candidate : SemanticMolecule) :
    SemanticAromaticBondsLocalized source candidate ↔
      SemanticAromaticBondsGraphLocalized source candidate := by
  constructor
  · intro localized edge edgePresent
    have contained := localized edge edgePresent
    have pairPresent :
        (edge.1, edge.2) ∈ candidate.semanticLocalizedMancudeEdges ∨
          (edge.2, edge.1) ∈ candidate.semanticLocalizedMancudeEdges :=
      (containsUndirectedEdge_eq_true_iff_pair_mem _ _ _).mp contained
    have bounds : edge.1 < candidate.atomCount ∧ edge.2 < candidate.atomCount := by
      rcases pairPresent with forward | reverse
      · exact candidate.endpoints_lt_of_mem_semanticLocalizedMancudeEdges forward
      · have reverseBounds :=
          candidate.endpoints_lt_of_mem_semanticLocalizedMancudeEdges reverse
        exact ⟨reverseBounds.2, reverseBounds.1⟩
    let left : Fin candidate.atomCount := ⟨edge.1, bounds.1⟩
    let right : Fin candidate.atomCount := ⟨edge.2, bounds.2⟩
    exact ⟨left, right, rfl, rfl,
      (candidate.containsUndirectedEdge_semanticLocalizedMancudeEdges_iff left right).mp
        contained⟩
  · intro graphLocalized edge edgePresent
    obtain ⟨left, right, leftValue, rightValue, localized⟩ :=
      graphLocalized edge edgePresent
    rw [← leftValue, ← rightValue]
    exact (candidate.containsUndirectedEdge_semanticLocalizedMancudeEdges_iff left right).mpr
      localized

def semanticAromaticBondsLocalized? (source candidate : SemanticMolecule) : Bool :=
  source.aromaticPairEdges.all fun edge =>
    containsUndirectedEdge candidate.semanticLocalizedMancudeEdges edge.1 edge.2

@[simp] theorem semanticAromaticBondsLocalized?_eq_true_iff
    (source candidate : SemanticMolecule) :
    source.semanticAromaticBondsLocalized? candidate = true ↔
      SemanticAromaticBondsLocalized source candidate := by
  simp [semanticAromaticBondsLocalized?, SemanticAromaticBondsLocalized,
    List.all_eq_true]

/-- In every localized semantic mancude component, the written double bonds are an ordinary
maximum-cardinality matching of the complete finite component edge graph. -/
def SemanticLocalizedMancudeKekuleAdmissible (molecule : SemanticMolecule) : Prop :=
  ∀ attached : Fin molecule.atomCount,
    let edges := molecule.semanticLocalizedMancudeComponentEdges attached.val
    let written := molecule.semanticLocalizedMancudeWrittenEdges attached.val
    IsMaximumMancudeEdgeMatching written edges

def semanticLocalizedMancudeKekuleAdmissible? (molecule : SemanticMolecule) : Bool :=
  (List.range molecule.atomCount).all fun attached =>
    let edges := molecule.semanticLocalizedMancudeComponentEdges attached
    let written := molecule.semanticLocalizedMancudeWrittenEdges attached
    decide (written ∈ maximumMancudeEdgeMatchings (exhaustiveMancudeEdgeMatchings edges))

@[simp] theorem semanticLocalizedMancudeKekuleAdmissible?_eq_true_iff
    (molecule : SemanticMolecule) :
    molecule.semanticLocalizedMancudeKekuleAdmissible? = true ↔
      molecule.SemanticLocalizedMancudeKekuleAdmissible := by
  unfold semanticLocalizedMancudeKekuleAdmissible?
    SemanticLocalizedMancudeKekuleAdmissible
  rw [List.all_eq_true]
  constructor
  · intro checked attached
    have atAttached := checked attached.val (List.mem_range.mpr attached.isLt)
    simp only [decide_eq_true_eq] at atAttached
    exact (mem_maximum_exhaustiveMancudeEdgeMatchings_iff
      (molecule.semanticLocalizedMancudeComponentEdges attached.val)
      (molecule.semanticLocalizedMancudeWrittenEdges attached.val)).1 atAttached
  · intro admissible attached attachedMem
    have maximum := admissible ⟨attached, List.mem_range.mp attachedMem⟩
    exact decide_eq_true
      ((mem_maximum_exhaustiveMancudeEdgeMatchings_iff
        (molecule.semanticLocalizedMancudeComponentEdges attached)
        (molecule.semanticLocalizedMancudeWrittenEdges attached)).2 maximum)

/-- At every attached atom, semantic Kekule admissibility supplies a maximum ordinary matching on
an edge list already proved to realize exactly the independent localized component, while the
selected written subset is exactly the localized graph's written-double relation. -/
theorem SemanticLocalizedMancudeKekuleAdmissible.maximum_realized_at
    {molecule : SemanticMolecule}
    (admissible : molecule.SemanticLocalizedMancudeKekuleAdmissible)
    (attached : Fin molecule.atomCount) :
    IsMaximumMancudeEdgeMatching
        (molecule.semanticLocalizedMancudeWrittenEdges attached.val)
        (molecule.semanticLocalizedMancudeComponentEdges attached.val) ∧
      (∀ left right : Fin molecule.atomCount,
        NatEdgeMatchedBy (molecule.semanticLocalizedMancudeComponentEdges attached.val)
            left right ↔
          molecule.toLocalizedMoleculeGraph.LocalizedMancudeEdge left right ∧
            molecule.toLocalizedMoleculeGraph.InMancudeComponent attached left) ∧
      (∀ left right : Fin molecule.atomCount,
        NatEdgeMatchedBy (molecule.semanticLocalizedMancudeWrittenEdges attached.val)
            left right ↔
          molecule.toLocalizedMoleculeGraph.LocalizedMancudeEdge left right ∧
            molecule.toLocalizedMoleculeGraph.InMancudeComponent attached left ∧
              molecule.toLocalizedMoleculeGraph.bond left right = 2) := by
  exact ⟨admissible attached,
    molecule.natEdgeMatchedBy_semanticLocalizedMancudeComponentEdges_iff attached,
    molecule.natEdgeMatchedBy_semanticLocalizedMancudeWrittenEdges_iff attached⟩

structure SemanticAromaticKekuleChoice (source : SemanticMolecule) where
  selectedDoubleEdges : List (Nat × Nat)
  candidate : SemanticMolecule
  candidate_eq : candidate = source.withAromaticKekuleSelection selectedDoubleEdges
  deriving DecidableEq, Repr

/-- Any two generated choices have exactly the same atom records after the source aromatic flags
are cleared; only aromatic single/double placement can differ. -/
theorem SemanticAromaticKekuleChoice.candidate_atoms_eq
    {source : SemanticMolecule}
    (left right : SemanticAromaticKekuleChoice source) :
    left.candidate.atoms = right.candidate.atoms := by
  rw [left.candidate_eq, right.candidate_eq]
  rfl

/-- Kekule selection cannot change the ordered constitutional pair-key list. -/
theorem SemanticAromaticKekuleChoice.candidate_localizedCovalentKeys_eq
    {source : SemanticMolecule}
    (left right : SemanticAromaticKekuleChoice source) :
    left.candidate.localizedCovalentKeys = right.candidate.localizedCovalentKeys := by
  rw [left.candidate_eq, right.candidate_eq,
    source.withAromaticKekuleSelection_localizedCovalentKeys,
    source.withAromaticKekuleSelection_localizedCovalentKeys]

def semanticAromaticKekuleCandidates (source : SemanticMolecule) :
    List (SemanticAromaticKekuleChoice source) :=
  source.aromaticPairEdges.sublists.map fun selectedDoubleEdges =>
    { selectedDoubleEdges := selectedDoubleEdges
      candidate := source.withAromaticKekuleSelection selectedDoubleEdges
      candidate_eq := rfl }

def SemanticAromaticKekuleChoice.Valid
    {source : SemanticMolecule} (choice : SemanticAromaticKekuleChoice source) : Prop :=
  source.StructurallyWellFormed ∧
    choice.candidate.LocalizedCIPGraphReady ∧
      SemanticAromaticBondsGraphLocalized source choice.candidate ∧
        SemanticAromaticMancudeEdgeSetExact source choice.candidate ∧
          choice.candidate.SemanticLocalizedMancudeKekuleAdmissible

def SemanticAromaticKekuleChoice.valid?
    {source : SemanticMolecule} (choice : SemanticAromaticKekuleChoice source) : Bool :=
  source.structurallyWellFormed? &&
    choice.candidate.localizedCIPGraphReady? &&
      source.semanticAromaticBondsLocalized? choice.candidate &&
        source.semanticAromaticMancudeEdgeSetExact? choice.candidate &&
          choice.candidate.semanticLocalizedMancudeKekuleAdmissible?

@[simp] theorem SemanticAromaticKekuleChoice.valid?_eq_true_iff
    {source : SemanticMolecule} (choice : SemanticAromaticKekuleChoice source) :
    choice.valid? = true ↔ choice.Valid := by
  simp [SemanticAromaticKekuleChoice.valid?, SemanticAromaticKekuleChoice.Valid,
    semanticAromaticBondsLocalized_iff_graphLocalized, and_assoc]

/-- The independent localized mancude relation is invariant across any two valid Kekule choices
for the same semantic aromatic source.  The vertices may inhabit different definitionally indexed
`Fin` types; equality of their natural-number atom indices is the exact correspondence. -/
theorem SemanticAromaticKekuleChoice.Valid.localizedMancudeEdge_invariant
    {source : SemanticMolecule}
    {leftChoice rightChoice : SemanticAromaticKekuleChoice source}
    (leftValid : leftChoice.Valid) (rightValid : rightChoice.Valid)
    (leftSource leftTarget : Fin leftChoice.candidate.atomCount)
    (rightSource rightTarget : Fin rightChoice.candidate.atomCount)
    (sourceIndex : leftSource.val = rightSource.val)
    (targetIndex : leftTarget.val = rightTarget.val) :
    leftChoice.candidate.toLocalizedMoleculeGraph.LocalizedMancudeEdge
        leftSource leftTarget ↔
      rightChoice.candidate.toLocalizedMoleculeGraph.LocalizedMancudeEdge
        rightSource rightTarget := by
  rw [localizedMancudeEdge_iff_semanticEdgeKey_mem_aromaticPairEdges
      source leftChoice.candidate leftValid.2.2.2.1 leftSource leftTarget,
    localizedMancudeEdge_iff_semanticEdgeKey_mem_aromaticPairEdges
      source rightChoice.candidate rightValid.2.2.2.1 rightSource rightTarget,
    sourceIndex, targetIndex]

/-- Exact Rule-1a mancude averaging is invariant under the selected written Kekule matching once
both selections realize exactly the same declared aromatic edge set. -/
theorem exactMancudeAverage_withAromaticKekuleSelection_invariant
    (source : SemanticMolecule)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection leftSelection))
    (rightExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection rightSelection))
    (attached : Fin (source.withAromaticKekuleSelection leftSelection).atomCount) :
    ((source.withAromaticKekuleSelection leftSelection).toLocalizedMoleculeGraph
      ).exactMancudeAverage attached =
      ((source.withAromaticKekuleSelection rightSelection).toLocalizedMoleculeGraph
        ).exactMancudeAverage attached := by
  apply MoleculeGraph.exactMancudeAverage_eq_of_atomZ_eq_of_localizedMancudeEdge_iff
  · intro atom
    rfl
  · intro left right
    rw [localizedMancudeEdge_iff_semanticEdgeKey_mem_aromaticPairEdges
        source (source.withAromaticKekuleSelection leftSelection) leftExact left right,
      localizedMancudeEdge_iff_semanticEdgeKey_mem_aromaticPairEdges
        source (source.withAromaticKekuleSelection rightSelection) rightExact left right]

/-- Every independent exact Rule-1a observation—not only the component average—is invariant under
the chosen valid Kekule matching.  This includes real atoms, ring duplicates, placeholders, and
multiple-bond duplicates at every parent address. -/
theorem exactOfficialRule1aObservation_withAromaticKekuleSelection_invariant
    (source : SemanticMolecule)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection leftSelection))
    (rightExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection rightSelection))
    (node : OfficialCIPNode
      (Fin (source.withAromaticKekuleSelection leftSelection).atomCount)) :
    ((source.withAromaticKekuleSelection leftSelection).toLocalizedMoleculeGraph
        ).exactOfficialRule1aObservation node =
      ((source.withAromaticKekuleSelection rightSelection).toLocalizedMoleculeGraph
        ).exactOfficialRule1aObservation node := by
  apply MoleculeGraph.exactOfficialRule1aObservation_eq_of_atomZ_eq_of_localizedMancudeEdge_iff
  · intro atom
    rfl
  · intro left right
    rw [localizedMancudeEdge_iff_semanticEdgeKey_mem_aromaticPairEdges
        source (source.withAromaticKekuleSelection leftSelection) leftExact left right,
      localizedMancudeEdge_iff_semanticEdgeKey_mem_aromaticPairEdges
        source (source.withAromaticKekuleSelection rightSelection) rightExact left right]

/-- The executable exhaustive observation inherits the same choice independence through its
proved equality with the independent maximum-matching specification. -/
theorem semanticExactOfficialRule1aObservation_withAromaticKekuleSelection_invariant
    (source : SemanticMolecule)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection leftSelection))
    (rightExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection rightSelection))
    (node : OfficialCIPNode
      (Fin (source.withAromaticKekuleSelection leftSelection).atomCount)) :
    (source.withAromaticKekuleSelection leftSelection
        ).semanticExactOfficialRule1aObservation node =
      (source.withAromaticKekuleSelection rightSelection
        ).semanticExactOfficialRule1aObservation node := by
  rw [(source.withAromaticKekuleSelection leftSelection
      ).semanticExactOfficialRule1aObservation_eq_independent node,
    (source.withAromaticKekuleSelection rightSelection
      ).semanticExactOfficialRule1aObservation_eq_independent node]
  exact source.exactOfficialRule1aObservation_withAromaticKekuleSelection_invariant
    leftSelection rightSelection leftExact rightExact node

/-- For any fixed addressed provenance trees, their complete exact Rules-1a--2 trace is independent
of Kekule selection.  The only remaining choice-independence obligation is therefore structural:
relating the provenance trees generated by the alternative written matchings. -/
theorem compareAddressedSourceTraceObserved_withAromaticKekuleSelection_invariant
    (source : SemanticMolecule)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection leftSelection))
    (rightExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection rightSelection))
    (leftSources rightSources : OfficialRuleMajorKey.AddressedSourceLayers
      (Fin (source.withAromaticKekuleSelection leftSelection).atomCount)) :
    ExactOfficialRuleMajorKey.compareAddressedSourceTraceObserved
        (source.withAromaticKekuleSelection leftSelection).toLocalizedMoleculeGraph
        (source.withAromaticKekuleSelection leftSelection
          ).semanticExactOfficialRule1aObservation leftSources rightSources =
      ExactOfficialRuleMajorKey.compareAddressedSourceTraceObserved
        (source.withAromaticKekuleSelection rightSelection).toLocalizedMoleculeGraph
        (source.withAromaticKekuleSelection rightSelection
          ).semanticExactOfficialRule1aObservation leftSources rightSources := by
  have observationIdentity :
      (source.withAromaticKekuleSelection leftSelection
        ).semanticExactOfficialRule1aObservation =
      (source.withAromaticKekuleSelection rightSelection
        ).semanticExactOfficialRule1aObservation := by
    funext node
    exact source.semanticExactOfficialRule1aObservation_withAromaticKekuleSelection_invariant
      leftSelection rightSelection leftExact rightExact node
  unfold ExactOfficialRuleMajorKey.compareAddressedSourceTraceObserved
    ExactOfficialRuleMajorKey.observedRule1aLayers ExactOfficialRuleMajorKey.rule2Layers
  rw [observationIdentity]
  rfl

structure SemanticAromaticKekuleNormalizationCertificate
    (source : SemanticMolecule) (choice : SemanticAromaticKekuleChoice source) : Prop where
  generated : choice ∈ source.semanticAromaticKekuleCandidates
  valid : choice.Valid

def SemanticAromaticKekuleNormalizable (source : SemanticMolecule) : Prop :=
  ∃ choice, Nonempty (SemanticAromaticKekuleNormalizationCertificate source choice)

def normalizeSemanticAromaticKekule?
    (source : SemanticMolecule) : Option (SemanticAromaticKekuleChoice source) :=
  source.semanticAromaticKekuleCandidates.find? SemanticAromaticKekuleChoice.valid?

theorem normalizeSemanticAromaticKekule?_certificate
    (source : SemanticMolecule) (choice : SemanticAromaticKekuleChoice source)
    (computed : source.normalizeSemanticAromaticKekule? = some choice) :
    SemanticAromaticKekuleNormalizationCertificate source choice := by
  have validBool : choice.valid? = true := List.find?_some computed
  have generated : choice ∈ source.semanticAromaticKekuleCandidates := by
    rcases (List.find?_eq_some_iff_append.mp computed).2 with
      ⟨before, after, candidatesEq, _⟩
    rw [candidatesEq]
    simp
  exact { generated := generated
          valid := (SemanticAromaticKekuleChoice.valid?_eq_true_iff choice).mp validBool }

@[simp] theorem normalizeSemanticAromaticKekule?_isSome_iff
    (source : SemanticMolecule) :
    source.normalizeSemanticAromaticKekule?.isSome = true ↔
      source.SemanticAromaticKekuleNormalizable := by
  unfold normalizeSemanticAromaticKekule? SemanticAromaticKekuleNormalizable
  rw [List.find?_isSome]
  constructor
  · rintro ⟨choice, generated, validBool⟩
    exact ⟨choice, ⟨{
      generated := generated
      valid := (SemanticAromaticKekuleChoice.valid?_eq_true_iff choice).mp validBool
    }⟩⟩
  · rintro ⟨choice, ⟨certificate⟩⟩
    exact ⟨choice, certificate.generated,
      (SemanticAromaticKekuleChoice.valid?_eq_true_iff choice).mpr certificate.valid⟩

theorem SemanticAromaticKekuleNormalizationCertificate.candidate_atomCount
    {source : SemanticMolecule} {choice : SemanticAromaticKekuleChoice source}
    (_certificate : SemanticAromaticKekuleNormalizationCertificate source choice) :
    choice.candidate.atomCount = source.atomCount := by
  rw [choice.candidate_eq]
  exact source.withAromaticKekuleSelection_atomCount choice.selectedDoubleEdges

end SemanticMolecule

namespace AuthoritativeChemicalInput

/-- Replace only the semantic molecule, preserving all spatial and diagram evidence. -/
def withMolecule (source : AuthoritativeChemicalInput) (molecule : SemanticMolecule) :
    AuthoritativeChemicalInput :=
  { molecule := molecule
    spatial? := source.spatial?
    diagram? := source.diagram? }

@[simp] theorem withMolecule_molecule (source : AuthoritativeChemicalInput)
    (molecule : SemanticMolecule) :
    (source.withMolecule molecule).molecule = molecule := rfl

@[simp] theorem withMolecule_spatial? (source : AuthoritativeChemicalInput)
    (molecule : SemanticMolecule) :
    (source.withMolecule molecule).spatial? = source.spatial? := rfl

@[simp] theorem withMolecule_diagram? (source : AuthoritativeChemicalInput)
    (molecule : SemanticMolecule) :
    (source.withMolecule molecule).diagram? = source.diagram? := rfl

theorem withMolecule_structurallyWellFormed
    (source : AuthoritativeChemicalInput) (molecule : SemanticMolecule)
    (sourceWellFormed : source.StructurallyWellFormed)
    (moleculeWellFormed : molecule.StructurallyWellFormed)
    (atomCount : molecule.atomCount = source.molecule.atomCount) :
    (source.withMolecule molecule).StructurallyWellFormed := by
  rcases sourceWellFormed with ⟨_sourceMoleculeWellFormed, spatialWellFormed,
    diagramWellFormed⟩
  refine ⟨moleculeWellFormed, ?_, ?_⟩
  · simpa [AuthoritativeChemicalInput.withMolecule,
      AuthoritativeChemicalInput.SpatialIndicesWellFormed, atomCount] using
      spatialWellFormed
  · simpa [AuthoritativeChemicalInput.withMolecule,
      AuthoritativeChemicalInput.DiagramIndicesWellFormed, atomCount] using
      diagramWellFormed

end AuthoritativeChemicalInput

/-- Proof-bearing authoritative aromatic normalization.  The original evidence channels are
preserved, while the semantic molecule is replaced by an exhaustive maximum-matching Kekule
candidate that satisfies the complete localized graph-readiness boundary. -/
structure CertifiedAuthoritativeSemanticAromaticKekuleNormalization
    (source : AuthoritativeChemicalInput) where
  choice : SemanticMolecule.SemanticAromaticKekuleChoice source.molecule
  certificate :
    SemanticMolecule.SemanticAromaticKekuleNormalizationCertificate source.molecule choice
  sourceStructurallyWellFormed : source.StructurallyWellFormed

namespace CertifiedAuthoritativeSemanticAromaticKekuleNormalization

def normalizedSource {source : AuthoritativeChemicalInput}
    (normalized : CertifiedAuthoritativeSemanticAromaticKekuleNormalization source) :
    AuthoritativeChemicalInput :=
  source.withMolecule normalized.choice.candidate

theorem normalizedSource_structurallyWellFormed {source : AuthoritativeChemicalInput}
    (normalized : CertifiedAuthoritativeSemanticAromaticKekuleNormalization source) :
    normalized.normalizedSource.StructurallyWellFormed := by
  apply source.withMolecule_structurallyWellFormed normalized.choice.candidate
    normalized.sourceStructurallyWellFormed
  · exact normalized.certificate.valid.2.1.1
  · exact normalized.certificate.candidate_atomCount

def toApplicable {source : AuthoritativeChemicalInput}
    (normalized : CertifiedAuthoritativeSemanticAromaticKekuleNormalization source) :
    CertifiedLocalizedCIPApplicableInput :=
  { source := normalized.normalizedSource
    applicable := ⟨normalized.normalizedSource_structurallyWellFormed,
      normalized.certificate.valid.2.1⟩ }

noncomputable def analyze {source : AuthoritativeChemicalInput}
    (normalized : CertifiedAuthoritativeSemanticAromaticKekuleNormalization source) :
    SupportedAuthoritativeLocalizedStereochemicalAnalysis :=
  normalized.toApplicable.analyze

theorem analyze_descriptorAssignment_member_conforms
    {source : AuthoritativeChemicalInput}
    (normalized : CertifiedAuthoritativeSemanticAromaticKekuleNormalization source)
    (assignment : normalized.analyze.input.LocalizedScheduledStereochemicalAssignment
      (defaultLocalizedStereochemicalFuel normalized.analyze.input))
    (present :
      CertifiedLocalizedCIPInput.LocalizedScheduledStereochemicalAnalysisEntry.descriptorAssignment
          assignment ∈ normalized.analyze.entries) :
    normalized.analyze.input.DeclarativeLocalizedScheduledStereochemicalAssignment
      (defaultLocalizedStereochemicalFuel normalized.analyze.input) assignment := by
  exact normalized.toApplicable.analyze_descriptorAssignment_member_conforms assignment present

end CertifiedAuthoritativeSemanticAromaticKekuleNormalization

def AuthoritativeChemicalInput.SemanticAromaticKekuleNormalizable
    (source : AuthoritativeChemicalInput) : Prop :=
  source.StructurallyWellFormed ∧ source.molecule.SemanticAromaticKekuleNormalizable

def AuthoritativeChemicalInput.normalizeSemanticAromaticKekule?
    (source : AuthoritativeChemicalInput) :
    Option (CertifiedAuthoritativeSemanticAromaticKekuleNormalization source) :=
  if checked : source.structurallyWellFormed? = true then
    match computed : source.molecule.normalizeSemanticAromaticKekule? with
    | none => none
    | some choice =>
        some {
          choice := choice
          certificate := source.molecule.normalizeSemanticAromaticKekule?_certificate choice computed
          sourceStructurallyWellFormed := source.structurallyWellFormed?_eq_true_iff.mp checked
        }
  else none

@[simp] theorem AuthoritativeChemicalInput.normalizeSemanticAromaticKekule?_isSome_iff
    (source : AuthoritativeChemicalInput) :
    source.normalizeSemanticAromaticKekule?.isSome = true ↔
      source.SemanticAromaticKekuleNormalizable := by
  constructor
  · intro present
    obtain ⟨normalized, _computed⟩ := Option.isSome_iff_exists.mp present
    exact ⟨normalized.sourceStructurallyWellFormed,
      ⟨normalized.choice, ⟨normalized.certificate⟩⟩⟩
  · rintro ⟨sourceWellFormed, moleculeNormalizable⟩
    have checked : source.structurallyWellFormed? = true :=
      source.structurallyWellFormed?_eq_true_iff.mpr sourceWellFormed
    have moleculePresent :
        source.molecule.normalizeSemanticAromaticKekule?.isSome = true :=
      source.molecule.normalizeSemanticAromaticKekule?_isSome_iff.mpr moleculeNormalizable
    unfold AuthoritativeChemicalInput.normalizeSemanticAromaticKekule?
    rw [dif_pos checked]
    split
    · rename_i computed
      simp [computed] at moleculePresent
    · rfl

/-- Every independently normalizable authoritative aromatic source has a certified localized
analysis, and every descriptor it emits satisfies the independent scheduled-family semantics. -/
theorem AuthoritativeChemicalInput.exists_semanticAromaticKekule_analysis_all_descriptors_conform
    (source : AuthoritativeChemicalInput)
    (normalizable : source.SemanticAromaticKekuleNormalizable) :
    ∃ normalized : CertifiedAuthoritativeSemanticAromaticKekuleNormalization source,
      ∀ assignment,
        CertifiedLocalizedCIPInput.LocalizedScheduledStereochemicalAnalysisEntry.descriptorAssignment
            assignment ∈ normalized.analyze.entries →
          normalized.analyze.input.DeclarativeLocalizedScheduledStereochemicalAssignment
            (defaultLocalizedStereochemicalFuel normalized.analyze.input) assignment := by
  have present : source.normalizeSemanticAromaticKekule?.isSome = true :=
    source.normalizeSemanticAromaticKekule?_isSome_iff.mpr normalizable
  obtain ⟨normalized, computed⟩ := Option.isSome_iff_exists.mp present
  refine ⟨normalized, ?_⟩
  intro assignment member
  exact normalized.analyze_descriptorAssignment_member_conforms assignment member

end

end TetraStereo.OneCenter
