import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3CircularAuxiliaryClassification

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Executable source-canonical coupled-unit perception

The earlier exhaustive classifier used proposition-level `decide` under `Classical`, making its
public definition noncomputable even though every condition is finite.  This module reflects the
complete four-key complementary-incidence relation into an explicit Boolean and rebuilds the
ordinary/coupled/ambiguous classifier without classical choice.
-/

/-- Executable reflection of the canonical order on physical-unit identifiers. -/
def aromaticCanonicalRule3PhysicalUnitLexLt?
    {source : AuthoritativeChemicalInput}
    (left right : source.AromaticCanonicalRule3PhysicalUnitId) : Bool :=
  decide (left.first.val < right.first.val) ||
    (left.first == right.first && decide (left.second.val < right.second.val))

theorem aromaticCanonicalRule3PhysicalUnitLexLt?_eq_true_iff
    {source : AuthoritativeChemicalInput}
    (left right : source.AromaticCanonicalRule3PhysicalUnitId) :
    aromaticCanonicalRule3PhysicalUnitLexLt? left right = true ↔ left.LexLt right := by
  simp [aromaticCanonicalRule3PhysicalUnitLexLt?,
    AromaticCanonicalRule3PhysicalUnitId.LexLt]

def aromaticCanonicalRule3CoupledUnitPairOK?
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (pair : source.AromaticCanonicalRule3CoupledUnitPair) : Bool :=
  (source.aromaticCanonicalRule3FramePhysicalUnits keys).contains pair.firstUnit &&
    (source.aromaticCanonicalRule3FramePhysicalUnits keys).contains pair.secondUnit &&
    aromaticCanonicalRule3PhysicalUnitLexLt? pair.firstUnit pair.secondUnit &&
    keys.length == 4 &&
    keys.all (fun left => keys.all (fun right =>
      ExactOfficialRuleMajorKey.compareObserved source.molecule.toLocalizedMoleculeGraph
        source.molecule.semanticExactOfficialRule1aObservation
        left.constitutional right.constitutional == Ordering.eq)) &&
    source.aromaticCanonicalRule3PhysicalUnitKeyCount keys pair.firstUnit == 2 &&
    source.aromaticCanonicalRule3PhysicalUnitKeyCount keys pair.secondUnit == 2 &&
    keys.all (fun key =>
      (source.aromaticCanonicalRule3PhysicalUnitIds key).contains pair.firstUnit !=
        (source.aromaticCanonicalRule3PhysicalUnitIds key).contains pair.secondUnit)

theorem aromaticCanonicalRule3CoupledUnitPairOK?_eq_true_iff
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (pair : source.AromaticCanonicalRule3CoupledUnitPair) :
    source.aromaticCanonicalRule3CoupledUnitPairOK? keys pair = true ↔
      source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys pair := by
  simp [aromaticCanonicalRule3CoupledUnitPairOK?,
    aromaticCanonicalRule3PhysicalUnitLexLt?_eq_true_iff,
    DeclarativeAromaticCanonicalRule3CoupledUnitPair, List.all_eq_true, and_assoc,
    ExactOfficialRuleMajorKey.compareObserved_eq_exact
      source.molecule.toLocalizedMoleculeGraph
      source.molecule.semanticExactOfficialRule1aObservation
      source.molecule.semanticExactOfficialRule1aObservation_eq_independent]
  intro _ _ _ _ _ _ _
  constructor
  · intro complementary key present
    have different := complementary key present
    constructor
    · intro firstPresent secondPresent
      exact different (by simp [firstPresent, secondPresent])
    · intro secondAbsent
      by_contra firstAbsent
      exact different (by simp [firstAbsent, secondAbsent])
  · intro complementary key present
    have relation := complementary key present
    by_cases firstPresent : pair.firstUnit ∈ source.aromaticCanonicalRule3PhysicalUnitIds key
    · have secondAbsent : pair.secondUnit ∉
          source.aromaticCanonicalRule3PhysicalUnitIds key := relation.mp firstPresent
      simp [firstPresent, secondAbsent]
    · have secondPresent : pair.secondUnit ∈
          source.aromaticCanonicalRule3PhysicalUnitIds key := by
        by_contra secondAbsent
        exact firstPresent (relation.mpr secondAbsent)
      simp [firstPresent, secondPresent]

/-- Exhaustive, structurally executable coupled-pair search. -/
def executableAromaticCanonicalRule3CoupledUnitPairs
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    List source.AromaticCanonicalRule3CoupledUnitPair :=
  (source.aromaticCanonicalRule3CoupledUnitPairCandidates keys).filter fun pair =>
    source.aromaticCanonicalRule3CoupledUnitPairOK? keys pair

theorem mem_executableAromaticCanonicalRule3CoupledUnitPairs_iff
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (pair : source.AromaticCanonicalRule3CoupledUnitPair) :
    pair ∈ source.executableAromaticCanonicalRule3CoupledUnitPairs keys ↔
      source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys pair := by
  rw [executableAromaticCanonicalRule3CoupledUnitPairs, List.mem_filter,
    source.aromaticCanonicalRule3CoupledUnitPairOK?_eq_true_iff,
    source.mem_aromaticCanonicalRule3CoupledUnitPairCandidates_iff]
  exact ⟨And.right, fun derived => ⟨⟨derived.1, derived.2.1⟩, derived⟩⟩

/-- Executable total classifier: no pair is ordinary, one pair is coupled, and two or more are
explicitly ambiguous. -/
def classifyExecutableAromaticCanonicalRule3CircularAuxiliary
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    source.AromaticCanonicalRule3CircularAuxiliaryClassification :=
  match source.executableAromaticCanonicalRule3CoupledUnitPairs keys with
  | [] => .ordinary
  | [pair] => .coupled pair
  | _ :: _ :: _ => .ambiguous

theorem classifyExecutableAromaticCanonicalRule3CircularAuxiliary_sound
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    source.DeclarativeAromaticCanonicalRule3CircularAuxiliaryClassification keys
      (source.classifyExecutableAromaticCanonicalRule3CircularAuxiliary keys) := by
  unfold classifyExecutableAromaticCanonicalRule3CircularAuxiliary
  cases foundIdentity : source.executableAromaticCanonicalRule3CoupledUnitPairs keys with
  | nil =>
      exact .ordinary (by
        intro pair derived
        have present :=
          (source.mem_executableAromaticCanonicalRule3CoupledUnitPairs_iff
            keys pair).mpr derived
        simp [foundIdentity] at present)
  | cons first tail =>
      cases tail with
      | nil =>
          exact .coupled first
            ((source.mem_executableAromaticCanonicalRule3CoupledUnitPairs_iff
              keys first).mp (by rw [foundIdentity]; simp))
            (by
              intro other derived
              have present :=
                (source.mem_executableAromaticCanonicalRule3CoupledUnitPairs_iff
                  keys other).mpr derived
              rw [foundIdentity] at present
              simpa using present)
      | cons second rest =>
          have firstDerived :=
            (source.mem_executableAromaticCanonicalRule3CoupledUnitPairs_iff
              keys first).mp (by rw [foundIdentity]; simp)
          have secondDerived :=
            (source.mem_executableAromaticCanonicalRule3CoupledUnitPairs_iff
              keys second).mp (by rw [foundIdentity]; simp)
          have candidateNodup := source.aromaticCanonicalRule3CoupledUnitPairCandidates_nodup keys
          have foundNodup :
              (source.executableAromaticCanonicalRule3CoupledUnitPairs keys).Nodup := by
            exact List.Nodup.filter _ candidateNodup
          rw [foundIdentity] at foundNodup
          exact .ambiguous first second firstDerived secondDerived
            (fun same => (List.nodup_cons.mp foundNodup).1 (by simp [same]))

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
