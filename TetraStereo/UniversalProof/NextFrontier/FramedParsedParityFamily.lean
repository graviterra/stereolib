import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorRuntime

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000










































namespace TetraStereo.UniversalProof.FramedParsedParityFamily

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule

/-! ## The eight-member parsed parity family -/

/-- Written parity marker. `@` is anticlockwise, `@@` is clockwise (smiles convention in the
adopted source). -/
def parityMarker : TetrahedralInputParity → String
  | .clockwise => "@@"
  | .anticlockwise => "@"

/-- Actual SMILES string of the fixed topology with the three written parities substituted. -/
def familyString (center leftArm rightArm : TetrahedralInputParity) : String :=
  "[H]-[C" ++ parityMarker center ++ "](-[C" ++ parityMarker leftArm ++
    "](-[H])(-[F])-[Cl])(-[Br])-[C" ++ parityMarker rightArm ++ "](-[H])(-[F])-[Cl]"

/-- Actual parse of the member; `none` is the fail-closed fallback. -/
def familyMol? (center leftArm rightArm : TetrahedralInputParity) : Option RawMolecule :=
  match parseOpenSMILES (familyString center leftArm rightArm) with
  | .ok mol => some mol
  | .error _ => none

/-- Actual complete central fact in the requested mode: actual parse, actual mode-selected
auxiliary builder (`buildOccurrenceAuxState?` fast, `buildOccurrenceAuxStateFullyAuthoritative?`
authoritative), then the actual maintained complete central occurrence caller. -/
def centralFact? (center leftArm rightArm : TetrahedralInputParity) (authoritative : Bool) :
    Option OccurrenceAuxFact := do
  let mol ← familyMol? center leftArm rightArm
  let fuel := analysisFuel mol
  let state ← if authoritative then buildOccurrenceAuxStateFullyAuthoritative? mol fuel 1
               else buildOccurrenceAuxState? mol fuel 1
  if authoritative then
    occurrenceFactAuthoritative? mol fuel state (canonicalCenterRoot 1)
  else
    occurrenceFact? mol fuel state (canonicalCenterRoot 1)

/-- Actual complete arm-pair decision (atoms 2 vs 7) under the shared profile at center root 1. -/
def armPairDecision? (center leftArm rightArm : TetrahedralInputParity) (authoritative : Bool) :
    Option OccurrenceComparison := do
  let mol ← familyMol? center leftArm rightArm
  let profile ← FrameRuntime.profile? mol (canonicalCenterRoot 1)
  let fuel := analysisFuel mol
  let state ← if authoritative then buildOccurrenceAuxStateFullyAuthoritative? mol fuel 1
               else buildOccurrenceAuxState? mol fuel 1
  let roots ← occurrenceLigandFrame? mol (canonicalCenterRoot 1)
  let left ← roots.find? (fun cursor => cursor.node.atom == 2)
  let right ← roots.find? (fun cursor => cursor.node.atom == 7)
  FrameRuntime.decisionComplete? mol profile authoritative state fuel left right

/-! ## Independently derived expected values (candidate classification)

These are derived from the independent parity choices: same-arm written parity gives an arm
comparison tie and a refused central fact; opposite-arm parity is the Rule-5 pseudoasymmetric case. The descriptor uses the center
parity and the even/odd permutation of the actual sorted-ligand positions. The truth of these
candidates is established only if the kernel `decide` proofs below check. -/

/-- Sorted priority positions of the four ligands `[H(0), arm(2), Br(6), arm(7)]`, read off the
actual sorted atom order. Case A (`leftArm = @`): arms order `[2,7]` -> `[2,1,3,0]`.
Case B (`leftArm = @@`): arms order `[7,2]` -> `[2,3,1,0]`. -/
def expectedPositions : TetrahedralInputParity → List Nat
  | .anticlockwise => [2, 1, 3, 0]
  | .clockwise => [2, 3, 1, 0]

/-- Candidate complete central fact. Mode-independent (both builders agree at these parities). -/
def expectedFact? (center leftArm rightArm : TetrahedralInputParity) : Option OccurrenceAuxFact :=
  match leftArm, rightArm with
  | .anticlockwise, .anticlockwise => none
  | .clockwise, .clockwise => none
  | .anticlockwise, .clockwise =>
      some
        { key := canonicalOccurrenceKey (canonicalCenterRoot 1)
          atom := 1
          descriptor := descriptorOfParity center (permutationIsEven [2, 1, 3, 0])
          uppercase := false
          priorityPositions := [2, 1, 3, 0] }
  | .clockwise, .anticlockwise =>
      some
        { key := canonicalOccurrenceKey (canonicalCenterRoot 1)
          atom := 1
          descriptor := descriptorOfParity center (permutationIsEven [2, 3, 1, 0])
          uppercase := false
          priorityPositions := [2, 3, 1, 0] }

/-- Candidate arm-pair decision: successful non-pseudo tie when written parities agree; Rule-5 pseudoasymmetric
`gt`/`lt` with `pseudo = true` when they oppose. -/
def expectedArmDecision? (leftArm rightArm : TetrahedralInputParity) : Option OccurrenceComparison :=
  match leftArm, rightArm with
  | .anticlockwise, .anticlockwise => some { ordering := Ordering.eq, pseudo := false }
  | .clockwise, .clockwise => some { ordering := Ordering.eq, pseudo := false }
  | .anticlockwise, .clockwise => some { ordering := Ordering.gt, pseudo := true }
  | .clockwise, .anticlockwise => some { ordering := Ordering.lt, pseudo := true }

/-! ## Independent closed structural family lemmas (parameter reach) -/

/-- Every member is accepted by the actual parser. -/
theorem family_parse_success (center leftArm rightArm : TetrahedralInputParity) :
    (parseOpenSMILES (familyString center leftArm rightArm)).isOk = true := by
  cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel

/-- Every member parses to the 11-atom topology and stores exactly the three chosen written
parities at atoms 1, 2 and 7. This proves each family parameter reaches the parsed input. -/
theorem family_structural (center leftArm rightArm : TetrahedralInputParity) :
    (familyMol? center leftArm rightArm).map (fun mol =>
      (mol.atomCount,
        (mol.atomAt? 1).bind (fun spec => spec.tetrahedral?),
        (mol.atomAt? 2).bind (fun spec => spec.tetrahedral?),
        (mol.atomAt? 7).bind (fun spec => spec.tetrahedral?))) =
      some (11, some center, some leftArm, some rightArm) := by
  cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel

/-- Independent actual auxiliary setup in the requested mode. It contains no central caller or
expected classification, so success excludes setup failure as a cause of central refusal. -/
def auxiliaryState? (center leftArm rightArm : TetrahedralInputParity) (authoritative : Bool) :
    Option OccurrenceAuxState := do
  let mol ← familyMol? center leftArm rightArm
  if authoritative then
    buildOccurrenceAuxStateFullyAuthoritative? mol (analysisFuel mol) 1
  else
    buildOccurrenceAuxState? mol (analysisFuel mol) 1

/-- All eight parsed members have a successful actual fast auxiliary builder. -/
theorem auxiliary_fast_success (center leftArm rightArm : TetrahedralInputParity) :
    (auxiliaryState? center leftArm rightArm false).isSome = true := by
  cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel

/-- All eight parsed members have a successful actual fully-authoritative auxiliary builder. -/
theorem auxiliary_authoritative_success (center leftArm rightArm : TetrahedralInputParity) :
    (auxiliaryState? center leftArm rightArm true).isSome = true := by
  cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel

/-! ## Actual closure theorems: all-parity, both modes -/

/- Fast-mode actual complete central fact equals the independently derived candidate. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem centralFast_eq_expected (center leftArm rightArm : TetrahedralInputParity) :
    centralFact? center leftArm rightArm false = expectedFact? center leftArm rightArm := by
  cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel

/- Authoritative-mode actual complete central fact equals the same candidate. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem centralAuthoritative_eq_expected (center leftArm rightArm : TetrahedralInputParity) :
    centralFact? center leftArm rightArm true = expectedFact? center leftArm rightArm := by
  cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel

/- Fast-mode actual complete arm-pair decision equals the independently derived candidate. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem armFast_eq_expected (center leftArm rightArm : TetrahedralInputParity) :
    armPairDecision? center leftArm rightArm false = expectedArmDecision? leftArm rightArm := by
  cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel

/- Authoritative-mode actual complete arm-pair decision equals the same candidate. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem armAuthoritative_eq_expected (center leftArm rightArm : TetrahedralInputParity) :
    armPairDecision? center leftArm rightArm true = expectedArmDecision? leftArm rightArm := by
  cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel

/-! ## Corollaries: non-vacuity and the tie/refusal versus pseudoasymmetric split

These are cheap: they rewrite by the actual closure theorems and then reduce only the
parser-free expected functions. -/

/-- The central fact caller refuses the same-arm tie; auxiliary success is proved independently. -/
theorem family_builder_none_same (center arm : TetrahedralInputParity) (authoritative : Bool) :
    centralFact? center arm arm authoritative = none := by
  cases authoritative
  · rw [centralFast_eq_expected]
    cases arm <;> rfl
  · rw [centralAuthoritative_eq_expected]
    cases arm <;> rfl

/-- Opposite written arm parity yields a fact: no vacuous `none = none`. -/
theorem family_builder_some_opposite (center leftArm rightArm : TetrahedralInputParity)
    (opposite : leftArm ≠ rightArm) (authoritative : Bool) :
    centralFact? center leftArm rightArm authoritative ≠ none := by
  cases authoritative
  · rw [centralFast_eq_expected]
    cases leftArm <;> cases rightArm <;> first | exact absurd rfl opposite | simp [expectedFact?]
  · rw [centralAuthoritative_eq_expected]
    cases leftArm <;> cases rightArm <;> first | exact absurd rfl opposite | simp [expectedFact?]

/-- Full-fact fields for an opposite-arm member: atom 1, descriptor from the center parity and the
actual priority permutation, lowercase pseudoasymmetric `uppercase = false`. -/
theorem family_builder_descriptor_opposite (center leftArm rightArm : TetrahedralInputParity)
    (opposite : leftArm ≠ rightArm) (authoritative : Bool) :
    (centralFact? center leftArm rightArm authoritative).map
        (fun fact => (fact.atom, fact.descriptor, fact.uppercase)) =
      some (1, descriptorOfParity center (permutationIsEven (expectedPositions leftArm)), false) := by
  cases authoritative
  · rw [centralFast_eq_expected]
    cases leftArm <;> cases rightArm <;> first | exact absurd rfl opposite | rfl
  · rw [centralAuthoritative_eq_expected]
    cases leftArm <;> cases rightArm <;> first | exact absurd rfl opposite | rfl

/-- Same written arm parity yields a successful non-pseudo tie, not an arm-comparison refusal. -/
theorem arm_tie_same (center arm : TetrahedralInputParity) (authoritative : Bool) :
    armPairDecision? center arm arm authoritative =
      some { ordering := Ordering.eq, pseudo := false } := by
  cases authoritative
  · rw [armFast_eq_expected]
    cases arm <;> rfl
  · rw [armAuthoritative_eq_expected]
    cases arm <;> rfl

/-- The actual arm-pair decision is the Rule-5 pseudoasymmetric case (`pseudo = true`) exactly when
the written arm parities oppose. -/
theorem arm_pseudo_opposite (center leftArm rightArm : TetrahedralInputParity)
    (opposite : leftArm ≠ rightArm) (authoritative : Bool) :
    (armPairDecision? center leftArm rightArm authoritative).map (fun decision => decision.pseudo) =
      some true := by
  cases authoritative
  · rw [armFast_eq_expected]
    cases leftArm <;> cases rightArm <;> first | exact absurd rfl opposite | rfl
  · rw [armAuthoritative_eq_expected]
    cases leftArm <;> cases rightArm <;> first | exact absurd rfl opposite | rfl






def factSummary (fact : OccurrenceAuxFact) : CanonicalOccurrenceKey × Nat × RS × Bool × List Nat :=
  (fact.key, fact.atom, fact.descriptor, fact.uppercase, fact.priorityPositions)

def observedFact (center leftArm rightArm : TetrahedralInputParity) (authoritative : Bool) :
    Option (CanonicalOccurrenceKey × Nat × RS × Bool × List Nat) :=
  (centralFact? center leftArm rightArm authoritative).map factSummary

def observedArm (center leftArm rightArm : TetrahedralInputParity) (authoritative : Bool) :
    Option (Ordering × Bool) :=
  (armPairDecision? center leftArm rightArm authoritative).map
    (fun decision => (decision.ordering, decision.pseudo))

#eval familyString .anticlockwise .anticlockwise .clockwise
#eval (parseOpenSMILES (familyString .anticlockwise .anticlockwise .clockwise)).isOk
#eval observedFact .anticlockwise .anticlockwise .clockwise false
#eval observedFact .anticlockwise .anticlockwise .clockwise true
#eval observedFact .clockwise .anticlockwise .clockwise false
#eval observedFact .anticlockwise .clockwise .clockwise false
#eval observedFact .clockwise .clockwise .clockwise false
#eval observedFact .clockwise .clockwise .anticlockwise true
#eval observedArm .anticlockwise .anticlockwise .clockwise false
#eval observedArm .anticlockwise .clockwise .anticlockwise false

#check family_parse_success
#check family_structural
#check auxiliary_fast_success
#check auxiliary_authoritative_success
#check arm_tie_same
#check centralFast_eq_expected
#check centralAuthoritative_eq_expected
#check family_builder_none_same
#check family_builder_some_opposite
#check arm_pseudo_opposite

end TetraStereo.UniversalProof.FramedParsedParityFamily
