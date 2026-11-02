import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.FramedMultipleBondPublicDispatchRegression

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule

/-! A concrete parsed acyclic multiple-bond input outside the generated-real-tree profile.
The actual profile refusal selects the preserved legacy evaluator, whose primitive frame,
sorting and adjacency computations give a positive fact in both public modes. This fixture
does not assert a general multiple-bond comparator law or external chemistry approval. -/

def smiles : String := "F[C@](Cl)(C=O)Br"

def raw : RawMolecule :=
  match parseOpenSMILES smiles with
  | .ok mol => mol
  | .error _ => { atoms := [], bonds := [] }

def molecule : RawMolecule := (normalizeRawMolecule raw).parsed.withExplicitHydrogens

def fuel : Nat := 4

def ordinaryAtom (element : Element) : AtomSpec :=
  { element := element, explicitHydrogens? := some 0 }

def centerAtom : AtomSpec :=
  { element := .C, explicitHydrogens? := some 0, tetrahedral? := some .anticlockwise }

/-- Six parsed heavy atoms plus the aldehyde hydrogen, in actual written order. -/
def fixture : RawMolecule :=
  { atoms := [ordinaryAtom .F, centerAtom, ordinaryAtom .Cl,
      ordinaryAtom .C, ordinaryAtom .O, ordinaryAtom .Br, AtomSpec.aliphatic .H]
    bonds := [⟨0, 1, .single⟩, ⟨1, 2, .single⟩, ⟨1, 3, .single⟩,
      ⟨3, 6, .single⟩, ⟨3, 4, .double⟩, ⟨1, 5, .single⟩]
    neighborOrder := [[1], [0, 2, 3, 5], [1], [1, 6, 4], [3], [1], [3]]
    introductionPredecessors := [none, some 0, some 1, some 1, some 3, some 1] }

def center : CanonicalBranchNode := canonicalCenterRoot 1

def cursor (atom : Nat) : CanonicalRerootCursor :=
  { node := canonicalRoot 1 atom, previous? := some center }

def roots : List CanonicalRerootCursor := [cursor 0, cursor 2, cursor 3, cursor 5]

def sortedRoots : List CanonicalRerootCursor := [cursor 5, cursor 2, cursor 0, cursor 3]

def decisions : List OccurrenceComparison :=
  [{ ordering := .gt }, { ordering := .gt }, { ordering := .gt }]

def pairs : List (OccurrenceComparedPair fixture [] fuel) :=
  [{ left := cursor 5, right := cursor 2, decision := { ordering := .gt } },
   { left := cursor 2, right := cursor 0, decision := { ordering := .gt } },
   { left := cursor 0, right := cursor 3, decision := { ordering := .gt } }]

def expectedFact : OccurrenceAuxFact :=
  { key := canonicalOccurrenceKey center
    atom := 1
    descriptor := .S
    uppercase := true
    priorityPositions := [3, 1, 0, 2] }

/-- The fallback branch in `raw` is not used. -/
theorem parsed : parseOpenSMILES smiles = .ok raw := by rfl

theorem normalized_expanded : molecule = fixture := by decide +kernel

theorem written_double_bond :
    ({ source := 3, target := 4, kind := .double } : RawBond) ∈ fixture.bonds := by
  decide +kernel

/-- The multiple bond produces an actual canonical duplicate, not merely a source label. -/
theorem generated_multiple_bond_duplicate :
    (fixture.canonicalChildren (canonicalRoot 1 3)).any
      (fun node => match node.provenance with
        | .multipleBondDuplicate _ => true
        | _ => false) = true := by
  decide +kernel

theorem fixture_profile_none : FrameRuntime.profile? fixture center = none := by
  decide +kernel

theorem actual_profile_none : FrameRuntime.profile? molecule center = none := by
  rw [normalized_expanded]
  exact fixture_profile_none

theorem atom_at_center : fixture.atomAt? center.atom = some centerAtom := by
  decide +kernel

theorem roots_computed : occurrenceLigandFrame? fixture center = some roots := by
  decide +kernel

theorem fast_sort : sortOccurrencesTracked? fixture [] fuel roots =
    some (sortedRoots, 0) := by
  decide +kernel

theorem authoritative_sort : sortOccurrencesTrackedAuthoritative? fixture [] fuel roots =
    some (sortedRoots, 0) := by
  decide +kernel

theorem priority_positions :
    (sortedRoots.mapM fun item =>
      ((fixture.ligandsWithLonePair center.atom).zipIdx.find?
        fun entry => entry.1 == item.node.atom).map Prod.snd) = some [3, 1, 0, 2] := by
  decide +kernel

theorem fast_adjacency : compareOccurrenceAdjacentPairs? fixture [] fuel sortedRoots =
    some pairs := by
  rfl

theorem authoritative_adjacency :
    compareOccurrenceAdjacentPairsAuthoritative? fixture [] fuel sortedRoots =
      some decisions := by
  decide +kernel

/-- Assemble the unchanged legacy fast fact from the actual primitive observations. -/
theorem fixture_legacy_fast_fact :
    legacyOccurrenceFact? fixture fuel [] center = some expectedFact := by
  simp only [legacyOccurrenceFact?, atom_at_center, centerAtom, roots_computed,
    fast_sort, priority_positions, fast_adjacency, Bind.bind, Option.bind]
  rfl

/-- Assemble the unchanged legacy authoritative fact from the same generated frame. -/
theorem fixture_legacy_authoritative_fact :
    legacyOccurrenceFactAuthoritative? fixture fuel [] center = some expectedFact := by
  simp only [legacyOccurrenceFactAuthoritative?, atom_at_center, centerAtom, roots_computed,
    authoritative_sort, priority_positions, authoritative_adjacency, Bind.bind, Option.bind]
  rfl

theorem legacy_fast_fact : legacyOccurrenceFact? molecule fuel [] center = some expectedFact := by
  rw [normalized_expanded]
  exact fixture_legacy_fast_fact

theorem legacy_authoritative_fact :
    legacyOccurrenceFactAuthoritative? molecule fuel [] center = some expectedFact := by
  rw [normalized_expanded]
  exact fixture_legacy_authoritative_fact

/-- The public fast entry point preserves the positive result on the actual parsed input. -/
theorem public_fast_fact : occurrenceFact? molecule fuel [] center = some expectedFact := by
  rw [occurrenceFact?_eq_legacy_of_profile_none molecule fuel [] center actual_profile_none]
  exact legacy_fast_fact

/-- The public authoritative entry point preserves the same positive parsed-input result. -/
theorem public_authoritative_fact :
    occurrenceFactAuthoritative? molecule fuel [] center = some expectedFact := by
  rw [occurrenceFactAuthoritative?_eq_legacy_of_profile_none
    molecule fuel [] center actual_profile_none]
  exact legacy_authoritative_fact

theorem public_modes_agree :
    occurrenceFact? molecule fuel [] center = occurrenceFactAuthoritative? molecule fuel [] center := by
  rw [public_fast_fact, public_authoritative_fact]

end TetraStereo.UniversalProof.NextFrontier.FramedMultipleBondPublicDispatchRegression
