import TetraStereo.OneCenter.DeclarativeCIPOccurrenceRules456

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter OneCenter.RawMolecule

/-! Concrete observations for the unchanged public Rule-5 fixture. The parser/normalizer
is connected once to an explicit eleven-atom value. Actual generated profiles, ranking and
adjacent decisions are separate kernel leaves; no legacy evaluator is substituted. -/

def smiles : String := "F[C@](Cl)([C@H](Br)I)[C@@H](Br)I"

def raw : RawMolecule :=
  match parseOpenSMILES smiles with
  | .ok molecule => molecule
  | .error _ => { atoms := [], bonds := [] }

def result := normalizeRawMolecule raw
def molecule := result.parsed.withExplicitHydrogens
def fuel : Nat := 4


/-- Materialized atom metadata: input parity is preserved, inline hydrogens are consumed. -/
def fixtureCarbon (parity : TetrahedralInputParity) : AtomSpec :=
  { element := .C, explicitHydrogens? := some 0, tetrahedral? := some parity }

def fixtureAtom (element : Element) : AtomSpec :=
  { element := element, explicitHydrogens? := some 0 }

/-- Literal normalization/hydrogen-expansion result, including written neighbor order. -/
def fixtureMolecule : RawMolecule :=
  { atoms :=
      [fixtureAtom .F, fixtureCarbon .anticlockwise, fixtureAtom .Cl,
       fixtureCarbon .anticlockwise, fixtureAtom .Br, fixtureAtom .I,
       fixtureCarbon .clockwise, fixtureAtom .Br, fixtureAtom .I,
       AtomSpec.aliphatic .H, AtomSpec.aliphatic .H]
    bonds :=
      [⟨0, 1, .single⟩, ⟨1, 2, .single⟩, ⟨1, 3, .single⟩,
       ⟨3, 9, .single⟩, ⟨3, 4, .single⟩, ⟨3, 5, .single⟩,
       ⟨1, 6, .single⟩, ⟨6, 10, .single⟩, ⟨6, 7, .single⟩, ⟨6, 8, .single⟩]
    neighborOrder :=
      [[1], [0, 2, 3, 6], [1], [1, 9, 4, 5], [3], [3],
       [1, 10, 7, 8], [6], [6], [3], [6]]
    introductionPredecessors := [none, some 0, some 1, some 1, some 3, some 3, some 1, some 6, some 6] }

theorem molecule_eq_fixture : molecule = fixtureMolecule := by decide +kernel

def fixtureDescendant (parent atom : Nat) : CanonicalBranchNode :=
  { atom := atom, parent := parent, history := [atom, parent, 1], provenance := .realAtom }

/-- Actual breadth-first order, including both newly materialized hydrogens. -/
def fixtureGenerated : List CanonicalBranchNode :=
  [canonicalCenterRoot 1, canonicalRoot 1 0, canonicalRoot 1 2,
   canonicalRoot 1 3, canonicalRoot 1 6,
   fixtureDescendant 3 9, fixtureDescendant 3 4, fixtureDescendant 3 5,
   fixtureDescendant 6 10, fixtureDescendant 6 7, fixtureDescendant 6 8]

def fixtureProfile (node : CanonicalBranchNode) : FrameRuntime.Profile :=
  ⟨node, ⟨node.history⟩, fixtureGenerated⟩

theorem fixture_center_profile :
    FrameRuntime.profile? fixtureMolecule (canonicalCenterRoot 1) =
      some (fixtureProfile (canonicalCenterRoot 1)) := by decide +kernel

theorem fixture_source_profile :
    FrameRuntime.profile? fixtureMolecule (canonicalRoot 1 3) =
      some (fixtureProfile (canonicalRoot 1 3)) := by decide +kernel

theorem fixture_other_profile :
    FrameRuntime.profile? fixtureMolecule (canonicalRoot 1 6) =
      some (fixtureProfile (canonicalRoot 1 6)) := by decide +kernel

def fixtureCenterCursor (atom : Nat) : CanonicalRerootCursor :=
  { node := canonicalRoot 1 atom, previous? := some (canonicalCenterRoot 1) }

def fixtureArmCursor (arm : Nat) (node : CanonicalBranchNode) : CanonicalRerootCursor :=
  { node := node, previous? := some (canonicalRoot 1 arm) }

def fixtureCenterRoots : List CanonicalRerootCursor :=
  [fixtureCenterCursor 0, fixtureCenterCursor 2, fixtureCenterCursor 3, fixtureCenterCursor 6]

def fixtureArmRoots (arm hydrogen bromine iodine : Nat) : List CanonicalRerootCursor :=
  [fixtureArmCursor arm (canonicalCenterRoot 1),
   fixtureArmCursor arm (fixtureDescendant arm hydrogen),
   fixtureArmCursor arm (fixtureDescendant arm bromine),
   fixtureArmCursor arm (fixtureDescendant arm iodine)]

def fixtureArmSorted (arm hydrogen bromine iodine : Nat) : List CanonicalRerootCursor :=
  [fixtureArmCursor arm (fixtureDescendant arm iodine),
   fixtureArmCursor arm (fixtureDescendant arm bromine),
   fixtureArmCursor arm (canonicalCenterRoot 1),
   fixtureArmCursor arm (fixtureDescendant arm hydrogen)]

def fixtureFullSorted : List CanonicalRerootCursor :=
  [fixtureCenterCursor 2, fixtureCenterCursor 0, fixtureCenterCursor 3, fixtureCenterCursor 6]

def fixtureRemovedSorted : List CanonicalRerootCursor :=
  [fixtureCenterCursor 2, fixtureCenterCursor 0, fixtureCenterCursor 6, fixtureCenterCursor 3]

def fixtureOrdinaryDecisions : List OccurrenceComparison :=
  [{ ordering := .gt }, { ordering := .gt }, { ordering := .gt }]

def fixturePseudoDecisions : List OccurrenceComparison :=
  [{ ordering := .gt }, { ordering := .gt }, { ordering := .gt, pseudo := true }]

theorem fixture_center_roots :
    occurrenceLigandFrame? fixtureMolecule (canonicalCenterRoot 1) =
      some fixtureCenterRoots := by decide +kernel

theorem fixture_source_roots :
    occurrenceLigandFrame? fixtureMolecule (canonicalRoot 1 3) =
      some (fixtureArmRoots 3 9 4 5) := by decide +kernel

theorem fixture_other_roots :
    occurrenceLigandFrame? fixtureMolecule (canonicalRoot 1 6) =
      some (fixtureArmRoots 6 10 7 8) := by decide +kernel

theorem fixture_source_sort :
    FramedCompleteRuntime.trackedSortComplete? fixtureMolecule
      (fixtureProfile (canonicalRoot 1 3)) false [] fuel (fixtureArmRoots 3 9 4 5) =
      some (fixtureArmSorted 3 9 4 5, 0) := by decide +kernel

theorem fixture_other_sort :
    FramedCompleteRuntime.trackedSortComplete? fixtureMolecule
      (fixtureProfile (canonicalRoot 1 6)) false [] fuel (fixtureArmRoots 6 10 7 8) =
      some (fixtureArmSorted 6 10 7 8, 0) := by decide +kernel

theorem fixture_source_adjacency :
    (FramedCompleteRuntime.adjacentComplete? fixtureMolecule
      (fixtureProfile (canonicalRoot 1 3)) false [] fuel (fixtureArmSorted 3 9 4 5)).map
      (fun pairs => pairs.map fun pair => pair.decision) =
      some fixtureOrdinaryDecisions := by decide +kernel

theorem fixture_other_adjacency :
    (FramedCompleteRuntime.adjacentComplete? fixtureMolecule
      (fixtureProfile (canonicalRoot 1 6)) false [] fuel (fixtureArmSorted 6 10 7 8)).map
      (fun pairs => pairs.map fun pair => pair.decision) =
      some fixtureOrdinaryDecisions := by decide +kernel

/-- Pure final fields, separated from actual profile/ranking/adjacency observations. -/
def fixtureFinish (node : CanonicalBranchNode) (parity : TetrahedralInputParity)
    (positions : List Nat) (decisions : List OccurrenceComparison) : Option OccurrenceAuxFact :=
  if !(decisions.all fun decision => decision.ordering != Ordering.eq) then none else
    some
      { key := canonicalOccurrenceKey node
        atom := node.atom
        descriptor := descriptorOfParity parity (permutationIsEven positions)
        uppercase := (decisions.filter fun decision => decision.pseudo).length % 2 == 0
        priorityPositions := positions }

/-- A structural evaluator equation from primitive observations. No desired full fact,
ordering law, or legacy/framed equivalence is a premise. -/
theorem fixture_fact_of_observations (mol : RawMolecule) (state : OccurrenceAuxState)
    (steps : Nat) (node : CanonicalBranchNode) (profile : FrameRuntime.Profile)
    (spec : AtomSpec) (parity : TetrahedralInputParity)
    (roots sorted : List CanonicalRerootCursor) (transientPseudoCount : Nat)
    (positions : List Nat) (decisions : List OccurrenceComparison)
    (profileComputed : FrameRuntime.profile? mol node = some profile)
    (atomComputed : mol.atomAt? node.atom = some spec)
    (parityComputed : spec.tetrahedral? = some parity)
    (rootsComputed : occurrenceLigandFrame? mol node = some roots)
    (sortComputed : FramedCompleteRuntime.trackedSortComplete? mol profile false state
      steps roots = some (sorted, transientPseudoCount))
    (positionsComputed : (sorted.mapM fun cursor =>
      ((mol.ligandsWithLonePair node.atom).zipIdx.find?
        fun entry => entry.1 == cursor.node.atom).map Prod.snd) = some positions)
    (adjacencyComputed :
      (FramedCompleteRuntime.adjacentComplete? mol profile false state steps sorted).map
        (fun pairs => pairs.map fun pair => pair.decision) = some decisions) :
    occurrenceFact? mol steps state node = fixtureFinish node parity positions decisions := by
  rw [occurrenceFact?_eq_framed_of_profile_some mol steps state node profile profileComputed,
    framedOccurrenceFact?_eq_complete]
  unfold FramedCompleteRuntime.occurrenceFactComplete?
  simp only [profileComputed, atomComputed, parityComputed, rootsComputed, sortComputed,
    positionsComputed, Bind.bind, Option.bind]
  cases adjacent : FramedCompleteRuntime.adjacentComplete? mol profile false state steps sorted with
  | none =>
      simp only [adjacent, Option.map_none] at adjacencyComputed
      cases adjacencyComputed
  | some pairs =>
      have decisionsEq : (pairs.map fun pair => pair.decision) = decisions := by
        simpa only [adjacent, Option.map_some, Option.some.injEq] using adjacencyComputed
      simp only [decisionsEq, fixtureFinish]

end TetraStereo.Examples.Rule5EssentialDependency
