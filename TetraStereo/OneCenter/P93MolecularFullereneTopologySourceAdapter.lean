import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.ProductionCIPRule1aGraphRealization
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Truthful authoritative-source adapter for fullerene topology cores

The certified fullerene cores deliberately encode cage adjacency with `RawBond.single`; those
records certify the numbered graph, not an authoritative Kekule bond-order assignment.  This
adapter therefore weakens exactly the interactions internal to a designated cage carrier to
`unspecifiedCovalent`.  Every bond with at least one endpoint outside the carrier retains the
ordinary parser-to-semantic translation, including double, triple, aromatic, and directional
single-bond semantics.
-/

namespace TetraStereo.OneCenter

/-- Semantic interpretation of one raw derivative bond relative to its cage carrier. -/
def RawBond.toMolecularFullereneTopologyInteraction
    (carrier : Finset Nat) (bond : RawBond) : SemanticInteraction :=
  if bond.source ∈ carrier ∧ bond.target ∈ carrier then
    { participants := [bond.source, bond.target]
      kind := .unspecifiedCovalent }
  else
    bond.toSemanticInteraction

@[simp] theorem RawBond.toMolecularFullereneTopologyInteraction_participants
    (carrier : Finset Nat) (bond : RawBond) :
    (bond.toMolecularFullereneTopologyInteraction carrier).participants =
      [bond.source, bond.target] := by
  by_cases internal : bond.source ∈ carrier ∧ bond.target ∈ carrier <;>
    simp [RawBond.toMolecularFullereneTopologyInteraction, RawBond.toSemanticInteraction,
      internal]

@[simp] theorem RawBond.toMolecularFullereneTopologyInteraction_wellFormed_iff
    (carrier : Finset Nat) (bond : RawBond) (atomCount : Nat) :
    (bond.toMolecularFullereneTopologyInteraction carrier).WellFormed atomCount ↔
      bond.source < atomCount ∧ bond.target < atomCount ∧ bond.source ≠ bond.target := by
  by_cases internal : bond.source ∈ carrier ∧ bond.target ∈ carrier
  · simp [RawBond.toMolecularFullereneTopologyInteraction, internal,
      SemanticInteraction.WellFormed]
    tauto
  · simp [RawBond.toMolecularFullereneTopologyInteraction, internal]

@[simp] theorem RawBond.toMolecularFullereneTopologyInteraction_internal_kind
    (carrier : Finset Nat) (bond : RawBond)
    (sourcePresent : bond.source ∈ carrier) (targetPresent : bond.target ∈ carrier) :
    (bond.toMolecularFullereneTopologyInteraction carrier).kind =
      .unspecifiedCovalent := by
  simp [RawBond.toMolecularFullereneTopologyInteraction, sourcePresent, targetPresent]

/-- Outside the induced cage, the adapter is literally the standard exact raw-bond conversion. -/
theorem RawBond.toMolecularFullereneTopologyInteraction_nonCage
    (carrier : Finset Nat) (bond : RawBond)
    (notInternal : ¬(bond.source ∈ carrier ∧ bond.target ∈ carrier)) :
    bond.toMolecularFullereneTopologyInteraction carrier = bond.toSemanticInteraction := by
  simp [RawBond.toMolecularFullereneTopologyInteraction, notInternal]

/-- Checked atom conversion followed by the carrier-relative interaction interpretation. -/
def RawMolecule.toMolecularFullereneTopologySemanticMolecule?
    (molecule : RawMolecule) (carrier : Finset Nat) : Option SemanticMolecule := do
  let ordinary ← molecule.toSemanticMolecule?
  some {
    atoms := ordinary.atoms
    interactions := molecule.bonds.map
      (RawBond.toMolecularFullereneTopologyInteraction carrier)
  }

/-- The exact semantic projections produced by the topology adapter. -/
theorem RawMolecule.toMolecularFullereneTopologySemanticMolecule?_exact
    (molecule : RawMolecule) (carrier : Finset Nat) (semantic : SemanticMolecule)
    (converted : molecule.toMolecularFullereneTopologySemanticMolecule? carrier = some semantic) :
    (∀ index,
      listGet? semantic.atoms index =
        (molecule.atomAt? index).bind AtomSpec.toSemanticAtom?) ∧
      semantic.interactions = molecule.bonds.map
        (RawBond.toMolecularFullereneTopologyInteraction carrier) := by
  cases ordinaryObserved : molecule.toSemanticMolecule? with
  | none =>
      simp [RawMolecule.toMolecularFullereneTopologySemanticMolecule?, ordinaryObserved] at converted
  | some ordinary =>
      simp [RawMolecule.toMolecularFullereneTopologySemanticMolecule?, ordinaryObserved] at converted
      subst semantic
      exact ⟨molecule.toSemanticMolecule?_atomAt? ordinary ordinaryObserved, rfl⟩

/-- The adapter neither adds nor removes atom positions. -/
theorem RawMolecule.toMolecularFullereneTopologySemanticMolecule?_atomCount
    (molecule : RawMolecule) (carrier : Finset Nat) (semantic : SemanticMolecule)
    (converted : molecule.toMolecularFullereneTopologySemanticMolecule? carrier = some semantic) :
    semantic.atomCount = molecule.atomCount := by
  cases ordinaryObserved : molecule.toSemanticMolecule? with
  | none =>
      simp [RawMolecule.toMolecularFullereneTopologySemanticMolecule?, ordinaryObserved] at converted
  | some ordinary =>
      have ordinaryCount := molecule.toSemanticMolecule?_atomCount ordinary ordinaryObserved
      simp [RawMolecule.toMolecularFullereneTopologySemanticMolecule?, ordinaryObserved] at converted
      subst semantic
      exact ordinaryCount

/-- Weakening cage bond orders does not change the structural endpoint contract. -/
theorem RawMolecule.toMolecularFullereneTopologySemanticMolecule?_structurallyWellFormed_iff
    (molecule : RawMolecule) (carrier : Finset Nat) (semantic : SemanticMolecule)
    (converted : molecule.toMolecularFullereneTopologySemanticMolecule? carrier = some semantic) :
    semantic.StructurallyWellFormed ↔ molecule.WellFormed := by
  cases ordinaryObserved : molecule.toSemanticMolecule? with
  | none =>
      simp [RawMolecule.toMolecularFullereneTopologySemanticMolecule?, ordinaryObserved] at converted
  | some ordinary =>
      have ordinaryCount := molecule.toSemanticMolecule?_atomCount ordinary ordinaryObserved
      simp [RawMolecule.toMolecularFullereneTopologySemanticMolecule?, ordinaryObserved] at converted
      subst semantic
      constructor
      · intro adaptedWellFormed bond bondPresent
        have interactionPresent :
            bond.toMolecularFullereneTopologyInteraction carrier ∈
              molecule.bonds.map
                (RawBond.toMolecularFullereneTopologyInteraction carrier) :=
          List.mem_map.mpr ⟨bond, bondPresent, rfl⟩
        have interactionChecked :
            (bond.toMolecularFullereneTopologyInteraction carrier).wellFormed?
                ordinary.atomCount = true := by
          apply (List.all_eq_true.mp adaptedWellFormed)
          exact interactionPresent
        have endpoints :
            bond.source < ordinary.atomCount ∧
              bond.target < ordinary.atomCount ∧ bond.source ≠ bond.target :=
          RawBond.toMolecularFullereneTopologyInteraction_wellFormed_iff
            carrier bond ordinary.atomCount |>.mp
              (SemanticInteraction.wellFormed?_eq_true_iff
                (bond.toMolecularFullereneTopologyInteraction carrier)
                ordinary.atomCount |>.mp interactionChecked)
        rw [ordinaryCount] at endpoints
        exact endpoints
      · intro rawWellFormed
        apply List.all_eq_true.mpr
        intro interaction interactionPresent
        obtain ⟨bond, bondPresent, rfl⟩ := List.mem_map.mp interactionPresent
        apply (SemanticInteraction.wellFormed?_eq_true_iff
          (bond.toMolecularFullereneTopologyInteraction carrier) ordinary.atomCount).mpr
        apply (RawBond.toMolecularFullereneTopologyInteraction_wellFormed_iff
          carrier bond ordinary.atomCount).mpr
        have endpoints := rawWellFormed bond bondPresent
        rw [ordinaryCount]
        exact endpoints

/-- Raw positive cage adjacency as represented in the semantic interaction list.  Orientation of
the raw edge record is irrelevant. -/
def SemanticMolecule.MolecularFullereneCageAdjacent
    (semantic : SemanticMolecule) (left right : Nat) : Prop :=
  ∃ interaction ∈ semantic.interactions,
    (interaction.participants = [left, right] ∨
      interaction.participants = [right, left]) ∧
      interaction.kind = .unspecifiedCovalent

/-- For carrier atoms, semantic adjacency is exactly raw positive adjacency; only bond order was
forgotten. -/
theorem RawMolecule.toMolecularFullereneTopologySemanticMolecule?_cageAdjacent_iff
    (molecule : RawMolecule) (carrier : Finset Nat) (semantic : SemanticMolecule)
    (converted : molecule.toMolecularFullereneTopologySemanticMolecule? carrier = some semantic)
    (left right : Nat) (leftPresent : left ∈ carrier) (rightPresent : right ∈ carrier)
    (distinct : left ≠ right) :
    semantic.MolecularFullereneCageAdjacent left right ↔
      0 < molecule.bondOrder left right := by
  rw [molecule.bondOrder_pos_iff_exists_bond distinct]
  have interactionsExact :=
    (molecule.toMolecularFullereneTopologySemanticMolecule?_exact carrier semantic converted).2
  rw [SemanticMolecule.MolecularFullereneCageAdjacent, interactionsExact]
  constructor
  · rintro ⟨interaction, interactionPresent, endpoints, _kind⟩
    obtain ⟨bond, bondPresent, rfl⟩ := List.mem_map.mp interactionPresent
    refine ⟨bond, bondPresent, ?_⟩
    simp only [RawBond.toMolecularFullereneTopologyInteraction_participants] at endpoints
    rcases endpoints with forward | reverse
    · have endpointExact : bond.source = left ∧ bond.target = right := by
        simpa using forward
      simp [RawBond.connects, endpointExact.1, endpointExact.2]
    · have endpointExact : bond.source = right ∧ bond.target = left := by
        simpa using reverse
      simp [RawBond.connects, endpointExact.1, endpointExact.2]
  · rintro ⟨bond, bondPresent, connects⟩
    have endpointCases :
        (bond.source = left ∧ bond.target = right) ∨
          (bond.source = right ∧ bond.target = left) := by
      simpa [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq] using connects
    refine ⟨bond.toMolecularFullereneTopologyInteraction carrier,
      List.mem_map.mpr ⟨bond, bondPresent, rfl⟩, ?_, ?_⟩
    · simp only [RawBond.toMolecularFullereneTopologyInteraction_participants]
      rcases endpointCases with ⟨sourceEq, targetEq⟩ | ⟨sourceEq, targetEq⟩
      · exact Or.inl (by simp [sourceEq, targetEq])
      · exact Or.inr (by simp [sourceEq, targetEq])
    · rcases endpointCases with ⟨sourceEq, targetEq⟩ | ⟨sourceEq, targetEq⟩
      · exact bond.toMolecularFullereneTopologyInteraction_internal_kind carrier
          (sourceEq ▸ leftPresent) (targetEq ▸ rightPresent)
      · exact bond.toMolecularFullereneTopologyInteraction_internal_kind carrier
          (sourceEq ▸ rightPresent) (targetEq ▸ leftPresent)

/-- Every bond that is not wholly internal to the cage occurs with its exact ordinary semantic
chemistry in the converted interaction list. -/
theorem RawMolecule.toMolecularFullereneTopologySemanticMolecule?_nonCageBondExact
    (molecule : RawMolecule) (carrier : Finset Nat) (semantic : SemanticMolecule)
    (converted : molecule.toMolecularFullereneTopologySemanticMolecule? carrier = some semantic)
    (bond : RawBond) (bondPresent : bond ∈ molecule.bonds)
    (notInternal : ¬(bond.source ∈ carrier ∧ bond.target ∈ carrier)) :
    bond.toSemanticInteraction ∈ semantic.interactions := by
  rw [(molecule.toMolecularFullereneTopologySemanticMolecule?_exact
    carrier semantic converted).2]
  apply List.mem_map.mpr
  exact ⟨bond, bondPresent,
    bond.toMolecularFullereneTopologyInteraction_nonCage carrier notInternal⟩

/-- Public source conversion.  The optional exact spatial evidence is copied verbatim; parser
directional bonds and atom parities remain available through the exact parser diagram. -/
def RawMolecule.toMolecularFullereneTopologyAuthoritativeInput?
    (molecule : RawMolecule) (carrier : Finset Nat)
    (spatial? : Option SpatialConfiguration := none) : Option AuthoritativeChemicalInput := do
  let semantic ← molecule.toMolecularFullereneTopologySemanticMolecule? carrier
  some {
    molecule := semantic
    spatial? := spatial?
    diagram? := some molecule.toDiagramConfiguration
  }

/-- Exact representation agreement at the source boundary. -/
def RawMolecule.MolecularFullereneTopologyRepresentationAgreement
    (molecule : RawMolecule) (carrier : Finset Nat)
    (spatial? : Option SpatialConfiguration) (source : AuthoritativeChemicalInput) : Prop :=
  molecule.toMolecularFullereneTopologySemanticMolecule? carrier = some source.molecule ∧
    source.spatial? = spatial? ∧
    source.diagram? = some molecule.toDiagramConfiguration

/-- Successful public conversion satisfies every projection of representation agreement. -/
theorem RawMolecule.toMolecularFullereneTopologyAuthoritativeInput?_exact
    (molecule : RawMolecule) (carrier : Finset Nat)
    (spatial? : Option SpatialConfiguration) (source : AuthoritativeChemicalInput)
    (converted : molecule.toMolecularFullereneTopologyAuthoritativeInput? carrier spatial? =
      some source) :
    molecule.MolecularFullereneTopologyRepresentationAgreement carrier spatial? source := by
  cases semanticObserved :
      molecule.toMolecularFullereneTopologySemanticMolecule? carrier with
  | none =>
      simp [RawMolecule.toMolecularFullereneTopologyAuthoritativeInput?, semanticObserved] at converted
  | some semantic =>
      simp [RawMolecule.toMolecularFullereneTopologyAuthoritativeInput?, semanticObserved] at converted
      subst source
      exact ⟨semanticObserved, rfl, rfl⟩

private theorem diagramBond_indices_of_mem
    (molecule : RawMolecule) (wellFormed : molecule.WellFormed)
    (diagramBond : DiagramBond)
    (present : diagramBond ∈ molecule.toDiagramConfiguration.bonds) :
    diagramBond.source < molecule.atomCount ∧
      diagramBond.target < molecule.atomCount ∧
      diagramBond.source ≠ diagramBond.target := by
  simp only [RawMolecule.toDiagramConfiguration, List.mem_filterMap] at present
  obtain ⟨bond, bondPresent, selected⟩ := present
  have endpoints := wellFormed bond bondPresent
  cases kindObserved : bond.kind with
  | unspecified => simp [kindObserved] at selected
  | single => simp [kindObserved] at selected
  | double => simp [kindObserved] at selected
  | triple => simp [kindObserved] at selected
  | aromatic => simp [kindObserved] at selected
  | up =>
      simp [kindObserved] at selected
      subst diagramBond
      exact endpoints
  | down =>
      simp [kindObserved] at selected
      subst diagramBond
      exact endpoints

private theorem enumerateFrom_index_bound
    {Alpha : Type*} (values : List Alpha) (start : Nat) (indexed : Nat × Alpha)
    (present : indexed ∈ enumerateFrom start values) :
    indexed.1 < start + values.length := by
  induction values generalizing start with
  | nil => simp [enumerateFrom] at present
  | cons head tail inductionHypothesis =>
      simp only [enumerateFrom, List.mem_cons] at present
      rcases present with rfl | tailPresent
      · simp
      · have bound := inductionHypothesis (start + 1) tailPresent
        simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound

private theorem enumerate_index_bound
    {Alpha : Type*} (values : List Alpha) (indexed : Nat × Alpha)
    (present : indexed ∈ enumerate values) : indexed.1 < values.length := by
  simpa [enumerate] using enumerateFrom_index_bound values 0 indexed present

private theorem diagramAtomConfiguration_index_of_mem
    (molecule : RawMolecule) (configuration : DiagramAtomConfiguration)
    (present : configuration ∈ molecule.toDiagramConfiguration.atomConfigurations) :
    configuration.atom < molecule.atomCount := by
  simp only [RawMolecule.toDiagramConfiguration, List.mem_filterMap] at present
  obtain ⟨indexed, indexedPresent, selected⟩ := present
  have indexBound := enumerate_index_bound molecule.atoms indexed indexedPresent
  cases parityObserved : indexed.2.tetrahedral? with
  | none => simp [parityObserved] at selected
  | some parity =>
      simp [parityObserved] at selected
      subst configuration
      simpa [RawMolecule.atomCount] using indexBound

/-- Raw endpoint well-formedness validates the copied parser diagram. -/
private theorem toMolecularFullereneTopologyAuthoritativeInput_diagramWellFormed
    (molecule : RawMolecule) (carrier : Finset Nat) (semantic : SemanticMolecule)
    (converted : molecule.toMolecularFullereneTopologySemanticMolecule? carrier = some semantic)
    (wellFormed : molecule.WellFormed) :
    ({ molecule := semantic
       diagram? := some molecule.toDiagramConfiguration } :
      AuthoritativeChemicalInput).DiagramIndicesWellFormed := by
  have countExact :=
    molecule.toMolecularFullereneTopologySemanticMolecule?_atomCount carrier semantic converted
  simp only [AuthoritativeChemicalInput.DiagramIndicesWellFormed]
  refine ⟨trivial, ?_, ?_⟩
  · simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    intro bond bondPresent
    have endpoints := diagramBond_indices_of_mem molecule wellFormed bond bondPresent
    exact ⟨⟨by simpa [countExact] using endpoints.1,
      by simpa [countExact] using endpoints.2.1⟩,
      endpoints.2.2⟩
  · simp only [List.all_eq_true, decide_eq_true_eq]
    intro configuration configurationPresent
    have bound := diagramAtomConfiguration_index_of_mem molecule configuration configurationPresent
    simpa [countExact] using bound

/-- The full authoritative input is structurally admitted from raw endpoint well-formedness and
the one unavoidable condition on independently supplied spatial evidence. -/
theorem RawMolecule.toMolecularFullereneTopologyAuthoritativeInput?_structurallyWellFormed
    (molecule : RawMolecule) (carrier : Finset Nat)
    (spatial? : Option SpatialConfiguration) (source : AuthoritativeChemicalInput)
    (converted : molecule.toMolecularFullereneTopologyAuthoritativeInput? carrier spatial? =
      some source)
    (wellFormed : molecule.WellFormed)
    (spatialWellFormed : ∀ spatial, spatial? = some spatial →
      spatial.positions.length = molecule.atomCount) :
    source.StructurallyWellFormed := by
  have exact := molecule.toMolecularFullereneTopologyAuthoritativeInput?_exact
    carrier spatial? source converted
  rcases exact with ⟨semanticConverted, sourceSpatial, sourceDiagram⟩
  refine ⟨
    (molecule.toMolecularFullereneTopologySemanticMolecule?_structurallyWellFormed_iff
      carrier source.molecule semanticConverted).2 wellFormed, ?_, ?_⟩
  · rw [AuthoritativeChemicalInput.SpatialIndicesWellFormed, sourceSpatial]
    cases spatialObserved : spatial? with
    | none => trivial
    | some spatial =>
        have lengthExact := spatialWellFormed spatial spatialObserved
        have countExact :=
          molecule.toMolecularFullereneTopologySemanticMolecule?_atomCount
            carrier source.molecule semanticConverted
        simpa [spatialObserved, countExact] using lengthExact
  · rw [AuthoritativeChemicalInput.DiagramIndicesWellFormed, sourceDiagram]
    exact toMolecularFullereneTopologyAuthoritativeInput_diagramWellFormed
      molecule carrier source.molecule semanticConverted wellFormed

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.toMolecularFullereneTopologySemanticMolecule?_exact
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.toMolecularFullereneTopologySemanticMolecule?_structurallyWellFormed_iff
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.toMolecularFullereneTopologySemanticMolecule?_cageAdjacent_iff
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.toMolecularFullereneTopologySemanticMolecule?_nonCageBondExact
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.toMolecularFullereneTopologyAuthoritativeInput?_structurallyWellFormed
