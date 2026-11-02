import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondElectronicInventoryExactReadiness
import TetraStereo.OneCenter.ExplicitHydrogenDoubleBondEndpointCount

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace AuthoritativeChemicalInput

/-!
# Parser and explicit-hydrogen refinement into endpoint electronic inventories

The parser embedding creates closed-shell semantic atoms: its source syntax has no radical field,
and the semantic conversion sets the unpaired-electron count to zero.  On a fully materialized
ordinary-double-bond endpoint, all two nonpartner positions are therefore represented atoms.  This
module proves that the corresponding all-zero virtual-position inventory is canonical and feeds it
through the stronger electronic-inventory exactness theorem.
-/

/-- Every canonical atom in a source has no unpaired electron. -/
def AromaticCanonicalAtomsClosedShell (source : AuthoritativeChemicalInput) : Prop :=
  ∀ atom : source.AromaticCanonicalAtom,
    (source.molecule.atoms.get atom).unpairedElectrons = 0

/-- The inventory of a fully materialized closed-shell endpoint. -/
def representedOnlyElectronicInventory :
    AromaticCanonicalRule3EndpointElectronicInventory where
  implicitProtia := 0
  lonePairs := 0
  vacancies := 0
  unpairedElectronPositions := 0

@[simp] theorem representedOnlyElectronicInventory_totalNonrepresentedPositions :
    representedOnlyElectronicInventory.totalNonrepresentedPositions = 0 := by
  rfl

/-- Fully represented closed-shell endpoints canonically generate a total electronic-inventory
source without directional records supplied by hand. -/
def representedOnlyElectronicInventorySource
    (source : AuthoritativeChemicalInput)
    (fullyRepresented : source.FullyRepresentedCanonicalIndividualDoubleBondEndpoints)
    (closedShell : source.AromaticCanonicalAtomsClosedShell) :
    source.AromaticCanonicalRule3EndpointElectronicInventorySource where
  inventory := fun _endpoint _partner => representedOnlyElectronicInventory
  canonical := by
    intro endpoint partner directed
    unfold CanonicalAromaticCanonicalRule3EndpointElectronicInventory
    constructor
    · simpa [representedOnlyElectronicInventory] using
        fullyRepresented endpoint partner directed
    · simpa [representedOnlyElectronicInventory] using (closedShell endpoint).symm

/-- The generated map literally returns the represented-only completion. -/
theorem electronicInventoryCompletionMap_representedOnly_eq_some
    (source : AuthoritativeChemicalInput)
    (fullyRepresented : source.FullyRepresentedCanonicalIndividualDoubleBondEndpoints)
    (closedShell : source.AromaticCanonicalAtomsClosedShell)
    (endpoint partner : source.AromaticCanonicalAtom) :
    source.electronicInventoryCompletionMap
        (source.representedOnlyElectronicInventorySource fullyRepresented closedShell)
        endpoint partner = some .representedOnly := by
  apply (source.electronicInventoryCompletionMap_eq_some_iff
    (source.representedOnlyElectronicInventorySource fullyRepresented closedShell)
    endpoint partner .representedOnly).mpr
  simp [representedOnlyElectronicInventorySource, representedOnlyElectronicInventory,
    AromaticCanonicalRule3EndpointElectronicInventorySupports,
    AromaticCanonicalRule3EndpointCompletion.implicitProtiumCount,
    AromaticCanonicalRule3EndpointCompletion.lonePairCount]

end AuthoritativeChemicalInput

namespace AtomSpec

/-- Every atom admitted by the current parser embedding becomes a closed-shell semantic atom. -/
theorem toSemanticAtom?_unpairedElectrons_eq_zero
    (spec : AtomSpec) (atom : SemanticAtom)
    (converted : spec.toSemanticAtom? = some atom) :
    atom.unpairedElectrons = 0 := by
  unfold AtomSpec.toSemanticAtom? at converted
  cases elementObserved : spec.element.toPeriodic? with
  | none => simp [elementObserved] at converted
  | some element =>
      simp [elementObserved] at converted
      subst atom
      rfl

end AtomSpec

namespace RawMolecule

/-- Whole-molecule parser conversion produces a closed-shell semantic source at every atom. -/
theorem toSemanticMolecule?_aromaticCanonicalAtomsClosedShell
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule) :
    source.AromaticCanonicalAtomsClosedShell := by
  intro atom
  have indexed := molecule.toSemanticMolecule?_atomAt?
    source.molecule converted atom.val
  have semanticLookup := listGet?_eq_some_get source.molecule.atoms atom
  rw [semanticLookup] at indexed
  cases rawObserved : molecule.atomAt? atom.val with
  | none => simp [rawObserved] at indexed
  | some spec =>
      rw [rawObserved] at indexed
      simp only [Option.bind_some] at indexed
      exact spec.toSemanticAtom?_unpairedElectrons_eq_zero
        (source.molecule.atoms.get atom) indexed.symm

/-- A materialized parser endpoint compiles directly to the canonical represented-only
electronic-inventory source. -/
def electronicInventorySourceOfMaterializedParser
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (materialized :
      molecule.MaterializedCanonicalIndividualDoubleBondEndpoints source converted) :
    source.AromaticCanonicalRule3EndpointElectronicInventorySource :=
  source.representedOnlyElectronicInventorySource
    (molecule.fullyRepresentedCanonicalIndividualDoubleBondEndpoints_of_materialized
      source converted writtenExact resolved materialized)
    (molecule.toSemanticMolecule?_aromaticCanonicalAtomsClosedShell source converted)

/-- Production explicit-hydrogen materialization on the proved carbon-fill domain generates the
canonical electronic-inventory source without endpoint annotations. -/
def electronicInventorySourceOfCarbonFilledMaterializedParser
    (molecule : RawMolecule) (admitted : molecule.StereochemicalAdmissible)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.withExplicitHydrogens.toSemanticMolecule? = some source.molecule)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (eligible : molecule.OriginalDoubleBondEndpointsCarbonFilled) :
    source.AromaticCanonicalRule3EndpointElectronicInventorySource :=
  molecule.withExplicitHydrogens.electronicInventorySourceOfMaterializedParser
    source converted molecule.withExplicitHydrogens_writtenNeighborExact
    (molecule.withExplicitHydrogens_preserves_noUnspecified resolved)
    (molecule.withExplicitHydrogens_materializedCanonicalIndividualDoubleBondEndpoints
      admitted source converted
      (molecule.carbonFilledCanonicalIndividualDoubleBondEndpoints_of_originalDoubleBonds
        source converted eligible))

/-- Actual inventory-aware ordinary-double-bond analyzer for the production carbon materializer. -/
noncomputable def analyzeOrdinaryDoubleBondsOfCarbonFilledMaterializedParser
    (molecule : RawMolecule) (admitted : molecule.StereochemicalAdmissible)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.withExplicitHydrogens.toSemanticMolecule? = some source.molecule)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (eligible : molecule.OriginalDoubleBondEndpointsCarbonFilled)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    List source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment :=
  source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory
    carrierFuel viewAt
    (molecule.electronicInventorySourceOfCarbonFilledMaterializedParser
      admitted source converted resolved eligible)

/-- Membership of the materialized-parser analyzer is exactly its independent inventory-aware
canonical judgment. -/
theorem mem_analyzeOrdinaryDoubleBondsOfCarbonFilledMaterializedParser_iff_canonical
    (molecule : RawMolecule) (admitted : molecule.StereochemicalAdmissible)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.withExplicitHydrogens.toSemanticMolecule? = some source.molecule)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (eligible : molecule.OriginalDoubleBondEndpointsCarbonFilled)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    assignment ∈ molecule.analyzeOrdinaryDoubleBondsOfCarbonFilledMaterializedParser
        admitted source converted resolved eligible carrierFuel viewAt ↔
      ∃ bond,
        source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
          carrierFuel
          (molecule.electronicInventorySourceOfCarbonFilledMaterializedParser
            admitted source converted resolved eligible)
          bond (viewAt bond.left) (viewAt bond.right) assignment := by
  unfold analyzeOrdinaryDoubleBondsOfCarbonFilledMaterializedParser
  exact
    source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory_iff_canonical
      carrierFuel viewAt
      (molecule.electronicInventorySourceOfCarbonFilledMaterializedParser
        admitted source converted resolved eligible) assignment

theorem analyzeOrdinaryDoubleBondsOfCarbonFilledMaterializedParser_nodup
    (molecule : RawMolecule) (admitted : molecule.StereochemicalAdmissible)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.withExplicitHydrogens.toSemanticMolecule? = some source.molecule)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (eligible : molecule.OriginalDoubleBondEndpointsCarbonFilled)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    (molecule.analyzeOrdinaryDoubleBondsOfCarbonFilledMaterializedParser
      admitted source converted resolved eligible carrierFuel viewAt).Nodup := by
  unfold analyzeOrdinaryDoubleBondsOfCarbonFilledMaterializedParser
  exact
    source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory_nodup
      carrierFuel viewAt
      (molecule.electronicInventorySourceOfCarbonFilledMaterializedParser
        admitted source converted resolved eligible)

/-- Every retained carbon-domain ordinary double bond is either present exactly once or receives
the exhaustive inventory-aware refusal classification. -/
theorem every_carbonFilledMaterializedParserOrdinaryDoubleBond_exact_success_or_refusal
    (molecule : RawMolecule) (admitted : molecule.StereochemicalAdmissible)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.withExplicitHydrogens.toSemanticMolecule? = some source.molecule)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (eligible : molecule.OriginalDoubleBondEndpointsCarbonFilled)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      (source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
          carrierFuel
          (molecule.electronicInventorySourceOfCarbonFilledMaterializedParser
            admitted source converted resolved eligible)
          bond (viewAt bond.left) (viewAt bond.right) ∧
        ∃! assignment,
          assignment ∈ molecule.analyzeOrdinaryDoubleBondsOfCarbonFilledMaterializedParser
            admitted source converted resolved eligible carrierFuel viewAt ∧
          assignment.bond = bond) ∨
      (source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalRefusal
          carrierFuel
          (molecule.electronicInventorySourceOfCarbonFilledMaterializedParser
            admitted source converted resolved eligible)
          bond (viewAt bond.left) (viewAt bond.right) ∧
        source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?
          carrierFuel
          (molecule.electronicInventorySourceOfCarbonFilledMaterializedParser
            admitted source converted resolved eligible)
          bond (viewAt bond.left) (viewAt bond.right) = none) := by
  unfold analyzeOrdinaryDoubleBondsOfCarbonFilledMaterializedParser
  exact source.every_aromaticCanonicalOrdinaryDoubleBond_electronicInventory_exact_success_or_refusal
    carrierFuel viewAt
    (molecule.electronicInventorySourceOfCarbonFilledMaterializedParser
      admitted source converted resolved eligible)

/-- Independent same-assignment parser judgment for the carbon-filled materialized ordinary-
double-bond route.  It combines exact source electronic/spatial semantics with an original raw
order-two bond record on the identical unordered endpoint pair. -/
def CarbonFilledMaterializedParserOrdinaryDoubleBondAssignmentJudgment
    (molecule : RawMolecule) (admitted : molecule.StereochemicalAdmissible)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.withExplicitHydrogens.toSemanticMolecule? = some source.molecule)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (eligible : molecule.OriginalDoubleBondEndpointsCarbonFilled)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) : Prop :=
  assignment.bond = bond ∧
    source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
      carrierFuel
      (molecule.electronicInventorySourceOfCarbonFilledMaterializedParser
        admitted source converted resolved eligible)
      bond (viewAt bond.left) (viewAt bond.right) assignment ∧
    ∃ rawBond ∈ molecule.bonds,
      rawBond.kind = .double ∧
        rawBond.connects bond.left.val bond.right.val = true

/-- Exact parser-backed success boundary for one ordinary double bond.  Inventory-aware canonical
readiness is equivalent to one unique emitted assignment carrying both the independent complete
endpoint/geometry/descriptor judgment and provenance in an original raw double-bond record. -/
theorem existsUnique_mem_analyzeOrdinaryDoubleBondsOfCarbonFilledMaterializedParser_parserBacked_iff_readiness
    (molecule : RawMolecule) (admitted : molecule.StereochemicalAdmissible)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.withExplicitHydrogens.toSemanticMolecule? = some source.molecule)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (eligible : molecule.OriginalDoubleBondEndpointsCarbonFilled)
    (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    (∃! assignment,
        assignment ∈ molecule.analyzeOrdinaryDoubleBondsOfCarbonFilledMaterializedParser
            admitted source converted resolved eligible carrierFuel viewAt ∧
          molecule.CarbonFilledMaterializedParserOrdinaryDoubleBondAssignmentJudgment
            admitted source converted resolved eligible carrierFuel viewAt bond assignment) ↔
      source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
        carrierFuel
        (molecule.electronicInventorySourceOfCarbonFilledMaterializedParser
          admitted source converted resolved eligible)
        bond (viewAt bond.left) (viewAt bond.right) := by
  constructor
  · rintro ⟨assignment, property, _unique⟩
    exact ⟨assignment, property.2.2.1⟩
  · intro ready
    have baseUnique :
        ∃! assignment,
          assignment ∈ molecule.analyzeOrdinaryDoubleBondsOfCarbonFilledMaterializedParser
              admitted source converted resolved eligible carrierFuel viewAt ∧
            assignment.bond = bond := by
      simpa [analyzeOrdinaryDoubleBondsOfCarbonFilledMaterializedParser] using
        (source.existsUnique_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory_iff_readiness
          carrierFuel viewAt
          (molecule.electronicInventorySourceOfCarbonFilledMaterializedParser
            admitted source converted resolved eligible) bond).mpr ready
    obtain ⟨assignment, ⟨present, assignmentBond⟩, unique⟩ := baseUnique
    obtain ⟨rawBond, materializedPresent, rawDouble, rawConnects⟩ :=
      rawDoubleBond_of_aromaticCanonicalOrdinaryDoubleBond
        molecule.withExplicitHydrogens source converted bond.ordinary
    have originalPresent : rawBond ∈ molecule.bonds :=
      molecule.withExplicitHydrogens_doubleBond_mem_original
        rawBond materializedPresent rawDouble
    obtain ⟨observedBond, observedCanonical⟩ :=
      (molecule.mem_analyzeOrdinaryDoubleBondsOfCarbonFilledMaterializedParser_iff_canonical
        admitted source converted resolved eligible carrierFuel viewAt assignment).mp present
    have observedAssignmentBond : assignment.bond = observedBond :=
      observedCanonical.1.sound.1
    have observedBondIdentity : observedBond = bond :=
      observedAssignmentBond.symm.trans assignmentBond
    subst observedBond
    have canonicalAtBond :
        source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
          carrierFuel
          (molecule.electronicInventorySourceOfCarbonFilledMaterializedParser
            admitted source converted resolved eligible)
          bond (viewAt bond.left) (viewAt bond.right) assignment := by
      rw [assignmentBond] at observedCanonical
      exact observedCanonical
    refine ⟨assignment,
      ⟨present, assignmentBond, canonicalAtBond,
        rawBond, originalPresent, rawDouble, rawConnects⟩, ?_⟩
    intro other otherProperty
    exact unique other ⟨otherProperty.1, otherProperty.2.1⟩

end RawMolecule
end TetraStereo.OneCenter
