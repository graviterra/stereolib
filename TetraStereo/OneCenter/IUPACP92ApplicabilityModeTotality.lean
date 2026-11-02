import TetraStereo.OneCenter.IUPACNext54P92FoundationalReviewedSemantics
import TetraStereo.OneCenter.IUPACNext54P92DigraphRule1aReviewedSemantics
import TetraStereo.OneCenter.IUPACPrimitive35Interpreter

set_option autoImplicit false

namespace TetraStereo.OneCenter.IUPACNormativeProvision

/-!
# Total classification of P-92 applicability modes

P-92 contains three semantically different kinds of applicability.  Definitions and scalar rule
schemas are input-invariant source relations.  Digraph and Rule-1a feature clauses require a
source-anchored molecular witness.  The Rules-4b/5 family requires a builder-free canonical
molecular comparison witness.  This module freezes the exact 29/11/3 partition so that a universal
schema relation cannot be mistaken for a missing chemical filter.
-/

/-- The three exact applicability modes represented by the 43 P-92 provisions. -/
inductive P92ApplicabilityMode where
  | inputInvariantSourceSchema
  | sourceFeatureWitness
  | canonicalMolecularWitness
  deriving DecidableEq, Repr

/-- Twenty-one foundational definitions plus eight source-level scalar rule schemas. -/
def p92InputInvariantSchemaProvisions : List IUPACNormativeProvision :=
  p92FoundationalSemanticsSlice ++
    [ .p92Rule1aAtomicNumber
    , .p92Rule1bDuplicateProximity
    , .p92Rule2IsotopeMass
    , .p92Rule3Geometry
    , .p92Rule3SeqCisTrans
    , .p92Rule3Priority
    , .p92Rule4aUnitKind
    , .p92Rule4cPseudoasymmetry
    ]

/-- The eleven clauses whose reviewed applicability is existence of a source-anchored feature
witness. -/
def p92FeatureWitnessProvisions : List IUPACNormativeProvision :=
  p92DigraphAndRule1aSemanticsSlice

/-- The three Rules-4b/5 projections whose applicability is existence of a canonical molecular
comparison witness. -/
def p92CanonicalMolecularWitnessProvisions : List IUPACNormativeProvision :=
  Rule45CanonicalProvisionFamily.all.map Rule45CanonicalProvisionFamily.provision

@[simp] theorem p92InputInvariantSchemaProvisions_length :
    p92InputInvariantSchemaProvisions.length = 29 := by decide

@[simp] theorem p92FeatureWitnessProvisions_length :
    p92FeatureWitnessProvisions.length = 11 := by decide

@[simp] theorem p92CanonicalMolecularWitnessProvisions_length :
    p92CanonicalMolecularWitnessProvisions.length = 3 := by decide

/-- The concatenated 29/11/3 partition contains no duplicate row across or within modes. -/
theorem p92ApplicabilityMode_partition_nodup :
    (p92InputInvariantSchemaProvisions ++ p92FeatureWitnessProvisions ++
      p92CanonicalMolecularWitnessProvisions).Nodup := by
  decide

/-- Executable total classifier on the P-92 scope; non-P-92 rows return `none`. -/
def p92ApplicabilityMode? (provision : IUPACNormativeProvision) :
    Option P92ApplicabilityMode :=
  if provision ∈ p92InputInvariantSchemaProvisions then
    some .inputInvariantSourceSchema
  else if provision ∈ p92FeatureWitnessProvisions then
    some .sourceFeatureWitness
  else if provision ∈ p92CanonicalMolecularWitnessProvisions then
    some .canonicalMolecularWitness
  else none

/-- The three modes cover exactly the manifest's 43 P-92 rows, with no foreign provision. -/
theorem p92ApplicabilityMode_partition_exact :
    (p92InputInvariantSchemaProvisions ++ p92FeatureWitnessProvisions ++
      p92CanonicalMolecularWitnessProvisions).toFinset =
        p92SourceProvisions.toFinset := by
  decide

/-- A row is classified exactly when it belongs to the complete P-92 source inventory. -/
theorem p92ApplicabilityMode?_isSome_iff_mem_p92SourceProvisions
    (provision : IUPACNormativeProvision) :
    (p92ApplicabilityMode? provision).isSome = true ↔
      provision ∈ p92SourceProvisions := by
  have classified :
      (p92ApplicabilityMode? provision).isSome = true ↔
        provision ∈ p92InputInvariantSchemaProvisions ∨
          provision ∈ p92FeatureWitnessProvisions ∨
            provision ∈ p92CanonicalMolecularWitnessProvisions := by
    by_cases schema : provision ∈ p92InputInvariantSchemaProvisions
    · simp [p92ApplicabilityMode?, schema]
    · by_cases feature : provision ∈ p92FeatureWitnessProvisions
      · simp [p92ApplicabilityMode?, schema, feature]
      · by_cases canonical : provision ∈ p92CanonicalMolecularWitnessProvisions
        · simp [p92ApplicabilityMode?, schema, feature, canonical]
        · simp [p92ApplicabilityMode?, schema, feature, canonical]
  rw [classified]
  have partitionMembership :
      (provision ∈ p92InputInvariantSchemaProvisions ∨
          provision ∈ p92FeatureWitnessProvisions ∨
            provision ∈ p92CanonicalMolecularWitnessProvisions) ↔
        provision ∈
          (p92InputInvariantSchemaProvisions ++ p92FeatureWitnessProvisions ++
            p92CanonicalMolecularWitnessProvisions).toFinset := by
    simp
  rw [partitionMembership, p92ApplicabilityMode_partition_exact]
  simp

/-- Every foundational row is deliberately a source schema, not an omitted molecular feature
test. -/
@[simp] theorem foundational_applicability_mode
    (row : Next54P92FoundationalAuthorityRow) :
    p92ApplicabilityMode? row.provision = some .inputInvariantSourceSchema := by
  cases row <;> decide

/-- Every digraph/Rule-1a row uses the already proved source-feature witness relation. -/
@[simp] theorem digraphRule1a_applicability_mode
    (row : Next54P92DigraphRule1aAuthorityRow) :
    p92ApplicabilityMode? row.provision = some .sourceFeatureWitness := by
  cases row <;> decide

/-- Each canonical Rules-4b/5 projection uses molecular canonical-comparison applicability. -/
@[simp] theorem rule45_applicability_mode
    (family : Rule45CanonicalProvisionFamily) :
    p92ApplicabilityMode? family.provision = some .canonicalMolecularWitness := by
  cases family <;> decide


theorem foundational_applicable_iff_true
    (row : Next54P92FoundationalAuthorityRow)
    (input : AuthoritativeChemicalInput) :
    row.reference.Applicable input ↔ True := by
  cases row <;> rfl

/-- Rules-4b/5 applicability is exactly existence of a canonical-complete observation, never an
unconditional scalar schema. -/
theorem rule45_applicable_iff_exists_canonical_complete
    (family : Rule45CanonicalProvisionFamily)
    (input : AuthoritativeChemicalInput) :
    family.completeReference.Applicable input ↔
      ∃ observation : family.completeReference.Observation,
        family.completeReference.Judges input observation :=
  Iff.rfl

end TetraStereo.OneCenter.IUPACNormativeProvision
