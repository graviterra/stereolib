import TetraStereo.OneCenter.IUPACP92ApplicabilityModeTotality

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-!
# Evidence-carrying totality of P-92 applicability semantics

The mode classifier proves the exact 29/11/3 partition.  This module strengthens that result from
a tag to a dependent authority row.  Every one of the 43 P-92 catalog provisions has one unique
row carrying its exact independent `ProvisionReference`; no default reference or catch-all
applicability relation is used.
-/

/-- The eight P-92 scalar schemas in the primitive reviewed table.  The three Rules-4b/5 rows are
kept separate because their applicability is molecular rather than input-invariant. -/
inductive P92ScalarSchemaAuthorityRow where
  | rule1aAtomicNumber
  | rule1bDuplicateProximity
  | rule2IsotopeMass
  | rule3Geometry
  | rule3SeqCisTrans
  | rule3Priority
  | rule4aUnitKind
  | rule4cPseudoasymmetry
  deriving DecidableEq, Repr

namespace P92ScalarSchemaAuthorityRow

def all : List P92ScalarSchemaAuthorityRow :=
  [ .rule1aAtomicNumber
  , .rule1bDuplicateProximity
  , .rule2IsotopeMass
  , .rule3Geometry
  , .rule3SeqCisTrans
  , .rule3Priority
  , .rule4aUnitKind
  , .rule4cPseudoasymmetry
  ]

def provision : P92ScalarSchemaAuthorityRow → IUPACNormativeProvision
  | .rule1aAtomicNumber => .p92Rule1aAtomicNumber
  | .rule1bDuplicateProximity => .p92Rule1bDuplicateProximity
  | .rule2IsotopeMass => .p92Rule2IsotopeMass
  | .rule3Geometry => .p92Rule3Geometry
  | .rule3SeqCisTrans => .p92Rule3SeqCisTrans
  | .rule3Priority => .p92Rule3Priority
  | .rule4aUnitKind => .p92Rule4aUnitKind
  | .rule4cPseudoasymmetry => .p92Rule4cPseudoasymmetry

def reference : P92ScalarSchemaAuthorityRow → ProvisionReference
  | .rule1aAtomicNumber => p92Rule1aAtomicNumberReference
  | .rule1bDuplicateProximity => p92Rule1bDuplicateProximityReference
  | .rule2IsotopeMass => p92Rule2IsotopeMassReference
  | .rule3Geometry => p92Rule3GeometryReference
  | .rule3SeqCisTrans => p92Rule3SeqCisTransReference
  | .rule3Priority => p92Rule3PriorityReference
  | .rule4aUnitKind => p92Rule4aUnitKindReference
  | .rule4cPseudoasymmetry => p92Rule4cPseudoasymmetryReference

@[simp] theorem all_length : all.length = 8 := by rfl

theorem all_nodup : all.Nodup := by decide

theorem provision_injective : Function.Injective provision := by
  intro left right equal
  cases left <;> cases right <;> simp_all [provision]



@[simp] theorem applicable_iff_true
    (row : P92ScalarSchemaAuthorityRow)
    (input : AuthoritativeChemicalInput) :
    row.reference.Applicable input ↔ True := by
  cases row <;> rfl

end P92ScalarSchemaAuthorityRow

/-- One typed applicability-semantics row for every P-92 provision. -/
inductive P92ApplicabilityAuthorityRow where
  | foundational (row : Next54P92FoundationalAuthorityRow)
  | feature (row : Next54P92DigraphRule1aAuthorityRow)
  | scalar (row : P92ScalarSchemaAuthorityRow)
  | canonical (family : Rule45CanonicalProvisionFamily)
  deriving DecidableEq, Repr

namespace P92ApplicabilityAuthorityRow

/-- The eleven whole-rule rows in their exact source-manifest order. -/
def ruleRows : List P92ApplicabilityAuthorityRow :=
  [ .scalar .rule1aAtomicNumber
  , .scalar .rule1bDuplicateProximity
  , .scalar .rule2IsotopeMass
  , .scalar .rule3Geometry
  , .scalar .rule3SeqCisTrans
  , .scalar .rule3Priority
  , .scalar .rule4aUnitKind
  , .canonical .rule4bLikeUnlike
  , .canonical .rule4bPairingMethodology
  , .scalar .rule4cPseudoasymmetry
  , .canonical .rule5Enantiomorph
  ]

/-- Exact 43-row typed table, preserving source-manifest order. -/
def all : List P92ApplicabilityAuthorityRow :=
  Next54P92FoundationalAuthorityRow.all.map .foundational ++
    Next54P92DigraphRule1aAuthorityRow.all.map .feature ++ ruleRows

def provision : P92ApplicabilityAuthorityRow → IUPACNormativeProvision
  | .foundational row => row.provision
  | .feature row => row.provision
  | .scalar row => row.provision
  | .canonical family => family.provision

/-- The exact independent reviewed reference carried by a typed P-92 row. -/
def reference : P92ApplicabilityAuthorityRow → ProvisionReference
  | .foundational row => row.reference
  | .feature row => row.reference
  | .scalar row => row.reference
  | .canonical family => family.completeReference

def mode : P92ApplicabilityAuthorityRow → P92ApplicabilityMode
  | .foundational _ | .scalar _ => .inputInvariantSourceSchema
  | .feature _ => .sourceFeatureWitness
  | .canonical _ => .canonicalMolecularWitness

@[simp] theorem all_length : all.length = 43 := by decide

theorem all_nodup : all.Nodup := by decide

/-- The typed row table is not merely equinumerous with P-92; it is the exact ordered manifest. -/
theorem all_provisions_exact : all.map provision = p92SourceProvisions := by
  rfl

/-- Every typed P-92 row occurs in the exact table. -/
@[simp] theorem mem_all (row : P92ApplicabilityAuthorityRow) : row ∈ all := by
  cases row with
  | foundational row =>
      cases row <;>
        simp [all, Next54P92FoundationalAuthorityRow.all]
  | feature row =>
      cases row <;>
        simp [all, Next54P92DigraphRule1aAuthorityRow.all]
  | scalar row =>
      cases row <;>
        simp [all, Next54P92FoundationalAuthorityRow.all,
          Next54P92DigraphRule1aAuthorityRow.all, ruleRows]
  | canonical family =>
      cases family <;>
        simp [all, Next54P92FoundationalAuthorityRow.all,
          Next54P92DigraphRule1aAuthorityRow.all, ruleRows]

theorem provision_injective : Function.Injective provision := by
  intro left right equal
  have mappedNodup : (all.map provision).Nodup := by
    rw [all_provisions_exact]
    decide
  exact List.inj_on_of_nodup_map mappedNodup (mem_all left) (mem_all right) equal

/-- Every catalog P-92 provision has exactly one dependent row and therefore exactly one selected
independent applicability reference. -/
theorem existsUnique_of_mem_p92SourceProvisions
    {target : IUPACNormativeProvision}
    (member : target ∈ p92SourceProvisions) :
    ∃! row : P92ApplicabilityAuthorityRow, row.provision = target := by
  have typedMember : target ∈ all.map provision := by
    rw [all_provisions_exact]
    exact member
  obtain ⟨row, _rowMember, rowProvision⟩ := List.mem_map.mp typedMember
  refine ⟨row, rowProvision, ?_⟩
  intro other otherProvision
  apply provision_injective
  exact otherProvision.trans rowProvision.symm

/-- The evidence-carrying row and the prior executable mode classifier agree exactly. -/
@[simp] theorem mode_classifier_exact (row : P92ApplicabilityAuthorityRow) :
    p92ApplicabilityMode? row.provision = some row.mode := by
  cases row with
  | foundational row => exact foundational_applicability_mode row
  | feature row => exact digraphRule1a_applicability_mode row
  | scalar row => cases row <;> decide
  | canonical family => exact rule45_applicability_mode family

/-- Every successful independent judgment carries enough evidence to establish its row-specific
applicability predicate. -/
theorem applicable_of_judged
    (row : P92ApplicabilityAuthorityRow)
    (input : AuthoritativeChemicalInput)
    (observation : row.reference.Observation)
    (judged : row.reference.Judges input observation) :
    row.reference.Applicable input := by
  cases row with
  | foundational foundational =>
      exact (foundational_applicable_iff_true foundational input).mpr trivial
  | feature feature =>
      exact feature.applicable_of_judged input observation judged
  | scalar scalar =>
      exact (scalar.applicable_iff_true input).mpr trivial
  | canonical family =>
      exact ⟨observation, judged⟩

end P92ApplicabilityAuthorityRow

namespace Next54P92DigraphRule1aAuthorityRow

/-- Negative applicability for a feature row is exact absence of every source-anchored feature
witness, rather than parser or analyzer failure. -/
theorem not_applicable_iff_forall_not_applicabilityWitness
    (row : Next54P92DigraphRule1aAuthorityRow)
    (input : AuthoritativeChemicalInput) :
    ¬ row.reference.Applicable input ↔
      ∀ observation : row.reference.Observation,
        ¬ row.applicabilityWitness input observation := by
  rw [row.applicable_iff_exists_applicabilityWitness input]
  simp

end Next54P92DigraphRule1aAuthorityRow

namespace Rule45CanonicalProvisionFamily

/-- Negative Rules-4b/5 applicability is exact absence of every canonical-complete molecular
comparison witness. -/
theorem not_applicable_iff_forall_not_canonical_complete
    (family : Rule45CanonicalProvisionFamily)
    (input : AuthoritativeChemicalInput) :
    ¬ family.completeReference.Applicable input ↔
      ∀ observation : family.completeReference.Observation,
        ¬ family.completeReference.Judges input observation := by
  cases family <;> simp [completeReference]

end Rule45CanonicalProvisionFamily
end IUPACNormativeProvision
end TetraStereo.OneCenter
