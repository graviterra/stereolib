import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCanonicalSourceProgram

set_option autoImplicit false

/-!
# Reusable proof-carrying source-meaning entry constructors

These constructors depend only on the canonical source-program interface.  Domain modules can
therefore package real total functions, predicates, and relations without importing an unrelated
semantic corpus.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorSourceMeaningConstructor

def witnessInput : AuthoritativeChemicalInput where
  molecule := { atoms := [], interactions := [] }

theorem witnessInput_structurallyWellFormed : witnessInput.StructurallyWellFormed := by
  simp [witnessInput, AuthoritativeChemicalInput.StructurallyWellFormed,
    SemanticMolecule.StructurallyWellFormed,
    AuthoritativeChemicalInput.SpatialIndicesWellFormed,
    AuthoritativeChemicalInput.DiagramIndicesWellFormed]

/-- A functional observation records both the source-domain input and the reported semantic
result.  The row relation fixes the source input and evaluates the independent source function. -/
structure FunctionalObservation (Context Result : Type) where
  context : Context
  reported : Result

def functionalReference {Context Result : Type} (meaning : Context → Result) :
    OperationProvisionReference .sourceMeaning where
  toReference :=
    { Observation := FunctionalObservation Context Result
      Applicable := fun input => input.StructurallyWellFormed
      Judges := fun _input observation =>
        observation.reported = meaning observation.context }

def functionalEntry {Context Result : Type}
    (provision : IUPACNormativeProvision) (expected : Context)
    (meaning : Context → Result) : GlobalNonDescriptorSourceMeaningEntry where
  provision := provision
  reference := functionalReference meaning
  admittedJudgment := ⟨witnessInput,
    { context := expected, reported := meaning expected },
    witnessInput_structurallyWellFormed, witnessInput_structurallyWellFormed, rfl⟩

/-- Predicate rows retain the source predicate itself and require a proof of the chosen witness. -/
def predicateReference {Context : Type} (meaning : Context → Prop) :
    OperationProvisionReference .sourceMeaning where
  toReference :=
    { Observation := Context
      Applicable := fun input => input.StructurallyWellFormed
      Judges := fun _input observation => meaning observation }

def predicateEntry {Context : Type}
    (provision : IUPACNormativeProvision) (expected : Context) (meaning : Context → Prop)
    (judged : meaning expected) : GlobalNonDescriptorSourceMeaningEntry where
  provision := provision
  reference := predicateReference meaning
  admittedJudgment := ⟨witnessInput, expected, witnessInput_structurallyWellFormed,
    witnessInput_structurallyWellFormed, judged⟩

def relationalReference {Observation : Type} (judges : Observation → Prop) :
    OperationProvisionReference .sourceMeaning where
  toReference :=
    { Observation := Observation
      Applicable := fun input => input.StructurallyWellFormed
      Judges := fun _input observation => judges observation }

def relationalEntry {Observation : Type}
    (provision : IUPACNormativeProvision) (witness : Observation)
    (judges : Observation → Prop) (judged : judges witness) :
    GlobalNonDescriptorSourceMeaningEntry where
  provision := provision
  reference := relationalReference judges
  admittedJudgment := ⟨witnessInput, witness, witnessInput_structurallyWellFormed,
    witnessInput_structurallyWellFormed, judged⟩

/-- An indexed table provision exposes the complete result of its existing total source function. -/
def rowResultEntry {Context Result : Type}
    (provision : IUPACNormativeProvision) (row : Context) (meaning : Context → Result) :
    GlobalNonDescriptorSourceMeaningEntry :=
  relationalEntry provision (meaning row) (fun reported => reported = meaning row) rfl

end GlobalNonDescriptorSourceMeaningConstructor
end IUPACNormativeProvision
end TetraStereo.OneCenter
