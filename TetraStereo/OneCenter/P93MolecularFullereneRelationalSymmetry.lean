import TetraStereo.OneCenter.P93MolecularFullereneAddendEvidence
import TetraStereo.OneCenter.P93MolecularFullereneFlagExtension

set_option autoImplicit false

/-!
# Graph-backed relational fullerene substitution symmetry

A multiport addend is not merely its set of attachment sites. A cage permutation preserves an
actual derivative only when it extends to a constitutional isomorphism of the corresponding
external addends and the induced site map is exactly the cage permutation. The all-`T` stage is
kept separate and deterministic: the hypothetical common achiral test object is an unlabeled
finite port set of the same denticity, so every port bijection is admissible by definition.
-/

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

namespace MolecularFullereneAddend

/-- Full constitutional isomorphism constrained to induce a specified cage symmetry on every
attachment site. -/
def ConstitutionallyIsomorphicAlong
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (first second : MolecularFullereneAddend) : Prop :=
  ∃ atomEquivalence :
      { atom // atom ∈ first.externalAtoms } ≃ { atom // atom ∈ second.externalAtoms },
    (∀ atom,
      molecule.atomAt? atom.1 = molecule.atomAt? (atomEquivalence atom).1) ∧
    (∀ left right,
      molecule.bondOrder left.1 right.1 =
        molecule.bondOrder (atomEquivalence left).1 (atomEquivalence right).1) ∧
    ∃ siteEquivalence :
        { site // site ∈ first.attachmentSites } ≃
          { site // site ∈ second.attachmentSites },
      (∀ site,
        (siteEquivalence site).1 =
          mapMolecularFullereneCarrierAtom input symmetry site.1) ∧
      ∃ portEquivalence :
          { port // port ∈ first.attachmentPorts } ≃
            { port // port ∈ second.attachmentPorts },
        (∀ port,
          siteEquivalence
              ⟨port.1.1, port_site_mem_attachmentSites port.2⟩ =
            ⟨(portEquivalence port).1.1,
              port_site_mem_attachmentSites (portEquivalence port).2⟩) ∧
        (∀ port,
          ∃ firstEndpoint : port.1.2 ∈ first.externalAtoms,
            ∃ secondEndpoint : (portEquivalence port).1.2 ∈ second.externalAtoms,
              atomEquivalence ⟨port.1.2, firstEndpoint⟩ =
                ⟨(portEquivalence port).1.2, secondEndpoint⟩) ∧
        ∀ port,
          molecule.bondOrder port.1.1 port.1.2 =
            molecule.bondOrder (portEquivalence port).1.1 (portEquivalence port).1.2

theorem constitutionallyIsomorphicAlong_isomorphic
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    {symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)}
    {first second : MolecularFullereneAddend}
    (along : first.ConstitutionallyIsomorphicAlong molecule input symmetry second) :
    first.ConstitutionallyIsomorphic molecule second := by
  rcases along with
    ⟨atomEquivalence, atoms, bonds, siteEquivalence, _agrees, portEquivalence,
      sites, endpoints, attachmentBonds⟩
  exact ⟨atomEquivalence, atoms, bonds, siteEquivalence, portEquivalence,
    sites, endpoints, attachmentBonds⟩

end MolecularFullereneAddend

/-- Typed ownership of an addend by one complete relational evidence family. -/
abbrev MolecularFullereneOwnedAddend
    {molecule : RawMolecule} {carrier : Finset Nat}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule carrier) :=
  { addend // addend ∈ evidence.addends.toFinset }

/-- Actual-pattern preservation requires a bijection of owned addends and a full constitutional
isomorphism along the cage symmetry for every source-to-target image. -/
def MolecularFullereneActualAddendPatternPreserved
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) : Prop :=
  ∃ addendEquivalence :
      MolecularFullereneOwnedAddend evidence ≃ MolecularFullereneOwnedAddend evidence,
    ∀ source : MolecularFullereneOwnedAddend evidence,
      source.1.ConstitutionallyIsomorphicAlong molecule input symmetry
        (addendEquivalence source).1

noncomputable instance molecularFullereneActualAddendPatternPreservedDecidable
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) :
    Decidable (MolecularFullereneActualAddendPatternPreserved
      molecule input evidence symmetry) :=
  Classical.propDecidable _

/-- Deterministic semantics of the common achiral test addend: its port object is an unlabeled
finite set.  Thus a source and target placement are equivalent exactly when some bijection of
their attachment-site subtypes agrees pointwise with the cage symmetry.  Equal denticity is a
consequence of the existence of this equivalence; there is no caller-authored authorization
corpus. -/
def MolecularFullereneUnlabeledSameTestPortEquivalence
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (first second : MolecularFullereneAddend) : Prop :=
  ∃ portEquivalence :
      { site // site ∈ first.attachmentSites } ≃
        { site // site ∈ second.attachmentSites },
    ∀ site,
      (portEquivalence site).1 =
        mapMolecularFullereneCarrierAtom input symmetry site.1

/-- All-`T` preservation requires a bijection of whole-addend placements and, for each image,
the deterministic unlabeled-port equivalence above. Every bijection of equal-cardinality port
sets is admissible by definition, so internal flips neither require nor admit source discretion. -/
def MolecularFullereneSameTestAddendPatternPreserved
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) : Prop :=
  ∃ addendEquivalence :
      MolecularFullereneOwnedAddend evidence ≃ MolecularFullereneOwnedAddend evidence,
    ∀ source : MolecularFullereneOwnedAddend evidence,
      MolecularFullereneUnlabeledSameTestPortEquivalence input symmetry
        source.1 (addendEquivalence source).1

noncomputable instance molecularFullereneSameTestAddendPatternPreservedDecidable
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) :
    Decidable (MolecularFullereneSameTestAddendPatternPreserved
      evidence symmetry) :=
  Classical.propDecidable _

/-- Independent oriented-cage chirality for an exact symmetry-preservation relation. -/
def MolecularFullereneRelationalChiral
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (preserved : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop) : Prop :=
  OrientedMolecularFullereneFaceMapJudgment molecule input ∧
    ¬∃ symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input),
      MolecularFullereneCarrierAutomorphism molecule input symmetry ∧
        MolecularFullereneFaceOrientationReversing input symmetry ∧ preserved symmetry

noncomputable instance molecularFullereneRelationalChiralDecidable
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (preserved : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop) :
    Decidable (MolecularFullereneRelationalChiral molecule input preserved) :=
  Classical.propDecidable _

noncomputable def molecularFullereneRelationalChiral
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (preserved : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop) : Bool :=
  decide (MolecularFullereneRelationalChiral molecule input preserved)

@[simp] theorem molecularFullereneRelationalChiral_eq_true_iff
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (preserved : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop) :
    molecularFullereneRelationalChiral molecule input preserved = true ↔
      MolecularFullereneRelationalChiral molecule input preserved := by
  simp [molecularFullereneRelationalChiral]

/-- Exact finite-certificate replacement of the independent all-permutation definition. -/
theorem molecularFullereneRelationalChiral_iff_certificate
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (preserved : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop)
    (certificate : MolecularFullereneReversingAutomorphismCertificate molecule input) :
    MolecularFullereneRelationalChiral molecule input preserved ↔
      OrientedMolecularFullereneFaceMapJudgment molecule input ∧
        ∀ symmetry ∈ certificate.members, ¬preserved symmetry := by
  unfold MolecularFullereneRelationalChiral
  constructor
  · rintro ⟨oriented, noReversing⟩
    refine ⟨oriented, ?_⟩
    intro symmetry member relationPreserved
    rcases certificate.sound symmetry member with ⟨automorphism, reversing⟩
    exact noReversing ⟨symmetry, automorphism, reversing, relationPreserved⟩
  · rintro ⟨oriented, corpusRejects⟩
    refine ⟨oriented, ?_⟩
    rintro ⟨symmetry, automorphism, reversing, relationPreserved⟩
    exact corpusRejects symmetry
      (certificate.complete symmetry automorphism reversing) relationPreserved

theorem molecularFullereneRelationalChiral_iff_directedEdgeExtension
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (preserved : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop)
    (certificate : MolecularFullereneDirectedEdgeExtensionCertificate molecule input) :
    MolecularFullereneRelationalChiral molecule input preserved ↔
      OrientedMolecularFullereneFaceMapJudgment molecule input ∧
        ∀ symmetry ∈ molecularFullereneDirectedEdgeReversingAutomorphisms
            molecule input certificate, ¬preserved symmetry :=
  molecularFullereneRelationalChiral_iff_certificate molecule input preserved
    (certificate.toReversingCertificate molecule input)

/-- Reuse the existing quadratic-state deduplicated reversing corpus without enumerating carrier
permutations anew. -/
theorem molecularFullereneRelationalChiral_iff_deduplicatedFlagSpanning
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (preserved : Equiv.Perm (MolecularFullereneCarrierAtom input) → Prop)
    (certificate : MolecularFullereneDeduplicatedFlagSpanningCertificate molecule input) :
    MolecularFullereneRelationalChiral molecule input preserved ↔
      OrientedMolecularFullereneFaceMapJudgment molecule input ∧
        ∀ symmetry ∈ molecularFullereneDirectedEdgeReversingAutomorphisms molecule input
            (MolecularFullereneConcreteFlagExtensionCertificate.toReversingDirectedEdgeExtension
              molecule input (certificate.toConcreteFlagExtension molecule input)),
          ¬preserved symmetry :=
  molecularFullereneRelationalChiral_iff_directedEdgeExtension molecule input preserved
    (MolecularFullereneConcreteFlagExtensionCertificate.toReversingDirectedEdgeExtension
      molecule input (certificate.toConcreteFlagExtension molecule input))

abbrev MolecularFullereneActualAddendPatternChiral
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier) : Prop :=
  MolecularFullereneRelationalChiral molecule input
    (MolecularFullereneActualAddendPatternPreserved molecule input evidence)

abbrev MolecularFullereneSameTestAddendPatternChiral
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier) : Prop :=
  MolecularFullereneRelationalChiral molecule input
    (MolecularFullereneSameTestAddendPatternPreserved evidence)

/-- Full five-field derivation. Actual identities use graph-backed isomorphisms along the cage;
all-`T` uses the deterministic unlabeled-port test-addend semantics. -/
noncomputable def deriveMolecularFullereneRelationalSubstitutionTest
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier) :
    FullereneSubstitutionTest :=
  { parentChiral :=
      molecularFullereneColoringChiral molecule input molecularFullereneParentColor
    originalDerivativeChiral := evidence.originalDerivativeChiral
    allSubstituentsReplacedByAchiralTChiral :=
      molecularFullereneRelationalChiral molecule input
        (MolecularFullereneSameTestAddendPatternPreserved evidence)
    substitutionPatternWithActualIdentitiesChiral :=
      molecularFullereneRelationalChiral molecule input
        (MolecularFullereneActualAddendPatternPreserved molecule input evidence)
    hasChiralSubstituent := decide evidence.chiralAddends.Nonempty }

@[simp] theorem deriveMolecularFullereneRelationalSubstitutionTest_parentChiral_iff
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier) :
    (deriveMolecularFullereneRelationalSubstitutionTest molecule input
      evidence).parentChiral = true ↔
      MolecularFullereneColoringChiral molecule input molecularFullereneParentColor := by
  exact molecularFullereneColoringChiral_eq_true_iff molecule input
    molecularFullereneParentColor

@[simp] theorem deriveMolecularFullereneRelationalSubstitutionTest_sameTest_iff
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier) :
    (deriveMolecularFullereneRelationalSubstitutionTest molecule input
      evidence).allSubstituentsReplacedByAchiralTChiral = true ↔
      MolecularFullereneSameTestAddendPatternChiral evidence := by
  exact molecularFullereneRelationalChiral_eq_true_iff molecule input _

@[simp] theorem deriveMolecularFullereneRelationalSubstitutionTest_actualIdentities_iff
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier) :
    (deriveMolecularFullereneRelationalSubstitutionTest molecule input
      evidence).substitutionPatternWithActualIdentitiesChiral = true ↔
      MolecularFullereneActualAddendPatternChiral molecule input evidence := by
  exact molecularFullereneRelationalChiral_eq_true_iff molecule input _

@[simp] theorem deriveMolecularFullereneRelationalSubstitutionTest_hasChiralAddend_iff
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier) :
    (deriveMolecularFullereneRelationalSubstitutionTest molecule input
      evidence).hasChiralSubstituent = true ↔ evidence.chiralAddends.Nonempty := by
  simp [deriveMolecularFullereneRelationalSubstitutionTest]

/-- Molecule-indexed source retaining immutable audited topology, actual graph evidence, and the
row descriptor evidence.  The emitted cage below replaces only the topology package's inert
payload fields; carrier and faces remain definitionally identical. -/
structure RelationalSymmetryDerivedMolecularFullereneConfigurationInput
    (molecule : RawMolecule) where
  topologyInput : MolecularFullereneConfigurationInput
  evidence : MolecularFullereneAddendRelationalEvidence molecule topologyInput.carrier
  descriptorEvidence : FullereneDescriptorEvidence

namespace RelationalSymmetryDerivedMolecularFullereneConfigurationInput

/-- The only emitted substitution test is the result of the graph-backed relational derivation. -/
noncomputable def cage
    {molecule : RawMolecule}
    (source : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule) :
    MolecularFullereneConfigurationInput :=
  { carrier := source.topologyInput.carrier
    faces := source.topologyInput.faces
    substitutionTest := deriveMolecularFullereneRelationalSubstitutionTest
      molecule source.topologyInput source.evidence
    descriptorEvidence := source.descriptorEvidence }

@[simp] theorem cage_carrier
    {molecule : RawMolecule}
    (source : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule) :
    source.cage.carrier = source.topologyInput.carrier := rfl

@[simp] theorem cage_faces
    {molecule : RawMolecule}
    (source : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule) :
    source.cage.faces = source.topologyInput.faces := rfl

@[simp] theorem cage_substitutionTest
    {molecule : RawMolecule}
    (source : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule) :
    source.cage.substitutionTest =
      deriveMolecularFullereneRelationalSubstitutionTest
        molecule source.topologyInput source.evidence := rfl

@[simp] theorem cage_descriptorEvidence
    {molecule : RawMolecule}
    (source : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule) :
    source.cage.descriptorEvidence = source.descriptorEvidence := rfl

end RelationalSymmetryDerivedMolecularFullereneConfigurationInput

def RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment
    (molecule : RawMolecule)
    (source : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule) : Prop :=
  OrientedMolecularFullereneFaceMapJudgment molecule source.cage

noncomputable instance relationalSymmetryDerivedInputJudgmentDecidable
    (molecule : RawMolecule)
    (source : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule) :
    Decidable (RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment
      molecule source) := Classical.propDecidable _

noncomputable def relationalSymmetryDerivedMolecularFullereneConfigurationInput?
    (molecule : RawMolecule)
    (source : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule) :
    Option MolecularFullereneConfigurationInput :=
  if RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule source then
    some source.cage
  else none

@[simp] theorem relationalSymmetryDerivedMolecularFullereneConfigurationInput?_eq_some_iff
    (molecule : RawMolecule)
    (source : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule)
    (cage : MolecularFullereneConfigurationInput) :
    relationalSymmetryDerivedMolecularFullereneConfigurationInput? molecule source = some cage ↔
      RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule source ∧
        cage = source.cage := by
  by_cases valid :
      RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule source
  · simp [relationalSymmetryDerivedMolecularFullereneConfigurationInput?, valid, eq_comm]
  · simp [relationalSymmetryDerivedMolecularFullereneConfigurationInput?, valid]

@[simp] theorem relationalSymmetryDerivedMolecularFullereneConfigurationInput?_eq_none_iff
    (molecule : RawMolecule)
    (source : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule) :
    relationalSymmetryDerivedMolecularFullereneConfigurationInput? molecule source = none ↔
      ¬RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule source := by
  by_cases valid :
      RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule source
  · simp [relationalSymmetryDerivedMolecularFullereneConfigurationInput?, valid]
  · simp [relationalSymmetryDerivedMolecularFullereneConfigurationInput?, valid]

noncomputable def validatedRelationalSymmetryDerivedMolecularFullereneConfigurationInputs
    (molecule : RawMolecule)
    (sources : List (RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule)) :
    List MolecularFullereneConfigurationInput :=
  sources.filterMap (relationalSymmetryDerivedMolecularFullereneConfigurationInput? molecule)

theorem mem_validatedRelationalSymmetryDerivedMolecularFullereneConfigurationInputs_iff
    (molecule : RawMolecule)
    (sources : List (RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule))
    (cage : MolecularFullereneConfigurationInput) :
    cage ∈ validatedRelationalSymmetryDerivedMolecularFullereneConfigurationInputs
        molecule sources ↔
      ∃ source ∈ sources,
        RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule source ∧
          cage = source.cage := by
  simp [validatedRelationalSymmetryDerivedMolecularFullereneConfigurationInputs,
    relationalSymmetryDerivedMolecularFullereneConfigurationInput?_eq_some_iff]

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneRelationalChiral_iff_certificate
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneRelationalChiral_iff_deduplicatedFlagSpanning
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.relationalSymmetryDerivedMolecularFullereneConfigurationInput?_eq_some_iff
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.mem_validatedRelationalSymmetryDerivedMolecularFullereneConfigurationInputs_iff
