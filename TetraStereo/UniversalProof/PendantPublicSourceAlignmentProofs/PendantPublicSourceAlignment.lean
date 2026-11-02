import TetraStereo.UniversalProof.PendantAuxiliaryBatchRecoveryProofs.PendantAuxiliaryBatchRecovery
import TetraStereo.UniversalProof.NonleafSourceParserAlignmentProofs.NonleafSourceParserAlignment
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel

set_option autoImplicit false

namespace TetraStereo.UniversalProof.PendantPublicSourceAlignmentProofs.PendantPublicSourceAlignment

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeOccurrenceFactRecoveryProofs.RuntimeOccurrenceFactRecovery
open TetraStereo.UniversalProof.NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery
open TetraStereo.UniversalProof.NonleafSourceParserAlignmentProofs.NonleafSourceParserAlignment
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
open TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery
open TetraStereo.UniversalProof.PendantAuxiliaryBatchRecoveryProofs.PendantAuxiliaryBatchRecovery
















theorem tagged_site_exists (raw : RawMolecule) (family : PendantFamily raw)
    (atom : Nat) (spec : AtomSpec) (lookup : raw.atomAt? atom = some spec)
    (parity : TetrahedralInputParity) (tag : spec.tetrahedral? = some parity) :
    Nonempty (PendantSite raw atom) :=
  family.taggedSite atom spec lookup (by simp [tag])

theorem tagged_root_bound (raw : RawMolecule) (family : PendantFamily raw)
    (atom : Nat) (spec : AtomSpec) (lookup : raw.atomAt? atom = some spec)
    (parity : TetrahedralInputParity) (tag : spec.tetrahedral? = some parity) :
    atom < raw.atomCount := by
  obtain ⟨site⟩ := tagged_site_exists raw family atom spec lookup parity tag
  exact site.bound

theorem tagged_root_carbon (raw : RawMolecule) (family : PendantFamily raw)
    (atom : Nat) (spec : AtomSpec) (lookup : raw.atomAt? atom = some spec)
    (parity : TetrahedralInputParity) (tag : spec.tetrahedral? = some parity) :
    raw.atomZAt atom = 6 := by
  obtain ⟨site⟩ := tagged_site_exists raw family atom spec lookup parity tag
  exact site.carbon

theorem tagged_four_records (raw : RawMolecule) (family : PendantFamily raw)
    (atom : Nat) (spec : AtomSpec) (lookup : raw.atomAt? atom = some spec)
    (parity : TetrahedralInputParity) (tag : spec.tetrahedral? = some parity) :
    (recordNeighbors raw atom).length = 4 := by
  obtain ⟨site⟩ := tagged_site_exists raw family atom spec lookup parity tag
  exact PendantSite.four raw atom site

/-- Physical domain transport; this constructor contains no source key/sort/output field. -/
def sourceDomainOfSite (raw : RawMolecule) (family : PendantFamily raw) (atom : Nat)
    (site : PendantSite raw atom)
    (incidentKinds : ∀ bond ∈ raw.bonds,
      bond.source = atom ∨ bond.target = atom → bond.kind = .single) :
    SourceAtomicDomain raw atom :=
  ⟨PendantSite.atomic_domain raw family.well atom site, incidentKinds⟩

/-- GENERAL actual multitag public/source assignment. Source keys, tracked ordering, written
slots, adjacent comparisons and the complete runtime auxiliary state are internally derived. -/
theorem actual_public_formal_alignment (raw : RawMolecule) (family : PendantFamily raw)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement raw source)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (incidentKinds : ∀ bond ∈ raw.bonds,
      bond.source = center.1.val ∨ bond.target = center.1.val → bond.kind = .single)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (spec : AtomSpec) (lookup : raw.atomAt? center.1.val = some spec)
    (parity : TetrahedralInputParity) (tag : spec.tetrahedral? = some parity)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (runtimeFuel : Nat) (enough : raw.atomCount + 1 ≤ runtimeFuel) :
    ∃ positions descriptor,
      tetrahedralOccurrenceFact? raw runtimeFuel center.1.val =
        some (publicFact center.1.val (actualAuxiliaryState raw center.1.val runtimeFuel)
          positions descriptor) ∧
      constitutionParserRichDescriptor? raw source agreement family.written
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
        (2 * (carrierFuel + 1)) = some (.chiral descriptor) ∧
      ConstitutionParserRichDescriptorMeaning raw source agreement family.written
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
        (2 * (carrierFuel + 1)) (.chiral descriptor) ∧
      descriptor = RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven positions) := by
  obtain ⟨site⟩ := tagged_site_exists raw family center.1.val spec lookup parity tag
  let domain := sourceDomainOfSite raw family center.1.val site incidentKinds
  let state := actualAuxiliaryState raw center.1.val runtimeFuel
  obtain ⟨result, positions, descriptor, frameComputed, sortComputed, positionsComputed,
      formula, parserComputed, meaning, _⟩ := actual_runtime_formal_descriptor_transport
    raw source agreement family.written carrierFuel center domain
    (PendantSite.four raw center.1.val site) noDouble spec lookup parity tag view state runtimeFuel
  obtain ⟨actual, actualComputed, permutation, sorted, _⟩ := actual_generated_sort
    raw center.1.val domain.atomic state runtimeFuel
  have equal : actual = result := Option.some.inj (actualComputed.symm.trans sortComputed)
  subst actual
  obtain ⟨decisions, decisionsComputed, strict, pseudo, _⟩ := actual_observed_adjacent
    raw state runtimeFuel result.1
    (fun cursor member => actual_root_observed raw center.1.val domain.atomic cursor
      (permutation.mem_iff.mp member)) sorted
  have localComputed := actual_fact_of_program_bindings raw center.1.val runtimeFuel state
    spec parity lookup tag result positions decisions descriptor frameComputed sortComputed
    positionsComputed decisionsComputed strict pseudo formula
    (actual_root_observed raw center.1.val domain.atomic)
    (actual_root_distinct_ranks raw center.1.val domain.atomic)
  have auxiliaryComputed := actual_auxiliary_build raw family center.1.val runtimeFuel
    site.bound site.carbon enough
  have publicComputed : tetrahedralOccurrenceFact? raw runtimeFuel center.1.val =
      some (publicFact center.1.val state positions descriptor) := by
    unfold tetrahedralOccurrenceFact? tetrahedralOccurrenceFactAuthoritative?
    change (do
      let actualState ← buildOccurrenceAuxStateFullyAuthoritative? raw runtimeFuel center.1.val
      let actualFact ← occurrenceFactAuthoritative? raw runtimeFuel actualState (canonicalCenterRoot center.1.val)
      some ({ atom := center.1.val, descriptor := actualFact.descriptor, uppercase := actualFact.uppercase, evidenceSize := max 1 actualState.length, decisiveRule? := none, descriptorDependentPairs := actualState.length, priorityPositions := actualFact.priorityPositions } : RawDescriptorFact)) = _
    dsimp only [state] at localComputed ⊢
    simp [auxiliaryComputed, localComputed, publicFact, recoveredFact]
  exact ⟨positions, descriptor, publicComputed, parserComputed, meaning, formula⟩

/-- OWN scheduled source model, not a caller-provided state or label. -/
noncomputable def ownState (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement raw source) (written : raw.WrittenNeighborExact)
    (carrierFuel : Nat) : source.AromaticCanonicalAuxiliaryState carrierFuel :=
  constitutionParserRichScheduledState raw source agreement written carrierFuel
    (2 * (carrierFuel + 1))

theorem ownState_cipModel (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement raw source) (written : raw.WrittenNeighborExact)
    (carrierFuel : Nat) :
    (source.aromaticCanonicalOccurrenceSystem
      (constitutionParserRichAuxiliarySemantics raw source agreement written carrierFuel
        (2 * (carrierFuel + 1)))).CIPModel (ownState raw source agreement written carrierFuel) :=
  constitutionParserRichScheduledState_cipModel raw source agreement written carrierFuel
    (2 * (carrierFuel + 1))

/-- The actual public output and the SAME source's internally computed scheduled label agree,
retaining the independent source meaning at that model's actual dependency view. -/
theorem actual_public_own_scheduled_alignment (raw : RawMolecule) (family : PendantFamily raw)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement raw source)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (incidentKinds : ∀ bond ∈ raw.bonds,
      bond.source = center.1.val ∨ bond.target = center.1.val → bond.kind = .single)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (spec : AtomSpec) (lookup : raw.atomAt? center.1.val = some spec)
    (parity : TetrahedralInputParity) (tag : spec.tetrahedral? = some parity)
    (runtimeFuel : Nat) (enough : raw.atomCount + 1 ≤ runtimeFuel) :
    ∃ positions descriptor,
      tetrahedralOccurrenceFact? raw runtimeFuel center.1.val =
        some (publicFact center.1.val (actualAuxiliaryState raw center.1.val runtimeFuel)
          positions descriptor) ∧
      ownState raw source agreement family.written carrierFuel
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) = some (.chiral descriptor) ∧
      ConstitutionParserRichDescriptorMeaning raw source agreement family.written
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)
        (source.aromaticCanonicalDependencyView
          (ownState raw source agreement family.written carrierFuel)
          (source.aromaticCanonicalFinalOccurrence carrierFuel center))
        (2 * (carrierFuel + 1)) (.chiral descriptor) ∧
      descriptor = RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven positions) := by
  let state := ownState raw source agreement family.written carrierFuel
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  obtain ⟨positions, descriptor, publicComputed, parserComputed, meaning, formula⟩ :=
    actual_public_formal_alignment raw family source agreement carrierFuel center incidentKinds
      noDouble spec lookup parity tag (source.aromaticCanonicalDependencyView state target)
      runtimeFuel enough
  have evaluated := constitutionParserRichModel_evaluates raw source agreement family.written
    state (ownState_cipModel raw source agreement family.written carrierFuel) target
  exact ⟨positions, descriptor, publicComputed, evaluated.symm.trans parserComputed, meaning, formula⟩

end TetraStereo.UniversalProof.PendantPublicSourceAlignmentProofs.PendantPublicSourceAlignment
