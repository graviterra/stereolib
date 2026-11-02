import TetraStereo.OneCenter.IUPACP94AssembledSourceProgram
import TetraStereo.OneCenter.IUPACFixedGlobalProductionRefinement
import TetraStereo.KernelOnly

set_option autoImplicit false











namespace TetraStereo.OneCenter

open BlueBookP94
open BlueBookP94.CoordinateTwistInOut
open BlueBookP94.P94MolecularBridgeheadAxisInterior
open BlueBookP94.P94MolecularBicyclicFramework
open BlueBookP94.P94MolecularBridgeSufficiency
open IUPACNormativeProvision

namespace P94AssembledSourceProgram

theorem distinguished_source_structurallyWellFormed
    (distinguished : P94FrozenDistinguishedEntry) :
    distinguished.record.source.StructurallyWellFormed := by
  rw [← distinguished.record.package.ledgerSource]
  exact distinguished.record.package.lonePairLedger.sourceWellFormed

theorem distinguished_evidence_observed
    (distinguished : P94FrozenDistinguishedEntry)
    (member : distinguished ∈ assembledProgram.distinguishedEntries) :
    assembledProgram.policy.EvidenceObserved distinguished.record.source
      distinguished.record.molecule distinguished.entry.evidence := by
  have listed := assembledProgram.distinguishedEntriesListed distinguished member
  exact ⟨distinguished.record, ⟨listed.1, rfl, rfl⟩,
    distinguished.entry, listed.2, rfl⟩

noncomputable def observationOfDistinguished
    (distinguished : P94FrozenDistinguishedEntry)
    (certificate : Option
      (P94InOutCoordinateObservation × P94InOutCoordinateObservation)) :
    P94AuthorityObservation assembledProgram.policy where
  molecule := distinguished.record.molecule
  evidence := distinguished.entry.evidence
  claim := distinguished.entry.claim
  inOutCertificate? := certificate

theorem observationOfDistinguished_valid
    (distinguished : P94FrozenDistinguishedEntry)
    (member : distinguished ∈ assembledProgram.distinguishedEntries)
    (certificate : Option
      (P94InOutCoordinateObservation × P94InOutCoordinateObservation))
    (certificateValid : P94InOutCertificateMatches assembledProgram.policy
      distinguished.record.source distinguished.record.molecule
      distinguished.entry.evidence certificate) :
    (observationOfDistinguished distinguished certificate).ValidFor
      assembledProgram.policy distinguished.record.source := by
  exact ⟨distinguished.record.package.authoritativeStructureAgreement,
    distinguished_evidence_observed distinguished member,
    distinguished.entry.unitValid, distinguished.entry.molecularRolesValid,
    distinguished.entry.matchesEvidence, distinguished.entry.supports, certificateValid⟩

theorem row_nonvacuous_of_distinguished
    (row : Remaining71P94AuthorityRow)
    (distinguished : P94FrozenDistinguishedEntry)
    (member : distinguished ∈ assembledProgram.distinguishedEntries)
    (certificate : Option
      (P94InOutCoordinateObservation × P94InOutCoordinateObservation))
    (certificateValid : P94InOutCertificateMatches assembledProgram.policy
      distinguished.record.source distinguished.record.molecule
      distinguished.entry.evidence certificate)
    (provisionExact : distinguished.entry.claim.provision = row.provision) :
    ∃ input, ∃ observation : (row.reference assembledProgram.policy).Observation,
      input.StructurallyWellFormed ∧
        (row.reference assembledProgram.policy).Applicable input ∧
          (row.reference assembledProgram.policy).Judges input observation := by
  let observation := observationOfDistinguished distinguished certificate
  have judged : (row.reference assembledProgram.policy).Judges
      distinguished.record.source observation :=
    ⟨observationOfDistinguished_valid distinguished member certificate certificateValid,
      provisionExact⟩
  exact ⟨distinguished.record.source, observation,
    distinguished_source_structurallyWellFormed distinguished,
    ⟨observation, judged⟩, judged⟩

/-! ## Stored in/out pair under the finite assembled policy -/

private theorem inOut_record_at :
    assembledProgram.PackageAt
      P94InOutSourceRecord.TopologySpecialization.source
      P94InOutSourceRecord.TopologySpecialization.molecule
      P94InOutSourceRecord.frozenRecord := by
  exact ⟨by simp [assembledProgram, packages], rfl, rfl⟩

private theorem inOut_pair_member :
    P94InOutSourceRecord.TopologySpecialization.inOutCoordinatePair ∈
      P94InOutSourceRecord.frozenRecord.package.inOutCoordinatePairs := by
  simp [P94InOutSourceRecord.frozenRecord,
    P94InOutSourceRecord.TopologySpecialization.sourcePackage]

private theorem inOut_pair_observed :
    assembledProgram.policy.InOutCoordinatePairObserved
      P94InOutSourceRecord.TopologySpecialization.source
      P94InOutSourceRecord.TopologySpecialization.molecule
      P94InOutSourceRecord.TopologySpecialization.inwardCoordinate
      P94InOutSourceRecord.TopologySpecialization.outwardCoordinate := by
  exact ⟨P94InOutSourceRecord.frozenRecord, inOut_record_at,
    P94InOutSourceRecord.TopologySpecialization.inOutCoordinatePair,
    inOut_pair_member, rfl, rfl⟩

private theorem inOut_inward_interior_observed :
    assembledProgram.policy.InOutInteriorWitness
      P94InOutSourceRecord.TopologySpecialization.source
      P94InOutSourceRecord.TopologySpecialization.molecule
      P94InOutSourceRecord.TopologySpecialization.inOutUnit
      P94InOutSourceRecord.TopologySpecialization.inwardCoordinate.framework
      P94InOutSourceRecord.TopologySpecialization.inwardCoordinate.bridgehead
      P94InOutSourceRecord.TopologySpecialization.inwardCoordinate.spatial
      P94InOutSourceRecord.TopologySpecialization.inwardCoordinate.interior := by
  exact ⟨P94InOutSourceRecord.frozenRecord, inOut_record_at,
    P94InOutSourceRecord.TopologySpecialization.inOutCoordinatePair,
    inOut_pair_member, rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩

private theorem inOut_outward_interior_observed :
    assembledProgram.policy.InOutInteriorWitness
      P94InOutSourceRecord.TopologySpecialization.source
      P94InOutSourceRecord.TopologySpecialization.molecule
      P94InOutSourceRecord.TopologySpecialization.inOutUnit
      P94InOutSourceRecord.TopologySpecialization.outwardCoordinate.framework
      P94InOutSourceRecord.TopologySpecialization.outwardCoordinate.bridgehead
      P94InOutSourceRecord.TopologySpecialization.outwardCoordinate.spatial
      P94InOutSourceRecord.TopologySpecialization.outwardCoordinate.interior := by
  exact ⟨P94InOutSourceRecord.frozenRecord, inOut_record_at,
    P94InOutSourceRecord.TopologySpecialization.inOutCoordinatePair,
    inOut_pair_member, rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩

private theorem inOut_graph_judged_to_candidate_policy
    (observation : P94InOutCoordinateObservation)
    (direction : BridgeheadDirection)
    (participant : Nat)
    (participantExact : observation.directedParticipant = .atom participant)
    (interiorObserved : assembledProgram.policy.InOutInteriorWitness
      P94InOutSourceRecord.TopologySpecialization.source
      P94InOutSourceRecord.TopologySpecialization.molecule
      P94InOutSourceRecord.TopologySpecialization.inOutUnit
      observation.framework observation.bridgehead observation.spatial observation.interior)
    (judged : CoordinateInOutDirectionJudgment
      (graphElectronicAxisBridgePremises
        P94InOutSourceRecord.TopologySpecialization.molecule
        P94InOutSourceRecord.TopologySpecialization.ledger)
      P94InOutSourceRecord.TopologySpecialization.molecule
      P94InOutSourceRecord.TopologySpecialization.inOutUnit observation direction) :
    CoordinateInOutDirectionJudgment
      (bridgeDerivedPremises
        (assembledProgram.policy.inOutBasePremises
          P94InOutSourceRecord.TopologySpecialization.source
          P94InOutSourceRecord.TopologySpecialization.molecule))
      P94InOutSourceRecord.TopologySpecialization.molecule
      P94InOutSourceRecord.TopologySpecialization.inOutUnit observation direction := by
  unfold CoordinateInOutDirectionJudgment at judged ⊢
  rw [participantExact] at judged ⊢
  rcases judged with
    ⟨ledgerValid, _interiorValid, participantValid,
      bridgeheadPoint, participantPoint, bridgeheadAt, participantAt, sign⟩
  rcases participantValid with
    ⟨bridgeheadMember, ⟨frameworkValid, bridgeheadValid⟩,
      bridgeheadBounded, participantBounded, participantOutsideUnit,
      participantOutsideFramework, participantBonded⟩
  refine ⟨ledgerValid, ⟨rfl, interiorObserved⟩,
    ⟨bridgeheadMember, ⟨rfl, frameworkValid, bridgeheadValid⟩,
      bridgeheadBounded, participantBounded, participantOutsideUnit, ?_, participantBonded⟩,
    bridgeheadPoint, participantPoint, bridgeheadAt, participantAt, sign⟩
  rintro ⟨_, participantInFramework⟩
  exact participantOutsideFramework participantInFramework

private theorem inOut_inward_policy_judged :
    CoordinateInOutDirectionJudgment
      (bridgeDerivedPremises
        (assembledProgram.policy.inOutBasePremises
          P94InOutSourceRecord.TopologySpecialization.source
          P94InOutSourceRecord.TopologySpecialization.molecule))
      P94InOutSourceRecord.TopologySpecialization.molecule
      P94InOutSourceRecord.TopologySpecialization.inOutUnit
      P94InOutSourceRecord.TopologySpecialization.inwardCoordinate .inward :=
  inOut_graph_judged_to_candidate_policy _ _ 5 rfl
    inOut_inward_interior_observed
    P94InOutSourceRecord.TopologySpecialization.inward_graph_judged

private theorem inOut_outward_policy_judged :
    CoordinateInOutDirectionJudgment
      (bridgeDerivedPremises
        (assembledProgram.policy.inOutBasePremises
          P94InOutSourceRecord.TopologySpecialization.source
          P94InOutSourceRecord.TopologySpecialization.molecule))
      P94InOutSourceRecord.TopologySpecialization.molecule
      P94InOutSourceRecord.TopologySpecialization.inOutUnit
      P94InOutSourceRecord.TopologySpecialization.outwardCoordinate .outward :=
  inOut_graph_judged_to_candidate_policy _ _ 5 rfl
    inOut_outward_interior_observed
    P94InOutSourceRecord.TopologySpecialization.outward_graph_judged

private theorem inOut_bridge_allows_both :
    BridgeAllowsBothDirections
      (assembledProgram.policy.inOutBasePremises
        P94InOutSourceRecord.TopologySpecialization.source
        P94InOutSourceRecord.TopologySpecialization.molecule)
      P94InOutSourceRecord.TopologySpecialization.molecule
      P94InOutSourceRecord.TopologySpecialization.inOutUnit
      P94InOutSourceRecord.TopologySpecialization.thetaFramework := by
  exact ⟨P94InOutSourceRecord.TopologySpecialization.inwardCoordinate,
    P94InOutSourceRecord.TopologySpecialization.outwardCoordinate,
    rfl, rfl, rfl, rfl, inOut_inward_policy_judged, inOut_outward_policy_judged⟩

private theorem inOut_certificate_valid :
    P94ConcreteInOutCertificateValid assembledProgram.policy
      P94InOutSourceRecord.TopologySpecialization.source
      P94InOutSourceRecord.TopologySpecialization.molecule
      P94InOutSourceRecord.TopologySpecialization.inOutRecord
      (some (P94InOutSourceRecord.TopologySpecialization.inwardCoordinate,
        P94InOutSourceRecord.TopologySpecialization.outwardCoordinate)) := by
  refine ⟨P94InOutSourceRecord.TopologySpecialization.inwardCoordinate,
    P94InOutSourceRecord.TopologySpecialization.outwardCoordinate,
    rfl, inOut_pair_observed, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
    P94InOutSourceRecord.TopologySpecialization.thetaFramework_valid,
    P94InOutSourceRecord.TopologySpecialization.thetaFramework_valid,
    inOut_inward_policy_judged, inOut_outward_policy_judged, Iff.rfl, ?_, ?_⟩
  · norm_num [P94InOutSourceRecord.TopologySpecialization.inwardCoordinate,
      P94InOutSourceRecord.TopologySpecialization.inwardSpatial,
      P94InOutSourceRecord.TopologySpecialization.molecule, RawMolecule.atomCount]
  · norm_num [P94InOutSourceRecord.TopologySpecialization.outwardCoordinate,
      P94InOutSourceRecord.TopologySpecialization.outwardSpatial,
      P94InOutSourceRecord.TopologySpecialization.molecule, RawMolecule.atomCount]
  · change True ↔ BridgeAllowsBothDirections
      (assembledProgram.policy.inOutBasePremises
        P94InOutSourceRecord.TopologySpecialization.source
        P94InOutSourceRecord.TopologySpecialization.molecule)
      P94InOutSourceRecord.TopologySpecialization.molecule
      P94InOutSourceRecord.TopologySpecialization.inOutUnit
      P94InOutSourceRecord.TopologySpecialization.thetaFramework
    exact (iff_true_intro inOut_bridge_allows_both).symm
  · change True ↔ BridgeAllowsBothDirections
      (assembledProgram.policy.inOutBasePremises
        P94InOutSourceRecord.TopologySpecialization.source
        P94InOutSourceRecord.TopologySpecialization.molecule)
      P94InOutSourceRecord.TopologySpecialization.molecule
      P94InOutSourceRecord.TopologySpecialization.inOutUnit
      P94InOutSourceRecord.TopologySpecialization.thetaFramework
    exact (iff_true_intro inOut_bridge_allows_both).symm

theorem Remaining71P94AuthorityRow.assembled_candidate_reference_nonvacuous
    (row : Remaining71P94AuthorityRow) :
    ∃ input, ∃ observation : (row.reference assembledProgram.policy).Observation,
      input.StructurallyWellFormed ∧
        (row.reference assembledProgram.policy).Applicable input ∧
          (row.reference assembledProgram.policy).Judges input observation := by
  cases row
  · exact row_nonvacuous_of_distinguished .conformationDefinition
      P94ConformationDefinitionSourceRecord.distinguishedEntry
      (by simp [assembledProgram, distinguishedEntries]) none (by rfl) rfl
  · exact row_nonvacuous_of_distinguished .torsionAngle
      P94TorsionAngleSourceRecord.distinguishedEntry
      (by simp [assembledProgram, distinguishedEntries]) none (by rfl) rfl
  · exact row_nonvacuous_of_distinguished .torsionLonePairs
      P94TorsionElectronicProxySourceRecord.distinguishedEntry
      (by simp [assembledProgram, distinguishedEntries]) none (by rfl) rfl
  · exact row_nonvacuous_of_distinguished .eclipsedStaggeredGauche
      P94EclipsedStaggeredGaucheSourceRecords.distinguishedEntry
      (by simp [assembledProgram, distinguishedEntries]) none (by rfl) rfl
  · exact row_nonvacuous_of_distinguished .trigonalConformations
      P94TrigonalSourceRecord.distinguishedEntry
      (by simp [assembledProgram, distinguishedEntries]) none (by rfl) rfl
  · exact row_nonvacuous_of_distinguished .sCisSTrans
      P94SCisSTransSourceRecord.distinguishedEntry
      (by simp [assembledProgram, distinguishedEntries]) none (by rfl) rfl
  · exact row_nonvacuous_of_distinguished .envelope
      P94EnvelopeSourceRecord.distinguishedEntry
      (by simp [assembledProgram, distinguishedEntries]) none (by rfl) rfl
  · exact row_nonvacuous_of_distinguished .chairBoatTwist
      P94ChairBoatTwistSourceRecord.distinguishedEntry
      (by simp [assembledProgram, distinguishedEntries]) none (by rfl) rfl
  · exact row_nonvacuous_of_distinguished .halfChair
      P94HalfChairSourceRecord.distinguishedEntry
      (by simp [assembledProgram, distinguishedEntries]) none (by rfl) rfl
  · exact row_nonvacuous_of_distinguished .crown crownDistinguishedEntry
      (by simp [assembledProgram, distinguishedEntries]) none (by rfl) rfl
  · exact row_nonvacuous_of_distinguished .tub tubDistinguishedEntry
      (by simp [assembledProgram, distinguishedEntries]) none (by rfl) rfl
  · exact row_nonvacuous_of_distinguished .inOut P94InOutSourceRecord.distinguishedEntry
      (by simp [assembledProgram, distinguishedEntries])
      (some (P94InOutSourceRecord.TopologySpecialization.inwardCoordinate,
        P94InOutSourceRecord.TopologySpecialization.outwardCoordinate))
      inOut_certificate_valid rfl

end P94AssembledSourceProgram

namespace IUPACNormativeProvision

namespace Remaining56P93ReviewedPolicies

def toRemaining71WithP94AssembledCandidate
    (policies : Remaining56P93ReviewedPolicies) : Remaining71ReviewedPolicies where
  p93General := policies.general
  p93Noncarbon := policies.noncarbon
  p93Acyclic := policies.acyclic
  p93Cyclic := policies.cyclic
  p94 := P94AssembledSourceProgram.assembledProgram.policy

def toDescriptorBearingWithP94AssembledCandidate
    (policies : Remaining56P93ReviewedPolicies) : DescriptorBearingReviewedPolicies where
  remaining71 := policies.toRemaining71WithP94AssembledCandidate

end Remaining56P93ReviewedPolicies

theorem assembledGlobalReviewedSemantics_p94AssembledCandidate_nonvacuous
    (policies : Remaining56P93ReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics)
    (row : Remaining71P94AuthorityRow) :
    let globalPolicies := policies.toDescriptorBearingWithP94AssembledCandidate
    ∃ input, ∃ observation :
        ((assembleGlobalReviewedSemantics globalPolicies negative).reviewed.row
          row.provision).reference.Observation,
      (assembleGlobalReviewedSemantics globalPolicies negative).reviewed.ChemicallyAdmitted input ∧
        ((assembleGlobalReviewedSemantics globalPolicies negative).reviewed.row
          row.provision).reference.Applicable input ∧
          ((assembleGlobalReviewedSemantics globalPolicies negative).reviewed.row
            row.provision).reference.Judges input observation := by
  dsimp only
  rcases TetraStereo.OneCenter.P94AssembledSourceProgram.Remaining71P94AuthorityRow.assembled_candidate_reference_nonvacuous row with
    ⟨input, observation, admitted, applicable, judged⟩
  let globalPolicies := policies.toDescriptorBearingWithP94AssembledCandidate
  have referenceEq :
      ((assembleGlobalReviewedSemantics globalPolicies negative).reviewed.row
        row.provision).reference =
          row.reference P94AssembledSourceProgram.assembledProgram.policy := by
    simpa [globalPolicies,
      Remaining56P93ReviewedPolicies.toDescriptorBearingWithP94AssembledCandidate,
      Remaining56P93ReviewedPolicies.toRemaining71WithP94AssembledCandidate] using
        congrArg ReviewedProvisionSemantics.reference
          (globalReviewedSemantics_remaining71P94_exact
            (assembleGlobalReviewedSemantics globalPolicies negative) row)
  have globalAdmitted :
      (assembleGlobalReviewedSemantics globalPolicies negative).reviewed.ChemicallyAdmitted
        input := by
    simpa [assembleGlobalReviewedSemantics, assembledGlobalReviewedTable] using admitted
  let globalObservation := cast
    (congrArg ProvisionReference.Observation referenceEq.symm) observation
  refine ⟨input, globalObservation, globalAdmitted,
    (ProvisionReference.applicable_congr referenceEq _).mpr applicable, ?_⟩
  apply (ProvisionReference.judges_cast_congr
    referenceEq input globalObservation).mpr
  simpa [globalObservation] using judged

noncomputable def IUPACP93CanonicalAssembledP94CandidateDescriptorBearingPolicies :
    DescriptorBearingReviewedPolicies :=
  P93CanonicalSourceProgram.iupacP93CanonicalSourceProgram.compiledPolicies
    |>.toDescriptorBearingWithP94AssembledCandidate

/-! The complete candidate-policy 152-row nonvacuity value is completed below after transporting
the already-frozen P-93 family across the P-94-only policy replacement. -/

private theorem candidate_p93_nonvacuous
    (negative : GlobalNonDescriptorReviewedSemantics)
    (row : Remaining71P93DescriptorKernelRow) :
    let candidatePolicies :=
      IUPACP93CanonicalAssembledP94CandidateDescriptorBearingPolicies
    ∃ input, ∃ observation :
        ((assembleGlobalReviewedSemantics candidatePolicies negative).reviewed.row
          row.provision).reference.Observation,
      (assembleGlobalReviewedSemantics candidatePolicies negative).reviewed.ChemicallyAdmitted input ∧
        ((assembleGlobalReviewedSemantics candidatePolicies negative).reviewed.row
          row.provision).reference.Applicable input ∧
          ((assembleGlobalReviewedSemantics candidatePolicies negative).reviewed.row
            row.provision).reference.Judges input observation := by
  dsimp only
  let sourcePolicies :=
    P93CanonicalSourceProgram.iupacP93CanonicalSourceProgram.compiledPolicies
  let schemaPolicies := sourcePolicies.toDescriptorBearingWithP94Schema
  let candidatePolicies := sourcePolicies.toDescriptorBearingWithP94AssembledCandidate
  let schemaGlobal := assembleGlobalReviewedSemantics schemaPolicies negative
  have schemaMember : row.provision ∈ descriptorBearingReviewedSemanticsSlice.toFinset := by
    rw [descriptorBearingReviewedSemanticsScope_exact]
    exact (List.mem_toFinset.mpr
      ((mem_descriptorAssignmentBearingProvisions_iff row.provision).2
        row.descriptorAssignmentBearing))
  rcases (iupacP93CanonicalGlobalReviewedNonvacuity negative).nonvacuous
      row.provision schemaMember with
    ⟨input, observation, admitted, applicable, judged⟩
  let candidateGlobal := assembleGlobalReviewedSemantics candidatePolicies negative
  have schemaReferenceEq :
      (schemaGlobal.reviewed.row row.provision).reference =
        row.reference schemaPolicies.remaining71 := by
    simpa [schemaGlobal] using
      congrArg ReviewedProvisionSemantics.reference
        (globalReviewedSemantics_remaining71P93_exact schemaGlobal row)
  have candidateReferenceEq :
      (candidateGlobal.reviewed.row row.provision).reference =
        row.reference candidatePolicies.remaining71 := by
    simpa [candidateGlobal] using
      congrArg ReviewedProvisionSemantics.reference
        (globalReviewedSemantics_remaining71P93_exact candidateGlobal row)
  have rowReferencesEqual :
      row.reference candidatePolicies.remaining71 =
        row.reference schemaPolicies.remaining71 := by
    cases row <;> rfl
  have referenceEq :
      (candidateGlobal.reviewed.row row.provision).reference =
        (schemaGlobal.reviewed.row row.provision).reference :=
    candidateReferenceEq.trans (rowReferencesEqual.trans schemaReferenceEq.symm)
  have candidateAdmitted : candidateGlobal.reviewed.ChemicallyAdmitted input := by
    simpa [candidateGlobal, candidatePolicies, schemaGlobal, schemaPolicies,
      sourcePolicies, assembleGlobalReviewedSemantics,
      assembledGlobalReviewedTable] using admitted
  let candidateObservation := cast
    (congrArg ProvisionReference.Observation referenceEq.symm) observation
  refine ⟨input, candidateObservation, candidateAdmitted,
    (ProvisionReference.applicable_congr referenceEq _).mpr applicable, ?_⟩
  apply (ProvisionReference.judges_cast_congr
    referenceEq input candidateObservation).mpr
  simpa [candidateObservation] using judged

noncomputable def iupacP93CanonicalAssembledP94CandidateGlobalReviewedNonvacuity
    (negative : GlobalNonDescriptorReviewedSemantics) :
    DescriptorBearingReviewedNonvacuity
      (parameterizedGlobalReviewedSemantics
        IUPACP93CanonicalAssembledP94CandidateDescriptorBearingPolicies negative) :=
  DescriptorBearingReviewedNonvacuityFamilies.toReviewedNonvacuity
    { primitive35 := parameterizedGlobalReviewedSemantics_primitive35_nonvacuous
        IUPACP93CanonicalAssembledP94CandidateDescriptorBearingPolicies negative
      next54 := parameterizedGlobalReviewedSemantics_next54_nonvacuous
        IUPACP93CanonicalAssembledP94CandidateDescriptorBearingPolicies negative
      remaining71 := by
        intro row
        cases row with
        | p93General child => exact candidate_p93_nonvacuous negative (.general child)
        | p93Noncarbon child => exact candidate_p93_nonvacuous negative (.noncarbon child)
        | p93Acyclic child => exact candidate_p93_nonvacuous negative (.acyclic child)
        | p93Cyclic child => exact candidate_p93_nonvacuous negative (.cyclic child)
        | p94 child =>
            exact assembledGlobalReviewedSemantics_p94AssembledCandidate_nonvacuous
              P93CanonicalSourceProgram.iupacP93CanonicalSourceProgram.compiledPolicies
              negative child
        | authorityData child =>
            exact assembledGlobalReviewedSemantics_authorityData_nonvacuous
              IUPACP93CanonicalAssembledP94CandidateDescriptorBearingPolicies negative child }

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P94AssembledSourceProgram.Remaining71P94AuthorityRow.assembled_candidate_reference_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.assembledGlobalReviewedSemantics_p94AssembledCandidate_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.iupacP93CanonicalAssembledP94CandidateGlobalReviewedNonvacuity
