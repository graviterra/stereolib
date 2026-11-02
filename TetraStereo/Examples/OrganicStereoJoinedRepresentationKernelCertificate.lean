/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OrganicStereoFiniteClassicalDescription
import TetraStereo.OneCenter.OrganicStereoFiniteClassicalDescriptionRecovery
import TetraStereo.OneCenter.OrganicStereoHeterogeneousSamples
import TetraStereo.OneCenter.OrganicStereoAuthoritativeSourceBridge
import TetraStereo.OneCenter.OrganicStereoAuthoritativeInformationIngress
import TetraStereo.OneCenter.OrganicStereoElectronicDescriptionIngress
import TetraStereo.OneCenter.OrganicStereoElectronicStateAttachment
import TetraStereo.OneCenter.OrganicStereoPathDescriptionIngress
import TetraStereo.OneCenter.OrganicStereoPathStateAttachment
import TetraStereo.OneCenter.OrganicStereoBandDescriptionIngress
import TetraStereo.OneCenter.OrganicStereoBandStateAttachment
import TetraStereo.OneCenter.OrganicStereoFrameAnnotations
import TetraStereo.OneCenter.OrganicStereoSourceBoundResidueAssembly

set_option autoImplicit false






















namespace TetraStereo
namespace OneCenter

open OrganicStereoIndependentElectronicEncoding
open OrganicStereoIndependentBandEncoding
open OrganicStereoElectronicSites

/-! ## Joined whole-state record: both inverses, whole-set recovery and frames -/

section JoinedRepresentation

variable {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
variable (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
  (eB : B ≃ Fin (Fintype.card B))

/-- Decoding an encoded whole description recovers the original record exactly. -/
example (description : FiniteClassicalStereoDescription V E B) :
    decodeDescription eV eE eB (encodeDescription eV eE eB description) = description :=
  decodeDescription_encodeDescription eV eE eB description

/-- Encoding a decoded payload recovers the payload exactly. -/
example (encoded : EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B)) :
    encodeDescription eV eE eB (decodeDescription eV eE eB encoded) = encoded :=
  encodeDescription_decodeDescription eV eE eB encoded

/-- Whole-set recovery for an arbitrary set of whole records. -/
example (descriptions : Set (FiniteClassicalStereoDescription V E B)) :
    decodeDescription eV eE eB '' encodeDescriptionSet eV eE eB descriptions = descriptions :=
  decodeDescription_image_encodeDescriptionSet eV eE eB descriptions

/-- The ordered frame list is recovered exactly, including order and duplicates. -/
example (description : FiniteClassicalStereoDescription V E B) :
    (decodeDescription eV eE eB (encodeDescription eV eE eB description)).frames =
      description.frames :=
  decodeDescription_encodeDescription_frames eV eE eB description

/-! ## Whole-information recovery and nonemptiness -/

/-- Decoding encoded information recovers the entire joint possible set. -/
example (info : FiniteClassicalInformation V E B) :
    FiniteClassicalInformation.decodeInformation eV eE eB
        (FiniteClassicalInformation.encodeInformation eV eE eB info) = info :=
  FiniteClassicalInformation.decodeInformation_encodeInformation eV eE eB info

/-- Encoding decoded information recovers the entire joint possible set. -/
example (info : FiniteClassicalInformation (Fin (Fintype.card V)) (Fin (Fintype.card E))
    (Fin (Fintype.card B))) :
    FiniteClassicalInformation.encodeInformation eV eE eB
        (FiniteClassicalInformation.decodeInformation eV eE eB info) = info :=
  FiniteClassicalInformation.encodeInformation_decodeInformation eV eE eB info

end JoinedRepresentation

/-! ## Heterogeneous samples: complete sample and whole-set recovery -/

section HeterogeneousSamples

variable {I : Type*} [Fintype I]
variable (shape : OrganicStereoHeterogeneousSamples.Shape I)
variable (idx : OrganicStereoHeterogeneousSamples.Indexing shape)

/-- The complete heterogeneous sample round trip. -/
example (s : OrganicStereoHeterogeneousSamples.HeterogeneousSample I shape) :
    OrganicStereoHeterogeneousSamples.decode shape idx
        (OrganicStereoHeterogeneousSamples.encode shape idx s) = s :=
  OrganicStereoHeterogeneousSamples.decode_encode shape idx s

/-- Encoding then decoding a whole uncertain sample recovers every correlated record. -/
example (U : OrganicStereoHeterogeneousSamples.UncertainSample I shape) :
    OrganicStereoHeterogeneousSamples.UncertainSample.decodeSet shape idx
        (OrganicStereoHeterogeneousSamples.UncertainSample.encodeSet shape idx U) = U :=
  OrganicStereoHeterogeneousSamples.UncertainSample.decodeSet_encodeSet shape idx U

end HeterogeneousSamples

/-! ## Authoritative source ingress: exact round trip for every certified input -/

/-- Every certified authoritative input re-encodes to exactly the stored input. -/
example (certified : CertifiedAuthoritativeChemicalInput) :
    OrganicFiniteSource.encode
        (CertifiedAuthoritativeChemicalInput.decode certified)
        (identityEnumeration certified.input.molecule.atomCount) = certified.input :=
  CertifiedAuthoritativeChemicalInput.encode_decode certified

/-! ## Completion ingress: original-source projection and arbitrary absent-spatial data -/

/-- Every completion of a source projects to exactly that source. -/
example {V : Type*} [DecidableEq V] [Fintype V] (source : OrganicFiniteSource V)
    {state : WholeState V (Fin 0) (Fin 0)} (member : state ∈ completions source) :
    sourceOfState state = source :=
  sourceOfState_of_mem_completions member

/-- When spatial data is absent, any real conformation occurs in a completion. -/
example (certified : CertifiedAuthoritativeChemicalInput)
    (absent : certified.input.spatial? = none)
    (conformation : MolecularConformation (Fin certified.input.molecule.atomCount)) :
    ∃ state ∈ completions (CertifiedAuthoritativeChemicalInput.decode certified),
      state.conformation = conformation :=
  CertifiedAuthoritativeChemicalInput.exists_completion_of_absent_spatial
    certified absent conformation

/-! ## Electronic ingress and electronic-state attachment -/

section ElectronicIngress

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {graph : FiniteAtomInteractionHypergraph V}
variable (conformation : MolecularConformation V)
variable (source : IndependentElectronicSiteSource graph)
variable (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)

/-- The electronic ingress state recovers the supplied independent source exactly. -/
example :
    toIndependentElectronicSiteSource
        (OrganicStereoElectronicDescriptionIngress.ingressState conformation source assignment)
        (OrganicStereoElectronicDescriptionIngress.ingressChannel source assignment) rfl =
      source :=
  OrganicStereoElectronicDescriptionIngress.ingressState_toIndependentElectronicSiteSource
    conformation source assignment

end ElectronicIngress

section ElectronicAttachment

variable {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
variable (state : WholeState V E B)
variable (source : IndependentElectronicSiteSource state.graph)
variable (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)

/-- Electronic attachment recovers the complete supplied evidence assignment. -/
example :
    electronicAssignment
        (OrganicStereoElectronicStateAttachment.attachElectronic state source assignment)
        (OrganicStereoElectronicDescriptionIngress.ingressChannel source assignment) rfl =
      assignment :=
  OrganicStereoElectronicStateAttachment.attachElectronic_electronicAssignment
    state source assignment

end ElectronicAttachment

/-! ## Path ingress and path-state attachment -/

section PathIngress

variable {V E : Type*} [DecidableEq V] [Fintype V] [Fintype E]
variable (data : IndependentBondPathData V E)

/-- The path ingress state recovers the whole independent record, including all proof fields. -/
example (valid : PathGeometryValid data.toWholeState) :
    toIndependentBondPathData data.toWholeState valid = data :=
  toIndependentBondPathData_toWholeState data valid

end PathIngress

section PathAttachment

variable {V E NewE B : Type*} [DecidableEq V] [Fintype V] [Fintype E] [Fintype NewE]
  [Fintype B]
variable (state : WholeState V E B) (input : IndependentBondPathData V NewE)
variable (graph_eq : input.graph = state.graph)
variable (conformation_eq : input.conformation = state.conformation)

/-- Attachment recovers the whole supplied independent path record. -/
example (valid : PathGeometryValid
    (attachIndependentBondPathData state input graph_eq conformation_eq)) :
    toIndependentBondPathData
        (attachIndependentBondPathData state input graph_eq conformation_eq) valid = input :=
  toIndependentBondPathData_attachIndependentBondPathData state input graph_eq conformation_eq
    valid

/-- Every oriented endpoint and every arc is the supplied path annotation, edge by edge. -/
example (edge : NewE) :
    ((attachIndependentBondPathData state input graph_eq conformation_eq).paths edge).source =
        input.source edge ∧
      ((attachIndependentBondPathData state input graph_eq conformation_eq).paths edge).target =
        input.target edge ∧
      ((attachIndependentBondPathData state input graph_eq conformation_eq).paths edge).arc =
        input.arc edge :=
  ⟨attachIndependentBondPathData_paths_source state input graph_eq conformation_eq edge,
    attachIndependentBondPathData_paths_target state input graph_eq conformation_eq edge,
    attachIndependentBondPathData_paths_arc state input graph_eq conformation_eq edge⟩

/-- The attached state satisfies the domain geometry predicate and retains bands, electronic data
and frames: a coexistence statement, not a metadata-only equation. -/
example :
    let attached := attachIndependentBondPathData state input graph_eq conformation_eq
    PathGeometryValid attached ∧
      toIndependentBondPathData attached
          (pathGeometryValid_attachIndependentBondPathData state input graph_eq
            conformation_eq) = input ∧
        attached.bandFamily = state.bandFamily ∧
          attached.electronic? = state.electronic? ∧
            attached.frames = state.frames :=
  attachIndependentBondPathData_coexistence_derived state input graph_eq conformation_eq

end PathAttachment

/-! ## Band ingress and band-state attachment -/

section BandIngress

variable {V : Type} [DecidableEq V] [Fintype V]
variable (input : IndependentBandAttachment V)

/-- The band ingress recovers the whole independent band attachment exactly. -/
example :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    toIndependentBandAttachment
        (OrganicStereoBandDescriptionIngress.ofIndependentBandAttachment input) = input :=
  OrganicStereoBandDescriptionIngress.toIndependentBandAttachment_ofIndependentBandAttachment input

end BandIngress

section BandAttachment

variable {V E B : Type} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
variable (state : WholeState V E B) (input : IndependentBandAttachment V)
variable (graph_eq : input.graph = state.graph)
variable (conformation_eq : input.conformation = state.conformation)

/-- Band attachment to an arbitrary state recovers the whole supplied band attachment. -/
example :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    toIndependentBandAttachment
        (OrganicStereoBandStateAttachment.attachIndependentBands state input graph_eq
          conformation_eq) = input :=
  OrganicStereoBandStateAttachment.toIndependentBandAttachment_attachIndependentBands
    state input graph_eq conformation_eq

/-- The attached band family carries the input's exact atom and parameter maps. -/
example (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((OrganicStereoBandStateAttachment.attachIndependentBands state input graph_eq
        conformation_eq).bandFamily band).atom = input.atom band ∧
      ((OrganicStereoBandStateAttachment.attachIndependentBands state input graph_eq
        conformation_eq).bandFamily band).parameter = input.parameter band :=
  ⟨OrganicStereoBandStateAttachment.attachIndependentBands_bandFamily_atom state input
      graph_eq conformation_eq band,
    OrganicStereoBandStateAttachment.attachIndependentBands_bandFamily_parameter state input
      graph_eq conformation_eq band⟩

/-- Off-band atoms keep their exact real position under band attachment. -/
example (v : V) (offBand : OrganicStereoBandStateAttachment.OffBand input v) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (OrganicStereoBandStateAttachment.attachIndependentBands state input graph_eq
      conformation_eq).conformation v = state.conformation v :=
  OrganicStereoBandStateAttachment.attachIndependentBands_offband_conformation state input
    graph_eq conformation_eq v offBand

end BandAttachment

/-! ## Source-bound residue assembly: full decoded-certificate reconstruction -/

section SourceBoundResidue

variable {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
variable {Locant : Type*}
variable (codec : LocantCodec Locant) (eV : V ≃ Fin (Fintype.card V))
variable (state : WholeState V E B)
variable (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
variable (cover : LocantCover ledger)

/-- The attached channel's annotation decodes to exactly the supplied ledger's view. -/
example :
    decodeView? codec (encodedAtomEquiv state.graph eV)
        (sourceBoundChannel codec eV state ledger cover).annotation =
      some (viewOfLedger ledger) :=
  sourceBoundChannel_decodeView codec eV state ledger cover

/-- Full dependent reconstruction: the decoded view carries a source-bound validity certificate
(from the ledger's actual participant facts) that rebuilds the dependent ledger exactly, with no
original ledger payload stored in the attached state. -/
example :
    ∃ view : ResidueLedgerView Locant
        (state.graph.certifiedEncoding eV).input.molecule.atomCount
        (state.graph.certifiedEncoding eV).input.molecule.interactions.length
        ledger.residueCount,
      decodeView? codec (encodedAtomEquiv state.graph eV)
          (sourceBoundChannel codec eV state ledger cover).annotation = some view ∧
      ∃ valid : SourceBoundViewValidity (Locant := Locant) state.graph eV view,
        viewToLedger view valid.link_source_mem valid.link_target_mem = ledger :=
  sourceBoundChannel_reconstruct codec eV state ledger cover

end SourceBoundResidue

/-! ## Final closed-ring frame successor: certificate, reconstruction and fieldwise recovery -/

section ClosedRingFrame

variable {V : Type*} {molecule : SemanticMolecule}
variable (e : V ≃ Fin molecule.atomCount)
variable (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule)

/-- Adapting an actual closed-ring observation retains its real plane, ordered ring support and
both substituents exactly through the common atom equivalence. -/
example :
    (physicalClosedRingObservationToFrame (V := V) e observation).realPlane? =
        some observation.observation.plane ∧
      (physicalClosedRingObservationToFrame (V := V) e observation).ringAtoms? =
        some (observation.observation.ringAtoms.map e.symm) ∧
      (physicalClosedRingObservationToFrame (V := V) e observation).realRingPlaneFirstSubstituent? =
        some (e.symm observation.observation.firstSubstituent) ∧
      (physicalClosedRingObservationToFrame (V := V) e observation).realRingPlaneSecondSubstituent? =
        some (e.symm observation.observation.secondSubstituent) :=
  physicalClosedRingObservationToFrame_genericRecovery e observation

/-- Decoding under the induced certificate recovers the first selected ring position exactly. -/
example :
    (RealRingPlaneFrame.toPhysicalClosedRingObservation e observation.observation.conformation
      (physicalClosedRingObservationToRealRingPlaneFrame e observation)
      (physicalClosedRingObservationToFrameCertificate e observation)).firstAttachment.ringPosition =
      observation.firstAttachment.ringPosition :=
  physicalClosedRingObservationToFrame_firstAttachment_recovery e observation

/-- Decoding under the induced certificate recovers the first actual source interaction, at the
frame's retained occurrence index, as the original interaction value. -/
example :
    (RealRingPlaneFrame.toPhysicalClosedRingObservation e observation.observation.conformation
      (physicalClosedRingObservationToRealRingPlaneFrame e observation)
      (physicalClosedRingObservationToFrameCertificate e observation)).firstAttachment.interaction =
      observation.firstAttachment.interaction :=
  physicalClosedRingObservationToFrame_firstInteraction_recovery e observation

end ClosedRingFrame

end OneCenter
end TetraStereo






-- Joined whole-state representation: both inverses, whole-set recovery and frames.
assert_kernel_only TetraStereo.OneCenter.decodeDescription_encodeDescription
assert_kernel_only TetraStereo.OneCenter.encodeDescription_decodeDescription
assert_kernel_only TetraStereo.OneCenter.decodeDescription_image_encodeDescriptionSet
assert_kernel_only TetraStereo.OneCenter.decodeDescription_encodeDescription_frames

-- Whole-information recovery and nonemptiness.
assert_kernel_only
  TetraStereo.OneCenter.FiniteClassicalInformation.decodeInformation_encodeInformation
assert_kernel_only
  TetraStereo.OneCenter.FiniteClassicalInformation.encodeInformation_decodeInformation
assert_kernel_only
  TetraStereo.OneCenter.FiniteClassicalInformation.encodeInformation_possible_nonempty_iff
assert_kernel_only
  TetraStereo.OneCenter.FiniteClassicalInformation.decodeInformation_possible_nonempty_iff

-- Heterogeneous samples: complete sample and whole-set recovery.
assert_kernel_only TetraStereo.OneCenter.OrganicStereoHeterogeneousSamples.decode_encode
assert_kernel_only TetraStereo.OneCenter.OrganicStereoHeterogeneousSamples.encode_decode
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoHeterogeneousSamples.UncertainSample.decodeSet_encodeSet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoHeterogeneousSamples.UncertainSample.encodeSet_decodeSet

-- Authoritative source ingress: exact round trip for every certified input.
assert_kernel_only
  TetraStereo.OneCenter.CertifiedAuthoritativeChemicalInput.encode_decode

-- Completion ingress: source projection, input reconstruction, nonemptiness and absent spatial.
assert_kernel_only TetraStereo.OneCenter.sourceOfState_of_mem_completions
assert_kernel_only
  TetraStereo.OneCenter.CertifiedAuthoritativeChemicalInput.encode_sourceOfState_completion
assert_kernel_only
  TetraStereo.OneCenter.CertifiedAuthoritativeChemicalInput.completions_nonempty_of_decode
assert_kernel_only
  TetraStereo.OneCenter.CertifiedAuthoritativeChemicalInput.exists_completion_of_absent_spatial

-- Electronic ingress and attachment: supplied source and complete assignment recovery.
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoElectronicDescriptionIngress.ingressState_toIndependentElectronicSiteSource
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoElectronicDescriptionIngress.ingressState_electronicAssignment
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoElectronicStateAttachment.attachElectronic_toIndependentElectronicSiteSource
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoElectronicStateAttachment.attachElectronic_electronicAssignment

-- Path ingress and attachment: full record recovery, geometry and coexistence.
assert_kernel_only TetraStereo.OneCenter.toIndependentBondPathData_toWholeState
assert_kernel_only
  TetraStereo.OneCenter.toIndependentBondPathData_attachIndependentBondPathData
assert_kernel_only TetraStereo.OneCenter.pathGeometryValid_attachIndependentBondPathData
assert_kernel_only
  TetraStereo.OneCenter.attachIndependentBondPathData_coexistence_derived

-- Band ingress and attachment: full record recovery, agreement and encoding compatibility.
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoBandDescriptionIngress.toIndependentBandAttachment_ofIndependentBandAttachment
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoBandStateAttachment.toIndependentBandAttachment_attachIndependentBands
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoBandStateAttachment.attachIndependentBands_band_agreement_apply
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoBandStateAttachment.encodedBandFamily_attachIndependentBands

-- Source-bound residue assembly: molecule identity and full decoded-certificate reconstruction.
assert_kernel_only TetraStereo.OneCenter.certifiedEncoding_molecule_identity
assert_kernel_only TetraStereo.OneCenter.sourceBoundChannel_decodeView
assert_kernel_only TetraStereo.OneCenter.sourceBoundChannel_links_recovered
assert_kernel_only TetraStereo.OneCenter.sourceBoundChannel_reconstruct

-- Final closed-ring frame successor: induced certificate, reconstruction and fieldwise recovery.
assert_kernel_only TetraStereo.OneCenter.physicalClosedRingObservationToFrameCertificate
assert_kernel_only TetraStereo.OneCenter.physicalClosedRingObservationToFrame_genericRecovery
assert_kernel_only TetraStereo.OneCenter.physicalClosedRingObservationToFrame_ringAtoms_recovery
assert_kernel_only TetraStereo.OneCenter.physicalClosedRingObservationToFrame_firstAttachment_recovery
assert_kernel_only TetraStereo.OneCenter.physicalClosedRingObservationToFrame_firstInteraction_recovery
assert_kernel_only TetraStereo.OneCenter.physicalClosedRingObservationToFrame_secondAttachment_recovery
assert_kernel_only TetraStereo.OneCenter.physicalClosedRingObservationToFrame_secondInteraction_recovery
