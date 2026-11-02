import TetraStereo.OneCenter.IUPACP93CanonicalFullereneDerivativeRelationalEvidence
import TetraStereo.OneCenter.P93MolecularFullereneExecutableRelationalAudit

set_option autoImplicit false
set_option maxRecDepth 100000










namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

abbrev iupacP93CanonicalFullereneC70SuperimposedTopologyInput :
    MolecularFullereneConfigurationInput :=
  iupacP93CanonicalFullereneC70Transcription.numberedPackage.topologyInput

abbrev iupacP93CanonicalFullereneC70SuperimposedMolecule : RawMolecule :=
  iupacP93CanonicalFullereneC70SuperimposedAssembly.compileExtension.assemble

abbrev iupacP93CanonicalFullereneC70SuperimposedFirstAddend :=
  iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledPlacedAddend 0
    iupacP93CanonicalFullereneC70SuperimposedFirstPlacement.toPlaced

abbrev iupacP93CanonicalFullereneC70SuperimposedSecondAddend :=
  iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledPlacedAddend 1
    iupacP93CanonicalFullereneC70SuperimposedSecondPlacement.toPlaced

private theorem compiledPlacedAddend_attachmentSites
    {core : RawMolecule} {carrier : Finset Nat}
    (assembly : MolecularFullereneAddendTemplateAssembly core carrier)
    (index : Nat) (placed : MolecularFullerenePlacedAddendTemplate carrier)
    (atIndex : assembly.placements[index]? = some placed) :
    (assembly.compiledPlacedAddend index placed).attachmentSites = placed.attachmentSites := by
  have observed := assembly.compiledAddend_externalAtoms index placed atIndex
  rw [assembly.compiledAddend_eq_some_compiledPlacedAddend index placed atIndex] at observed
  have addendEq := Option.some.inj observed
  rw [addendEq]
  ext site
  simp [MolecularFullereneAddend.attachmentSites,
    MolecularFullerenePlacedAddendTemplate.attachmentSites]

private theorem c70SuperimposedFirstAddend_attachmentSites :
    iupacP93CanonicalFullereneC70SuperimposedFirstAddend.attachmentSites = {7, 24} := by
  rw [compiledPlacedAddend_attachmentSites
    iupacP93CanonicalFullereneC70SuperimposedAssembly 0
    iupacP93CanonicalFullereneC70SuperimposedFirstPlacement.toPlaced rfl]
  have sites := iupacP93CanonicalFullereneDerivativeAssemblies_attachmentSites.2.2.2.2
  have indexed := congrArg (fun values => values[0]?) sites
  dsimp only at indexed
  rw [List.getElem?_map,
    show iupacP93CanonicalFullereneC70SuperimposedAssembly.placements[0]? =
      some iupacP93CanonicalFullereneC70SuperimposedFirstPlacement.toPlaced by rfl] at indexed
  simpa [iupacP93CanonicalFullereneC70SuperimposedPlacements] using indexed

private theorem c70SuperimposedSecondAddend_attachmentSites :
    iupacP93CanonicalFullereneC70SuperimposedSecondAddend.attachmentSites = {32, 33} := by
  rw [compiledPlacedAddend_attachmentSites
    iupacP93CanonicalFullereneC70SuperimposedAssembly 1
    iupacP93CanonicalFullereneC70SuperimposedSecondPlacement.toPlaced rfl]
  have sites := iupacP93CanonicalFullereneDerivativeAssemblies_attachmentSites.2.2.2.2
  have indexed := congrArg (fun values => values[1]?) sites
  dsimp only at indexed
  rw [List.getElem?_map,
    show iupacP93CanonicalFullereneC70SuperimposedAssembly.placements[1]? =
      some iupacP93CanonicalFullereneC70SuperimposedSecondPlacement.toPlaced by rfl] at indexed
  simpa [iupacP93CanonicalFullereneC70SuperimposedPlacements] using indexed

inductive IUPACP93C70SuperimposedProbe
  | site7
  | site24
  | site32
  | site33
  deriving DecidableEq, Fintype

def iupacP93C70FlagWordTo7 : List MolecularFullereneFlagMove :=
  [.reverseEdge, .continueLeftFace, .continueLeftFace, .reverseEdge,
    .continueLeftFace, .reverseEdge]

def iupacP93C70FlagWordTo24 : List MolecularFullereneFlagMove :=
  [.reverseEdge, .continueLeftFace, .continueLeftFace, .reverseEdge,
    .continueLeftFace, .continueLeftFace, .reverseEdge]

def iupacP93C70FlagWordTo32 : List MolecularFullereneFlagMove :=
  [.continueLeftFace, .reverseEdge, .continueLeftFace, .continueLeftFace,
    .continueLeftFace, .continueLeftFace, .reverseEdge, .continueLeftFace, .reverseEdge]

def iupacP93C70FlagWordTo33 : List MolecularFullereneFlagMove :=
  [.continueLeftFace, .reverseEdge, .continueLeftFace, .continueLeftFace,
    .continueLeftFace, .continueLeftFace, .reverseEdge, .continueLeftFace,
    .continueLeftFace, .reverseEdge]

def iupacP93CanonicalFullereneC70SuperimposedSourceDart :
    MolecularFullereneDirectedCarrierEdge
      iupacP93CanonicalFullereneC70SuperimposedTopologyInput :=
  (⟨0, by decide⟩, ⟨1, by decide⟩)

def iupacP93C70SuperimposedProbe : IUPACP93C70SuperimposedProbe →
    MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC70SuperimposedTopologyInput
  | .site7 => ⟨7, by decide⟩
  | .site24 => ⟨24, by decide⟩
  | .site32 => ⟨32, by decide⟩
  | .site33 => ⟨33, by decide⟩

def iupacP93C70SuperimposedAddress : IUPACP93C70SuperimposedProbe →
    List MolecularFullereneFlagMove
  | .site7 => iupacP93C70FlagWordTo7
  | .site24 => iupacP93C70FlagWordTo24
  | .site32 => iupacP93C70FlagWordTo32
  | .site33 => iupacP93C70FlagWordTo33

private theorem c70SuperimposedProbe_recovers : ∀ index,
    (walkMolecularFullereneFlag
      (molecularFullereneContinueForwardFace
        iupacP93CanonicalFullereneC70SuperimposedTopologyInput)
      iupacP93CanonicalFullereneC70SuperimposedSourceDart
      (iupacP93C70SuperimposedAddress index)).1 =
        iupacP93C70SuperimposedProbe index := by
  intro index
  cases index <;> decide

def iupacP93C70SuperimposedImagePair
    (image : IUPACP93C70SuperimposedProbe →
      MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC70SuperimposedTopologyInput)
    (first second : IUPACP93C70SuperimposedProbe) : Finset Nat :=
  {(image first).1, (image second).1}

def iupacP93C70SuperimposedObstruction
    (image : IUPACP93C70SuperimposedProbe →
      MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC70SuperimposedTopologyInput) : Prop :=
  (iupacP93C70SuperimposedImagePair image .site7 .site24 = {7, 24} ∧
      iupacP93C70SuperimposedImagePair image .site32 .site33 = {32, 33}) ∨
    (iupacP93C70SuperimposedImagePair image .site7 .site24 = {32, 33} ∧
      iupacP93C70SuperimposedImagePair image .site32 .site33 = {7, 24})


structure IUPACP93C70SuperimposedCoreAuditCertificate : Prop where
  firstAttachmentSites :
    iupacP93CanonicalFullereneC70SuperimposedFirstAddend.attachmentSites = {7, 24}
  secondAttachmentSites :
    iupacP93CanonicalFullereneC70SuperimposedSecondAddend.attachmentSites = {32, 33}
  probeRecovers : ∀ index,
    (walkMolecularFullereneFlag
      (molecularFullereneContinueForwardFace
        iupacP93CanonicalFullereneC70SuperimposedTopologyInput)
      iupacP93CanonicalFullereneC70SuperimposedSourceDart
      (iupacP93C70SuperimposedAddress index)).1 =
        iupacP93C70SuperimposedProbe index


def iupacP93CanonicalFullereneC70SuperimposedCoreAudit :
    IUPACP93C70SuperimposedCoreAuditCertificate where
  firstAttachmentSites := c70SuperimposedFirstAddend_attachmentSites
  secondAttachmentSites := c70SuperimposedSecondAddend_attachmentSites
  probeRecovers := c70SuperimposedProbe_recovers

end

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
