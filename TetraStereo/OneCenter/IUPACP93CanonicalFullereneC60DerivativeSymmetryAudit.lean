import TetraStereo.OneCenter.IUPACP93CanonicalFullereneDerivativeRelationalEvidence
import TetraStereo.OneCenter.P93MolecularFullereneCageSymmetryTransport
import TetraStereo.OneCenter.P93MolecularFullereneExecutableRelationalAudit
import TetraStereo.OneCenter.P93MolecularFullereneLocantInvolution

set_option autoImplicit false
set_option maxRecDepth 100000










namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

abbrev iupacP93CanonicalFullereneC60DerivativeTopologyInput :
    MolecularFullereneConfigurationInput :=
  iupacP93CanonicalFullereneC60Transcription.numberedPackage.topologyInput

abbrev iupacP93CanonicalFullereneC60Type2Molecule : RawMolecule :=
  iupacP93CanonicalFullereneC60Type2Assembly.compileExtension.assemble

abbrev iupacP93CanonicalFullereneC60Type3Molecule : RawMolecule :=
  iupacP93CanonicalFullereneC60Type3Assembly.compileExtension.assemble

abbrev iupacP93CanonicalFullereneC60Type2FirstAddend :=
  iupacP93CanonicalFullereneC60Type2Assembly.compiledPlacedAddend 0
    iupacP93CanonicalFullereneC60Type2FirstPlacement.toPlaced

abbrev iupacP93CanonicalFullereneC60Type2SecondAddend :=
  iupacP93CanonicalFullereneC60Type2Assembly.compiledPlacedAddend 1
    iupacP93CanonicalFullereneC60Type2SecondPlacement.toPlaced

abbrev iupacP93CanonicalFullereneC60Type3TertButylAddend :=
  iupacP93CanonicalFullereneC60Type3Assembly.compiledPlacedAddend 0
    iupacP93CanonicalFullereneC60Type3TertButylPlacement.toPlaced

abbrev iupacP93CanonicalFullereneC60Type3DicyclopropylAddend :=
  iupacP93CanonicalFullereneC60Type3Assembly.compiledPlacedAddend 1
    iupacP93CanonicalFullereneC60Type3DicyclopropylPlacement.toPlaced

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

private theorem c60Type2FirstAddend_attachmentSites :
    iupacP93CanonicalFullereneC60Type2FirstAddend.attachmentSites = {0} := by
  rw [compiledPlacedAddend_attachmentSites
    iupacP93CanonicalFullereneC60Type2Assembly 0
    iupacP93CanonicalFullereneC60Type2FirstPlacement.toPlaced rfl]
  have sites := iupacP93CanonicalFullereneDerivativeAssemblies_attachmentSites.2.1
  have indexed := congrArg (fun values => values[0]?) sites
  dsimp only at indexed
  rw [List.getElem?_map, show iupacP93CanonicalFullereneC60Type2Assembly.placements[0]? =
    some iupacP93CanonicalFullereneC60Type2FirstPlacement.toPlaced by rfl] at indexed
  simpa [iupacP93CanonicalFullereneC60Type2Placements] using indexed

private theorem c60Type2SecondAddend_attachmentSites :
    iupacP93CanonicalFullereneC60Type2SecondAddend.attachmentSites = {22} := by
  rw [compiledPlacedAddend_attachmentSites
    iupacP93CanonicalFullereneC60Type2Assembly 1
    iupacP93CanonicalFullereneC60Type2SecondPlacement.toPlaced rfl]
  have sites := iupacP93CanonicalFullereneDerivativeAssemblies_attachmentSites.2.1
  have indexed := congrArg (fun values => values[1]?) sites
  dsimp only at indexed
  rw [List.getElem?_map, show iupacP93CanonicalFullereneC60Type2Assembly.placements[1]? =
    some iupacP93CanonicalFullereneC60Type2SecondPlacement.toPlaced by rfl] at indexed
  simpa [iupacP93CanonicalFullereneC60Type2Placements] using indexed

private theorem c60Type3TertButylAddend_attachmentSites :
    iupacP93CanonicalFullereneC60Type3TertButylAddend.attachmentSites = {0} := by
  rw [compiledPlacedAddend_attachmentSites
    iupacP93CanonicalFullereneC60Type3Assembly 0
    iupacP93CanonicalFullereneC60Type3TertButylPlacement.toPlaced rfl]
  have sites := iupacP93CanonicalFullereneDerivativeAssemblies_attachmentSites.2.2.1
  have indexed := congrArg (fun values => values[0]?) sites
  dsimp only at indexed
  rw [List.getElem?_map, show iupacP93CanonicalFullereneC60Type3Assembly.placements[0]? =
    some iupacP93CanonicalFullereneC60Type3TertButylPlacement.toPlaced by rfl] at indexed
  simpa [iupacP93CanonicalFullereneC60Type3Placements] using indexed

private theorem c60Type3DicyclopropylAddend_attachmentSites :
    iupacP93CanonicalFullereneC60Type3DicyclopropylAddend.attachmentSites = {6} := by
  rw [compiledPlacedAddend_attachmentSites
    iupacP93CanonicalFullereneC60Type3Assembly 1
    iupacP93CanonicalFullereneC60Type3DicyclopropylPlacement.toPlaced rfl]
  have sites := iupacP93CanonicalFullereneDerivativeAssemblies_attachmentSites.2.2.1
  have indexed := congrArg (fun values => values[1]?) sites
  dsimp only at indexed
  rw [List.getElem?_map, show iupacP93CanonicalFullereneC60Type3Assembly.placements[1]? =
    some iupacP93CanonicalFullereneC60Type3DicyclopropylPlacement.toPlaced by rfl] at indexed
  simpa [iupacP93CanonicalFullereneC60Type3Placements] using indexed

inductive IUPACP93C60AttachmentProbe
  | first
  | second
  | sourceRight
  deriving DecidableEq, Fintype

def iupacP93C60FlagWordTo6 : List MolecularFullereneFlagMove :=
  [.reverseEdge, .continueLeftFace, .reverseEdge, .continueLeftFace,
    .continueLeftFace, .continueLeftFace, .reverseEdge]

def iupacP93C60FlagWordTo22 : List MolecularFullereneFlagMove :=
  [.reverseEdge, .continueLeftFace, .reverseEdge, .continueLeftFace,
    .continueLeftFace, .continueLeftFace, .continueLeftFace, .reverseEdge,
    .continueLeftFace, .continueLeftFace, .reverseEdge]

def iupacP93CanonicalFullereneC60DerivativeSourceDart :
    MolecularFullereneDirectedCarrierEdge
      iupacP93CanonicalFullereneC60DerivativeTopologyInput :=
  (⟨0, by decide⟩, ⟨1, by decide⟩)

def iupacP93C60Type2Probe : IUPACP93C60AttachmentProbe →
    MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC60DerivativeTopologyInput
  | .first => ⟨0, by decide⟩
  | .second => ⟨22, by decide⟩
  | .sourceRight => ⟨1, by decide⟩

def iupacP93C60Type2Address : IUPACP93C60AttachmentProbe →
    List MolecularFullereneFlagMove
  | .first => []
  | .second => iupacP93C60FlagWordTo22
  | .sourceRight => [.reverseEdge]

def iupacP93C60Type3Probe : IUPACP93C60AttachmentProbe →
    MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC60DerivativeTopologyInput
  | .first => ⟨0, by decide⟩
  | .second => ⟨6, by decide⟩
  | .sourceRight => ⟨1, by decide⟩

def iupacP93C60Type3Address : IUPACP93C60AttachmentProbe →
    List MolecularFullereneFlagMove
  | .first => []
  | .second => iupacP93C60FlagWordTo6
  | .sourceRight => [.reverseEdge]

private theorem c60Type2Probe_recovers : ∀ index,
    (walkMolecularFullereneFlag
      (molecularFullereneContinueForwardFace
        iupacP93CanonicalFullereneC60DerivativeTopologyInput)
      iupacP93CanonicalFullereneC60DerivativeSourceDart
      (iupacP93C60Type2Address index)).1 = iupacP93C60Type2Probe index := by
  intro index
  cases index <;> decide

private theorem c60Type3Probe_recovers : ∀ index,
    (walkMolecularFullereneFlag
      (molecularFullereneContinueForwardFace
        iupacP93CanonicalFullereneC60DerivativeTopologyInput)
      iupacP93CanonicalFullereneC60DerivativeSourceDart
      (iupacP93C60Type3Address index)).1 = iupacP93C60Type3Probe index := by
  intro index
  cases index <;> decide

private def c60ReversePentagonBoundaryDarts : List (Nat × Nat) :=
  (iupacP93CanonicalFullereneC60Faces.take 12).flatMap fun face =>
    (iupacP93C60DirectedFaceEdges face).map fun edge => (edge.2, edge.1)

def iupacP93C60UnorderedPairObstruction (secondSite : Nat)
    (image : IUPACP93C60AttachmentProbe →
      MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC60DerivativeTopologyInput) : Prop :=
  (image .first).1 = 0 ∧ (image .second).1 = secondSite ∨
    (image .first).1 = secondSite ∧ (image .second).1 = 0

def iupacP93C60FixedPairObstruction (secondSite : Nat)
    (image : IUPACP93C60AttachmentProbe →
      MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC60DerivativeTopologyInput) : Prop :=
  (image .first).1 = 0 ∧ (image .second).1 = secondSite

def iupacP93C60Type3AdmissibleFixedObstruction
    (image : IUPACP93C60AttachmentProbe →
      MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC60DerivativeTopologyInput) : Prop :=
  ((image .first).1, (image .sourceRight).1) ∈ c60ReversePentagonBoundaryDarts ∧
    iupacP93C60FixedPairObstruction 6 image

private def c60CarrierAtomAt (atom : Nat) :
    MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC60DerivativeTopologyInput :=
  if present : atom ∈ iupacP93CanonicalFullereneC60DerivativeTopologyInput.carrier then
    ⟨atom, present⟩
  else ⟨0, by decide⟩

private def c60DartAt (left right : Nat) : MolecularFullereneDirectedCarrierEdge
    iupacP93CanonicalFullereneC60DerivativeTopologyInput :=
  (c60CarrierAtomAt left, c60CarrierAtomAt right)

private theorem c60DartAt_eq (target : MolecularFullereneDirectedCarrierEdge
    iupacP93CanonicalFullereneC60DerivativeTopologyInput) :
    c60DartAt target.1.1 target.2.1 = target := by
  apply Prod.ext
  · apply Subtype.ext
    simp [c60DartAt, c60CarrierAtomAt, target.1.2]
  · apply Subtype.ext
    simp [c60DartAt, c60CarrierAtomAt, target.2.2]

private theorem c60PentagonFaces_exact :
    iupacP93CanonicalFullereneC60Faces.filter (fun face => face.length = 5) =
      iupacP93CanonicalFullereneC60Faces.take 12 := by
  decide

private theorem c60DirectedFaceEdges_eq_zip_rotate (face : List Nat) :
    iupacP93C60DirectedFaceEdges face = face.zip (face.rotate 1) := by
  cases face <;> simp [iupacP93C60DirectedFaceEdges]

private theorem c60DirectedFaceEdges_isRotated
    {first second : List Nat} (rotated : first.IsRotated second) :
    (iupacP93C60DirectedFaceEdges first).IsRotated
      (iupacP93C60DirectedFaceEdges second) := by
  rcases rotated with ⟨turn, rfl⟩
  rw [c60DirectedFaceEdges_eq_zip_rotate,
    c60DirectedFaceEdges_eq_zip_rotate]
  refine ⟨turn, ?_⟩
  change (List.zipWith (fun left right => (left, right)) first
      (first.rotate 1)).rotate turn =
    List.zipWith (fun left right => (left, right)) (first.rotate turn)
      ((first.rotate turn).rotate 1)
  rw [List.zipWith_rotate_distrib (fun left right => (left, right))
    first (first.rotate 1) turn (by simp)]
  simp only [List.rotate_rotate]
  rw [Nat.add_comm turn 1]

private theorem c60_reversingImageSourceDart_mem_reversePentagonBoundary
    (symmetry : Equiv.Perm
      (MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC60DerivativeTopologyInput))
    (reversing : MolecularFullereneFaceOrientationReversing
      iupacP93CanonicalFullereneC60DerivativeTopologyInput symmetry) :
    ((symmetry (iupacP93C60Type3Probe .first)).1,
      (symmetry (iupacP93C60Type3Probe .sourceRight)).1) ∈
        c60ReversePentagonBoundaryDarts := by
  rcases reversing iupacP93CanonicalFullereneC60FsCStartFace
      iupacP93CanonicalFullereneC60_fsCStartFace_mem with
    ⟨targetFace, targetPresent, rotated⟩
  have targetLength : targetFace.length = 5 := by
    have lengths := rotated.perm.length_eq
    simpa [mapMolecularFullereneFace,
      iupacP93CanonicalFullereneC60FsCStartFace] using lengths.symm
  have targetPentagon : targetFace ∈ iupacP93CanonicalFullereneC60Faces.take 12 := by
    rw [← c60PentagonFaces_exact]
    exact List.mem_filter.mpr ⟨targetPresent, by simp [targetLength]⟩
  have sourceEdge :
      ((symmetry (iupacP93C60Type3Probe .sourceRight)).1,
        (symmetry (iupacP93C60Type3Probe .first)).1) ∈
          iupacP93C60DirectedFaceEdges
            (mapMolecularFullereneFace
              iupacP93CanonicalFullereneC60DerivativeTopologyInput symmetry
              iupacP93CanonicalFullereneC60FsCStartFace).reverse := by
    simp [iupacP93C60DirectedFaceEdges, mapMolecularFullereneFace,
      iupacP93CanonicalFullereneC60FsCStartFace,
      iupacP93C60Type3Probe,
      show 0 ∈ iupacP93CanonicalFullereneC60DerivativeTopologyInput.carrier by decide,
      show 1 ∈ iupacP93CanonicalFullereneC60DerivativeTopologyInput.carrier by decide,
      show 2 ∈ iupacP93CanonicalFullereneC60DerivativeTopologyInput.carrier by decide,
      show 3 ∈ iupacP93CanonicalFullereneC60DerivativeTopologyInput.carrier by decide,
      show 4 ∈ iupacP93CanonicalFullereneC60DerivativeTopologyInput.carrier by decide]
  have targetEdge :
      ((symmetry (iupacP93C60Type3Probe .sourceRight)).1,
        (symmetry (iupacP93C60Type3Probe .first)).1) ∈
          iupacP93C60DirectedFaceEdges targetFace :=
    (c60DirectedFaceEdges_isRotated rotated).mem_iff.mp sourceEdge
  apply List.mem_flatMap.mpr
  refine ⟨targetFace, targetPentagon, ?_⟩
  apply List.mem_map.mpr
  exact ⟨_, targetEdge, rfl⟩

private def c60Type2TargetDecision
    (target : MolecularFullereneDirectedCarrierEdge
      iupacP93CanonicalFullereneC60DerivativeTopologyInput) :
    Decidable (¬iupacP93C60UnorderedPairObstruction 22 fun index =>
      (walkMolecularFullereneFlag
        (molecularFullereneContinueReverseFace
          iupacP93CanonicalFullereneC60DerivativeTopologyInput)
        target (iupacP93C60Type2Address index)).1) := by
  unfold iupacP93C60UnorderedPairObstruction
  infer_instance

private def c60Type3TargetDecision
    (target : MolecularFullereneDirectedCarrierEdge
      iupacP93CanonicalFullereneC60DerivativeTopologyInput) :
    Decidable (¬iupacP93C60Type3AdmissibleFixedObstruction fun index =>
      (walkMolecularFullereneFlag
        (molecularFullereneContinueReverseFace
          iupacP93CanonicalFullereneC60DerivativeTopologyInput)
        target (iupacP93C60Type3Address index)).1) := by
  unfold iupacP93C60Type3AdmissibleFixedObstruction
    iupacP93C60FixedPairObstruction
  infer_instance

private def c60Type2TargetWordAudit : Bool :=
  iupacP93CanonicalFullereneC60Edges.all fun edge =>
    @decide (¬iupacP93C60UnorderedPairObstruction 22 fun index =>
      (walkMolecularFullereneFlag
        (molecularFullereneContinueReverseFace
          iupacP93CanonicalFullereneC60DerivativeTopologyInput)
        (c60DartAt edge.1 edge.2) (iupacP93C60Type2Address index)).1)
      (c60Type2TargetDecision (c60DartAt edge.1 edge.2)) &&
    @decide (¬iupacP93C60UnorderedPairObstruction 22 fun index =>
      (walkMolecularFullereneFlag
        (molecularFullereneContinueReverseFace
          iupacP93CanonicalFullereneC60DerivativeTopologyInput)
        (c60DartAt edge.2 edge.1) (iupacP93C60Type2Address index)).1)
      (c60Type2TargetDecision (c60DartAt edge.2 edge.1))

private def c60Type3FixedTargetWordAudit : Bool :=
  c60ReversePentagonBoundaryDarts.all fun edge =>
    @decide (¬iupacP93C60Type3AdmissibleFixedObstruction fun index =>
      (walkMolecularFullereneFlag
        (molecularFullereneContinueReverseFace
          iupacP93CanonicalFullereneC60DerivativeTopologyInput)
        (c60DartAt edge.1 edge.2) (iupacP93C60Type3Address index)).1)
      (c60Type3TargetDecision (c60DartAt edge.1 edge.2))

set_option maxHeartbeats 0 in
private theorem c60Type2TargetWordAudit_true : c60Type2TargetWordAudit = true := by
  unfold c60Type2TargetWordAudit
  decide

set_option maxHeartbeats 0 in
private theorem c60Type3FixedTargetWordAudit_true :
    c60Type3FixedTargetWordAudit = true := by
  unfold c60Type3FixedTargetWordAudit
  decide

private theorem c60Type2_targetWordsReject
    (target : MolecularFullereneDirectedCarrierEdge
      iupacP93CanonicalFullereneC60DerivativeTopologyInput)
    (targetBond : 0 < iupacP93CanonicalFullereneC60Type2Molecule.bondOrder
      target.1.1 target.2.1) :
    ¬iupacP93C60UnorderedPairObstruction 22 fun index =>
      (walkMolecularFullereneFlag
        (molecularFullereneContinueReverseFace
          iupacP93CanonicalFullereneC60DerivativeTopologyInput)
        target (iupacP93C60Type2Address index)).1 := by
  have coreBond : 0 < iupacP93CanonicalFullereneC60Transcription.cageMolecule.bondOrder
      target.1.1 target.2.1 := by
    rw [← iupacP93CanonicalFullereneC60Type2Assembly.compileExtension.bondOrder_on_carrier
      target.1.1 target.2.1 target.1.2 target.2.2]
    exact targetBond
  have leftBound : target.1.1 < 60 := by
    have present := target.1.2
    change target.1.1 ∈ Finset.range 60 at present
    exact Finset.mem_range.mp present
  have rightBound : target.2.1 < 60 := by
    have present := target.2.2
    change target.2.1 ∈ Finset.range 60 at present
    exact Finset.mem_range.mp present
  have distinct : target.1.1 ≠ target.2.1 := by
    intro equal
    have targetEq : target.1 = target.2 := Subtype.ext equal
    rw [targetEq, RawMolecule.bondOrder_self] at coreBond
    simp at coreBond
  have sourceEdge := (iupacP93CanonicalFullereneC60_hasFaceEdge_iff_hasSourceEdge
    target.1.1 target.2.1 leftBound rightBound distinct).1
      ((NumberedFaceTranscription.cageMolecule_bondOrder_pos_iff_hasFaceEdge
        iupacP93CanonicalFullereneC60Transcription target.1.1 target.2.1
        leftBound rightBound distinct).1 coreBond)
  have sourcePresent : iupacP93C60CanonicalEdge (target.1.1, target.2.1) ∈
      iupacP93CanonicalFullereneC60Edges := by
    simpa [iupacP93CanonicalFullereneC60HasSourceEdge] using sourceEdge
  have checked := (List.all_eq_true.mp c60Type2TargetWordAudit_true)
    (iupacP93C60CanonicalEdge (target.1.1, target.2.1)) sourcePresent
  rcases lt_or_gt_of_ne distinct with ordered | ordered
  · have canonical : iupacP93C60CanonicalEdge (target.1.1, target.2.1) =
        (target.1.1, target.2.1) := by
      simp [iupacP93C60CanonicalEdge, ordered]
    rw [canonical] at checked
    simp only [Bool.and_eq_true] at checked
    have forward := checked.1
    have rejected := @of_decide_eq_true _
      (c60Type2TargetDecision (c60DartAt target.1.1 target.2.1)) forward
    rw [c60DartAt_eq target] at rejected
    exact rejected
  · have canonical : iupacP93C60CanonicalEdge (target.1.1, target.2.1) =
        (target.2.1, target.1.1) := by
      simp [iupacP93C60CanonicalEdge, Nat.not_lt.mpr (Nat.le_of_lt ordered)]
    rw [canonical] at checked
    simp only [Bool.and_eq_true] at checked
    have reverse := checked.2
    have rejected := @of_decide_eq_true _
      (c60Type2TargetDecision (c60DartAt target.1.1 target.2.1)) reverse
    rw [c60DartAt_eq target] at rejected
    exact rejected

private theorem c60Type3_targetWordsReject
    (target : MolecularFullereneDirectedCarrierEdge
      iupacP93CanonicalFullereneC60DerivativeTopologyInput)
    (_targetBond : 0 < iupacP93CanonicalFullereneC60Type3Molecule.bondOrder
      target.1.1 target.2.1) :
    ¬iupacP93C60Type3AdmissibleFixedObstruction fun index =>
      (walkMolecularFullereneFlag
        (molecularFullereneContinueReverseFace
          iupacP93CanonicalFullereneC60DerivativeTopologyInput)
        target (iupacP93C60Type3Address index)).1 := by
  intro obstruction
  have targetListed : (target.1.1, target.2.1) ∈
      c60ReversePentagonBoundaryDarts := obstruction.1
  have checked := (List.all_eq_true.mp c60Type3FixedTargetWordAudit_true)
    (target.1.1, target.2.1) targetListed
  have rejected := @of_decide_eq_true _
    (c60Type3TargetDecision (c60DartAt target.1.1 target.2.1)) checked
  rw [c60DartAt_eq target] at rejected
  exact rejected obstruction

private theorem c60Type2_sourceBond :
    0 < iupacP93CanonicalFullereneC60Type2Molecule.bondOrder
      iupacP93CanonicalFullereneC60DerivativeSourceDart.1.1
      iupacP93CanonicalFullereneC60DerivativeSourceDart.2.1 := by
  rw [iupacP93CanonicalFullereneC60Type2Assembly.compileExtension.bondOrder_on_carrier
    _ _ iupacP93CanonicalFullereneC60DerivativeSourceDart.1.2
      iupacP93CanonicalFullereneC60DerivativeSourceDart.2.2]
  decide

private theorem c60Type3_sourceBond :
    0 < iupacP93CanonicalFullereneC60Type3Molecule.bondOrder
      iupacP93CanonicalFullereneC60DerivativeSourceDart.1.1
      iupacP93CanonicalFullereneC60DerivativeSourceDart.2.1 := by
  rw [iupacP93CanonicalFullereneC60Type3Assembly.compileExtension.bondOrder_on_carrier
    _ _ iupacP93CanonicalFullereneC60DerivativeSourceDart.1.2
      iupacP93CanonicalFullereneC60DerivativeSourceDart.2.2]
  decide

private theorem c60Type2_preserved_implies_obstruction
    (symmetry : Equiv.Perm
      (MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC60DerivativeTopologyInput))
    (preserved : MolecularFullereneSameTestAddendPatternPreserved
      iupacP93CanonicalFullereneC60Type2RelationalEvidence symmetry) :
    iupacP93C60UnorderedPairObstruction 22 fun index =>
      symmetry (iupacP93C60Type2Probe index) := by
  have addendsExact : iupacP93CanonicalFullereneC60Type2RelationalEvidence.addends =
      [iupacP93CanonicalFullereneC60Type2FirstAddend,
        iupacP93CanonicalFullereneC60Type2SecondAddend] :=
    iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.1
  have mapped := (molecularFullereneSameTestAddendPatternPreserved_two_iff_mappedSites
    iupacP93CanonicalFullereneC60Type2RelationalEvidence symmetry
    iupacP93CanonicalFullereneC60Type2FirstAddend
    iupacP93CanonicalFullereneC60Type2SecondAddend addendsExact).1 preserved
  rcases mapped with fixed | swapped
  · left
    simp [mappedMolecularFullereneAttachmentSites,
      c60Type2FirstAddend_attachmentSites, c60Type2SecondAddend_attachmentSites,
      mapMolecularFullereneCarrierAtom] at fixed
    exact ⟨fixed.1 _, fixed.2 _⟩
  · right
    simp [mappedMolecularFullereneAttachmentSites,
      c60Type2FirstAddend_attachmentSites, c60Type2SecondAddend_attachmentSites,
      mapMolecularFullereneCarrierAtom] at swapped
    exact ⟨swapped.1, swapped.2⟩

private theorem c60Type3_actualPreserved_implies_obstruction
    (symmetry : Equiv.Perm
      (MolecularFullereneCarrierAtom iupacP93CanonicalFullereneC60DerivativeTopologyInput))
    (preserved : MolecularFullereneActualAddendPatternPreserved
      iupacP93CanonicalFullereneC60Type3Molecule
      iupacP93CanonicalFullereneC60DerivativeTopologyInput
      iupacP93CanonicalFullereneC60Type3RelationalEvidence symmetry) :
    iupacP93C60FixedPairObstruction 6 fun index =>
      symmetry (iupacP93C60Type3Probe index) := by
  have addendsExact : iupacP93CanonicalFullereneC60Type3RelationalEvidence.addends =
      [iupacP93CanonicalFullereneC60Type3TertButylAddend,
        iupacP93CanonicalFullereneC60Type3DicyclopropylAddend] :=
    iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.1
  have actual := (molecularFullereneActualAddendPatternPreserved_two_iff
    iupacP93CanonicalFullereneC60Type3RelationalEvidence symmetry
    iupacP93CanonicalFullereneC60Type3TertButylAddend
    iupacP93CanonicalFullereneC60Type3DicyclopropylAddend addendsExact).1 preserved
  rcases actual with fixed | swapped
  · have firstMapped := fixed.1.mappedAttachmentSites_eq
    have secondMapped := fixed.2.mappedAttachmentSites_eq
    simp [mappedMolecularFullereneAttachmentSites,
      c60Type3TertButylAddend_attachmentSites,
      c60Type3DicyclopropylAddend_attachmentSites,
      mapMolecularFullereneCarrierAtom] at firstMapped secondMapped
    exact ⟨firstMapped _, secondMapped _⟩
  · exact False.elim ((iupacP93CanonicalFullereneC60Type3Assembly
      |>.compiledAddends_not_constitutionallyIsomorphic_of_atomCount_ne 0 1
        iupacP93CanonicalFullereneC60Type3TertButylPlacement.toPlaced
        iupacP93CanonicalFullereneC60Type3DicyclopropylPlacement.toPlaced
        (by decide))
      (MolecularFullereneAddend.constitutionallyIsomorphicAlong_isomorphic swapped.1))

theorem iupacP93CanonicalFullereneC60Type2_sameTest_chiral :
    MolecularFullereneSameTestAddendPatternChiral
      iupacP93CanonicalFullereneC60Type2RelationalEvidence := by
  apply molecularFullereneRelationalChiral_of_flagWord_obstruction
    iupacP93CanonicalFullereneC60Type2Molecule
    iupacP93CanonicalFullereneC60DerivativeTopologyInput
    (MolecularFullereneSameTestAddendPatternPreserved
      iupacP93CanonicalFullereneC60Type2RelationalEvidence)
    (iupacP93C60UnorderedPairObstruction 22)
    (iupacP93CanonicalFullereneC60Type2Assembly.transportCertificate
      iupacP93CanonicalFullereneC60Certificate).oriented
    iupacP93CanonicalFullereneC60DerivativeSourceDart c60Type2_sourceBond
    iupacP93C60Type2Probe iupacP93C60Type2Address c60Type2Probe_recovers
  · intro symmetry _automorphism _reversing preserved
    exact c60Type2_preserved_implies_obstruction symmetry preserved
  · exact c60Type2_targetWordsReject

theorem iupacP93CanonicalFullereneC60Type2_actual_chiral :
    MolecularFullereneActualAddendPatternChiral
      iupacP93CanonicalFullereneC60Type2Molecule
      iupacP93CanonicalFullereneC60DerivativeTopologyInput
      iupacP93CanonicalFullereneC60Type2RelationalEvidence :=
  molecularFullereneSameTestAddendPatternChiral_implies_actual
    iupacP93CanonicalFullereneC60Type2RelationalEvidence
    iupacP93CanonicalFullereneC60Type2_sameTest_chiral

theorem iupacP93CanonicalFullereneC60Type3_actual_chiral :
    MolecularFullereneActualAddendPatternChiral
      iupacP93CanonicalFullereneC60Type3Molecule
      iupacP93CanonicalFullereneC60DerivativeTopologyInput
      iupacP93CanonicalFullereneC60Type3RelationalEvidence := by
  apply molecularFullereneRelationalChiral_of_flagWord_obstruction
    iupacP93CanonicalFullereneC60Type3Molecule
    iupacP93CanonicalFullereneC60DerivativeTopologyInput
    (MolecularFullereneActualAddendPatternPreserved
      iupacP93CanonicalFullereneC60Type3Molecule
      iupacP93CanonicalFullereneC60DerivativeTopologyInput
      iupacP93CanonicalFullereneC60Type3RelationalEvidence)
    iupacP93C60Type3AdmissibleFixedObstruction
    (iupacP93CanonicalFullereneC60Type3Assembly.transportCertificate
      iupacP93CanonicalFullereneC60Certificate).oriented
    iupacP93CanonicalFullereneC60DerivativeSourceDart c60Type3_sourceBond
    iupacP93C60Type3Probe iupacP93C60Type3Address c60Type3Probe_recovers
  · intro symmetry _automorphism reversing preserved
    exact ⟨c60_reversingImageSourceDart_mem_reversePentagonBoundary symmetry reversing,
      c60Type3_actualPreserved_implies_obstruction symmetry preserved⟩
  · exact c60Type3_targetWordsReject

/-! ## Explicit Type-3 all-`T` reversing witness -/

def iupacP93CanonicalFullereneC60Type3ReversingTable : List Nat :=
  [6, 21, 20, 19, 5, 4, 0, 8, 7, 24, 23, 22, 41, 40, 39, 38, 37, 18, 17, 3,
    2, 1, 11, 10, 9, 25, 26, 44, 43, 42, 56, 55, 54, 53, 52, 35, 36, 16, 15,
    14, 13, 12, 29, 28, 27, 46, 45, 57, 58, 59, 51, 50, 34, 33, 32, 31, 30,
    47, 48, 49]

def iupacP93CanonicalFullereneC60Type3Involution :
    MolecularFullereneLocantInvolutionCertificate
      iupacP93CanonicalFullereneC60DerivativeTopologyInput where
  table := iupacP93CanonicalFullereneC60Type3ReversingTable
  mapsCarrier := by
    intro atom atomPresent
    have atomBound : atom < 60 := by
      simpa [iupacP93CanonicalFullereneC60DerivativeTopologyInput,
        MolecularFullereneNumberedCagePackage.topologyInput,
        MolecularFullereneNumberedCagePackage.toConfigurationInput,
        MolecularFullereneNumberedCagePackage.carrier,
        NumberedFaceTranscription.numberedPackage,
        NumberedFaceTranscription.atomsByLocant,
        iupacP93CanonicalFullereneC60Transcription] using atomPresent
    interval_cases atom <;> decide
  involutive := by
    intro atom atomPresent
    have atomBound : atom < 60 := by
      simpa [iupacP93CanonicalFullereneC60DerivativeTopologyInput,
        MolecularFullereneNumberedCagePackage.topologyInput,
        MolecularFullereneNumberedCagePackage.toConfigurationInput,
        MolecularFullereneNumberedCagePackage.carrier,
        NumberedFaceTranscription.numberedPackage,
        NumberedFaceTranscription.atomsByLocant,
        iupacP93CanonicalFullereneC60Transcription] using atomPresent
    interval_cases atom <;> decide

abbrev iupacP93CanonicalFullereneC60Type3ReversingSymmetry :=
  iupacP93CanonicalFullereneC60Type3Involution.toPerm

private theorem c60DerivativeCarrierAtom_lt
    (atom : MolecularFullereneCarrierAtom
      iupacP93CanonicalFullereneC60DerivativeTopologyInput) : atom.1 < 60 := by
  have member := atom.2
  change atom.1 ∈ Finset.range 60 at member
  exact Finset.mem_range.mp member

private theorem c60Type3Table_preservesEdgeTable :
    iupacP93CanonicalFullereneC60Transcription.edgeTable.all (fun edge =>
      iupacP93CanonicalFullereneC60Transcription.hasFaceEdge
        (iupacP93CanonicalFullereneC60Type3ReversingTable.getD edge.1 edge.1)
        (iupacP93CanonicalFullereneC60Type3ReversingTable.getD edge.2 edge.2)) = true := by
  decide

private theorem c60Type3_parentAutomorphism : MolecularFullereneCarrierAutomorphism
    iupacP93CanonicalFullereneC60Transcription.cageMolecule
    iupacP93CanonicalFullereneC60DerivativeTopologyInput
    iupacP93CanonicalFullereneC60Type3ReversingSymmetry := by
  apply molecularFullereneCarrierAutomorphism_of_involutive_forward
    iupacP93CanonicalFullereneC60Transcription.cageMolecule
    iupacP93CanonicalFullereneC60DerivativeTopologyInput
    iupacP93CanonicalFullereneC60Type3ReversingSymmetry
    iupacP93CanonicalFullereneC60Type3Involution.toPerm_involutive
  intro left right positive
  have leftBound : left.1 < iupacP93CanonicalFullereneC60Transcription.atomCount := by
    simpa [iupacP93CanonicalFullereneC60Transcription] using
      c60DerivativeCarrierAtom_lt left
  have rightBound : right.1 < iupacP93CanonicalFullereneC60Transcription.atomCount := by
    simpa [iupacP93CanonicalFullereneC60Transcription] using
      c60DerivativeCarrierAtom_lt right
  have distinct : left.1 ≠ right.1 := by
    intro equal
    have leftEqRight : left = right := Subtype.ext equal
    subst right
    simp [RawMolecule.bondOrder_self] at positive
  have faceEdge :=
    (NumberedFaceTranscription.cageMolecule_bondOrder_pos_iff_hasFaceEdge
      iupacP93CanonicalFullereneC60Transcription left.1 right.1
      leftBound rightBound distinct).mp positive
  have mappedLeftBound :
      (iupacP93CanonicalFullereneC60Type3ReversingSymmetry left).1 <
        iupacP93CanonicalFullereneC60Transcription.atomCount := by
    simpa [iupacP93CanonicalFullereneC60Transcription] using
      c60DerivativeCarrierAtom_lt
        (iupacP93CanonicalFullereneC60Type3ReversingSymmetry left)
  have mappedRightBound :
      (iupacP93CanonicalFullereneC60Type3ReversingSymmetry right).1 <
        iupacP93CanonicalFullereneC60Transcription.atomCount := by
    simpa [iupacP93CanonicalFullereneC60Transcription] using
      c60DerivativeCarrierAtom_lt
        (iupacP93CanonicalFullereneC60Type3ReversingSymmetry right)
  have mappedDistinct :
      (iupacP93CanonicalFullereneC60Type3ReversingSymmetry left).1 ≠
        (iupacP93CanonicalFullereneC60Type3ReversingSymmetry right).1 := by
    intro equal
    exact distinct (Subtype.ext_iff.mp
      (iupacP93CanonicalFullereneC60Type3ReversingSymmetry.injective
        (Subtype.ext equal)))
  apply (NumberedFaceTranscription.cageMolecule_bondOrder_pos_iff_hasFaceEdge
    iupacP93CanonicalFullereneC60Transcription _ _ mappedLeftBound mappedRightBound
    mappedDistinct).mpr
  rcases lt_or_gt_of_ne distinct with ordered | ordered
  · have edgePresent : (left.1, right.1) ∈
        iupacP93CanonicalFullereneC60Transcription.edgeTable :=
      (numberedFaceTranscription_mem_edgeTable_iff _ _ _).mpr
        ⟨leftBound, rightBound, ordered, faceEdge⟩
    have audited := (List.all_eq_true.mp c60Type3Table_preservesEdgeTable)
      (left.1, right.1) edgePresent
    simpa [iupacP93CanonicalFullereneC60Type3ReversingSymmetry,
      MolecularFullereneLocantInvolutionCertificate.toPerm,
      iupacP93CanonicalFullereneC60Type3Involution] using audited
  · have reverseFaceEdge :
        iupacP93CanonicalFullereneC60Transcription.hasFaceEdge right.1 left.1 = true := by
      rw [numberedFaceTranscription_hasFaceEdge_symm]
      exact faceEdge
    have edgePresent : (right.1, left.1) ∈
        iupacP93CanonicalFullereneC60Transcription.edgeTable :=
      (numberedFaceTranscription_mem_edgeTable_iff _ _ _).mpr
        ⟨rightBound, leftBound, ordered, reverseFaceEdge⟩
    have audited := (List.all_eq_true.mp c60Type3Table_preservesEdgeTable)
      (right.1, left.1) edgePresent
    rw [numberedFaceTranscription_hasFaceEdge_symm]
    simpa [iupacP93CanonicalFullereneC60Type3ReversingSymmetry,
      MolecularFullereneLocantInvolutionCertificate.toPerm,
      iupacP93CanonicalFullereneC60Type3Involution] using audited

private theorem c60Type3_automorphism : MolecularFullereneCarrierAutomorphism
    iupacP93CanonicalFullereneC60Type3Molecule
    iupacP93CanonicalFullereneC60DerivativeTopologyInput
    iupacP93CanonicalFullereneC60Type3ReversingSymmetry :=
  (iupacP93CanonicalFullereneC60Type3Assembly.compileExtension.cageAgreement
    iupacP93CanonicalFullereneC60SharedNumberedCage.certificate
      |>.carrierAutomorphism_iff
        iupacP93CanonicalFullereneC60Type3ReversingSymmetry).mp
    c60Type3_parentAutomorphism

set_option maxRecDepth 100000 in
private theorem c60Type3_reversing : MolecularFullereneFaceOrientationReversing
    iupacP93CanonicalFullereneC60DerivativeTopologyInput
    iupacP93CanonicalFullereneC60Type3ReversingSymmetry := by
  apply (molecularFullereneFaceOrientationReversingChecked_eq_true_iff
    iupacP93CanonicalFullereneC60DerivativeTopologyInput
    iupacP93CanonicalFullereneC60Type3ReversingSymmetry).mp
  decide

private theorem c60Type3_sameTest_preserved :
    MolecularFullereneSameTestAddendPatternPreserved
      iupacP93CanonicalFullereneC60Type3RelationalEvidence
      iupacP93CanonicalFullereneC60Type3ReversingSymmetry := by
  have addendsExact : iupacP93CanonicalFullereneC60Type3RelationalEvidence.addends =
      [iupacP93CanonicalFullereneC60Type3TertButylAddend,
        iupacP93CanonicalFullereneC60Type3DicyclopropylAddend] :=
    iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.1
  apply (molecularFullereneSameTestAddendPatternPreserved_two_iff_mappedSites
    iupacP93CanonicalFullereneC60Type3RelationalEvidence
    iupacP93CanonicalFullereneC60Type3ReversingSymmetry
    iupacP93CanonicalFullereneC60Type3TertButylAddend
    iupacP93CanonicalFullereneC60Type3DicyclopropylAddend addendsExact).2
  right
  constructor
  · unfold mappedMolecularFullereneAttachmentSites
    rw [c60Type3TertButylAddend_attachmentSites,
      c60Type3DicyclopropylAddend_attachmentSites]
    ext site
    simp [mapMolecularFullereneCarrierAtom,
      iupacP93CanonicalFullereneC60Type3ReversingSymmetry,
      iupacP93CanonicalFullereneC60Type3Involution,
      iupacP93CanonicalFullereneC60Type3ReversingTable,
      show 0 ∈ iupacP93CanonicalFullereneC60DerivativeTopologyInput.carrier by decide]
  · unfold mappedMolecularFullereneAttachmentSites
    rw [c60Type3DicyclopropylAddend_attachmentSites,
      c60Type3TertButylAddend_attachmentSites]
    ext site
    simp [mapMolecularFullereneCarrierAtom,
      iupacP93CanonicalFullereneC60Type3ReversingSymmetry,
      iupacP93CanonicalFullereneC60Type3Involution,
      iupacP93CanonicalFullereneC60Type3ReversingTable,
      show 6 ∈ iupacP93CanonicalFullereneC60DerivativeTopologyInput.carrier by decide]

theorem iupacP93CanonicalFullereneC60Type3_sameTest_achiral :
    ¬MolecularFullereneSameTestAddendPatternChiral
      iupacP93CanonicalFullereneC60Type3RelationalEvidence := by
  rintro ⟨_oriented, noReversing⟩
  exact noReversing ⟨iupacP93CanonicalFullereneC60Type3ReversingSymmetry,
    c60Type3_automorphism, c60Type3_reversing, c60Type3_sameTest_preserved⟩

end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC60Type2_sameTest_chiral
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC60Type2_actual_chiral
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC60Type3_sameTest_achiral
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC60Type3_actual_chiral
