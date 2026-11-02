import TetraStereo.OneCenter.LocalizedAcyclicPhysicalPseudoFidelity
import TetraStereo.OneCenter.LocalizedNoDoubleWholeStateRule45Bridge
import TetraStereo.OneCenter.LocalizedPhysicalLeafModelNone
import TetraStereo.OneCenter.LocalizedAcyclicFourLigandFrameCompleteness
import TetraStereo.OneCenter.LocalizedPhysicalTerminalTwinOutwardDomain
import TetraStereo.OneCenter.LocalizedRule4bSparseLabelDecoding
import TetraStereo.OneCenter.LocalizedConstitutionalFrameNormalization
import TetraStereo.OneCenter.LocalizedRootZAutomorphismLabelCovariance
import TetraStereo.OneCenter.LocalizedAcyclicCarrierInjectivity
import TetraStereo.OneCenter.AuxiliaryContextIntegrity
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false




































namespace TetraStereo
namespace OneCenter

namespace CertifiedLocalizedCIPInput

open TetraStereo.OneCenter

/-! ## Structural physical source predicates -/

/-- The current physical atom of an occurrence is not an automatically detected
tetrahedral center.  This is a statement about the molecule graph, not about any label. -/
def ActualPhysicalNoncandidate
    (input : LocalizedUniversalReference.Input)
    (target : LocalizedUniversalReference.Occurrence input) : Prop :=
  ∃ atom : input.certified.Atom,
    target.1.node.current? = some atom ∧
      atom ∉ input.certified.tetrahedralCenterSet

/-- The actual four-ligand frame constructor succeeds and its four root atomic numbers are
pairwise distinct.  This is immediate-neighbour atomic-number separation, a sufficient
physical rigidity condition; no key, comparison or label is mentioned. -/
def ActualPhysicalZSeparatedFrame
    (input : LocalizedUniversalReference.Input)
    (target : LocalizedUniversalReference.Occurrence input) : Prop :=
  ∃ frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input),
    input.certified.localizedOccurrenceFourLigandFrame? target = some frame ∧
      input.certified.ConstitutionallyAtomicNumberSeparatedFrame frame

/-- Two distinct physical terminal leaves at the current tetrahedral atom, with equal
atomic number, mass and formal charge.  Z/mass equality is what the runtime twin refusal
uses; formal-charge equality is retained for the shared strong gauge domain. -/
def ActualPhysicalTerminalTwinLeaves
    (input : LocalizedUniversalReference.Input)
    (target : LocalizedUniversalReference.Occurrence input) : Prop :=
  ∃ centerAtom leftAtom rightAtom : input.certified.Atom,
    target.1.node.current? = some centerAtom ∧
      input.certified.moleculeGraph.IsTetrahedralCenter centerAtom ∧
      input.certified.moleculeGraph.neighborFinset leftAtom = {centerAtom} ∧
      input.certified.moleculeGraph.neighborFinset rightAtom = {centerAtom} ∧
      leftAtom ≠ rightAtom ∧
      input.certified.moleculeGraph.atomZ leftAtom =
        input.certified.moleculeGraph.atomZ rightAtom ∧
      input.certified.moleculeGraph.atomMass leftAtom =
        input.certified.moleculeGraph.atomMass rightAtom ∧
      input.certified.moleculeGraph.formalCharge leftAtom =
        input.certified.moleculeGraph.formalCharge rightAtom

/-- The physical sparse source domain on one occurrence.  It is a structural disjunction:
not a detected candidate, or a Z-separated actual frame, or physical terminal twins. -/
def ActualPhysicalSparseSource
    (input : LocalizedUniversalReference.Input)
    (target : LocalizedUniversalReference.Occurrence input) : Prop :=
  ActualPhysicalNoncandidate input target ∨
    ActualPhysicalZSeparatedFrame input target ∨
      ActualPhysicalTerminalTwinLeaves input target

/-! ## Noncandidate occurrences read `none` -/





theorem referenceState_eq_none_of_actualPhysicalNoncandidate
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (noncandidate : ActualPhysicalNoncandidate input target) :
    LocalizedUniversalReference.referenceState input target = none := by
  obtain ⟨atom, current, notMem⟩ := noncandidate
  exact input.certified.localizedOccurrenceRule45CIPModel_eq_none_of_current_not_mem
    target atom current notMem
    (LocalizedUniversalReference.referenceState_bareRule45CIPModel_of_noDoubleRecords
      input noDouble)

/-! ## A separated actual frame reads `none` or uppercase -/

/-- **Evidence frame and safe-order recovery.**  If the actual spatial-evidence compiler
succeeds at `evidence`, then the frame it used is the actual frame supplied by the
four-ligand constructor, and the safe tracked order it used is exactly the executable
safe order at that frame.  No label or geometry is assumed. -/
theorem frame_and_safeTracked_of_spatialEvidence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (evidence : input.LocalizedOccurrenceRule45SpatialEvidence carrierFuel)
    (computed : input.localizedOccurrenceRule45SpatialEvidence? target view = some evidence) :
    evidence.frame = frame ∧
      input.safeLocalizedOccurrenceRule45TrackedOrder? target view frame =
        some evidence.tracked := by
  unfold localizedOccurrenceRule45SpatialEvidence? at computed
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp [centerComputed] at computed
  | some center =>
      cases actualFrame : input.localizedOccurrenceFourLigandFrame? target with
      | none => simp [centerComputed, actualFrame] at computed
      | some foundFrame =>
          have foundEq : foundFrame = frame :=
            Option.some.inj (actualFrame.symm.trans frameComputed)
          cases safeComputed : input.safeLocalizedOccurrenceRule45TrackedOrder?
              target view foundFrame with
          | none => simp [centerComputed, actualFrame, safeComputed] at computed
          | some tracked =>
              cases pointsComputed : tracked.highestFirst.mapM (fun index =>
                  input.localizedRerootCursorSpatialPoint? (foundFrame.cursorAt index)) with
              | none =>
                  simp [centerComputed, actualFrame, safeComputed, pointsComputed] at computed
              | some points =>
                  simp [centerComputed, actualFrame, safeComputed, pointsComputed] at computed
                  cases computed
                  subst foundEq
                  exact ⟨rfl, safeComputed⟩








theorem localizedOccurrenceRule45Descriptor?_sparse_of_separatedFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (separated : input.ConstitutionallyAtomicNumberSeparatedFrame frame) :
    LocalizedRule4bSparseLabel
      (input.localizedOccurrenceRule45Descriptor? target view) := by
  unfold localizedOccurrenceRule45Descriptor?
  cases evidenceComputed : input.localizedOccurrenceRule45SpatialEvidence? target view with
  | none => simp [evidenceComputed]
  | some evidence =>
      cases rawComputed : descriptorOfPriorityOrderedPoints? evidence.points with
      | none => simp [evidenceComputed, rawComputed]
      | some raw =>
          obtain ⟨_frameEq, safeComputed⟩ :=
            input.frame_and_safeTracked_of_spatialEvidence target view frame
              frameComputed evidence evidenceComputed
          obtain ⟨tracked, safeTracked, _canonical, _permutation, _strict, pseudoZero⟩ :=
            input.exists_localizedConstitutionalFrame_safeTrackedOrder
              target view frame
              (input.localizedOccurrenceFourLigandFrame?_sound target frame frameComputed)
              separated
          have trackedEq : evidence.tracked = tracked :=
            Option.some.inj (safeComputed.symm.trans safeTracked)
          subst trackedEq
          exact Or.inr ⟨raw, by simp [rawComputed, pseudoZero]⟩

/-- The reference state is sparse at a target carrying a separated actual frame. -/
theorem referenceState_sparse_of_actualPhysicalZSeparatedFrame
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (separatedFrame : ActualPhysicalZSeparatedFrame input target) :
    LocalizedRule4bSparseLabel
      (LocalizedUniversalReference.referenceState input target) := by
  obtain ⟨frame, frameComputed, separated⟩ := separatedFrame
  rw [LocalizedUniversalReference.referenceState_eq_bareRule45Descriptor_of_noDoubleRecords
    input noDouble target]
  exact input.certified.localizedOccurrenceRule45Descriptor?_sparse_of_separatedFrame
    target
    (input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) target)
    frame frameComputed separated

/-! ## Fuel adequacy and top-root binding -/

/-- The universal carrier fuel is adequate for the physical frame constructor: the certified
molecule's atom count is at most `atomCount + 1`. -/
theorem carrierFuel_adequate (input : LocalizedUniversalReference.Input) :
    input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
  dsimp [LocalizedUniversalReference.carrierFuel,
    LocalizedExtendedShortCircuit.carrierFuel, LocalizedReference.carrierFuel,
    LocalizedReference.Input.molecule]
  omega









theorem dependency_current_ne_topAtom_of_finalOccurrence
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (topCenter : input.certified.TetrahedralCenter)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (dependency : input.certified.LocalizedDepthDependency cursor.occurrence
      (input.certified.localizedFinalOccurrence
        (LocalizedUniversalReference.carrierFuel input) topCenter))
    (currentEq : cursor.occurrence.1.node.current? = some topCenter.1) :
    False := by
  let finalOcc : input.certified.LocalizedCIPOccurrence
      (LocalizedUniversalReference.carrierFuel input) :=
    input.certified.localizedFinalOccurrence
      (LocalizedUniversalReference.carrierFuel input) topCenter
  have finalCurrent : finalOcc.1.node.current? = some topCenter.1 := by
    dsimp only [finalOcc]
    rw [AuxiliaryContextIntegrity.localizedFinalOccurrence_node input.certified
      (LocalizedUniversalReference.carrierFuel input) topCenter]
    rfl
  have sameCurrent : cursor.occurrence.1.node.current? = finalOcc.1.node.current? := by
    rw [currentEq, finalCurrent]
  have equal : cursor.occurrence = finalOcc :=
    input.certified.localizedCIPOccurrence_current_injective_at_fixedRoot
      singleBonded acyclic cursor.occurrence finalOcc dependency.1 sameCurrent
  have depth := dependency.2
  rw [equal] at depth
  exact Nat.lt_irrefl _ depth

/-! ## Physical rigid Z-separated calibration certificate -/









structure ActualPhysicalRigidSeparatedCertificate
    (input : LocalizedUniversalReference.Input)
    (target : LocalizedUniversalReference.Occurrence input) where
  /-- The actual physical multi-center molecule. -/
  m : MultiCenterMolecule input.certified.Atom
  /-- Its molecular graph is exactly the certified input graph. -/
  graphEq : m.mol = input.certified.moleculeGraph
  /-- The distinguished physical center. -/
  center : m.Center
  /-- The distinguished center is the target's current physical atom. -/
  centerAt : target.1.node.current? = some center.1
  /-- The physical configuration whose signs are compared. -/
  cfg : m.Configuration
  /-- Physical coordinates in the molecule's own ligand enumeration. -/
  physicalPointAt : Fin 4 → CartesianPoint3
  /-- Atomic numbers of the four physical ligands are pairwise distinct. -/
  zInjective : Function.Injective (fun i => m.mol.atomZ (m.ligandAtomAt center i))
  /-- Every physical ligand atom has exactly the stated coordinate. -/
  pointAt : ∀ i, input.certified.spatialPointAt? (m.ligandAtomAt center i) =
    some (physicalPointAt i)
  /-- The physical configuration is nondegenerate. -/
  nondegenerate :
    CartesianPoint3.orientedVolume
      (physicalPointAt 0) (physicalPointAt 1) (physicalPointAt 2) (physicalPointAt 3) ≠ 0
  /-- The physical sign is the configuration sign at the distinguished center. -/
  sign_eq :
    TetraStereo.OneCenter.rationalVolumeSign
      (CartesianPoint3.orientedVolume
        (physicalPointAt 0) (physicalPointAt 1) (physicalPointAt 2) (physicalPointAt 3)) =
      m.configurationSign cfg center






theorem exists_frameAndSeparated_of_actualPhysicalRigidSeparatedCertificate
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : LocalizedUniversalReference.Occurrence input)
    (certificate : ActualPhysicalRigidSeparatedCertificate input target) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)),
      input.certified.localizedOccurrenceFourLigandFrame? target = some frame ∧
        (∀ i, (frame.cursorAt i).occurrence.1.node.current? =
          some (certificate.m.ligandAtomAt certificate.center (alpha i))) ∧
        input.certified.ConstitutionallyAtomicNumberSeparatedFrame frame := by
  obtain ⟨frame, alpha, frameComputed, matchLigand⟩ :=
    input.certified.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation
      singleBonded acyclic (carrierFuel_adequate input) target
      certificate.centerAt certificate.m certificate.graphEq certificate.center rfl
  refine ⟨frame, alpha, frameComputed, matchLigand, ?_⟩
  intro left right different equal
  have realLeft : (frame.cursorAt left).occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom :=
    input.certified.carrierOccurrence_provenance_real singleBonded acyclic
      (frame.cursorAt left).occurrence
  have realRight : (frame.cursorAt right).occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom :=
    input.certified.carrierOccurrence_provenance_real singleBonded acyclic
      (frame.cursorAt right).occurrence
  have leftZ : frame.rootAtomicNumberAt input.certified left =
      certificate.m.mol.atomZ
        (certificate.m.ligandAtomAt certificate.center (alpha left)) := by
    rw [TetraStereo.OneCenter.rootAtomicNumberAt_eq_atomZ_of_real input.certified frame left
      (certificate.m.ligandAtomAt certificate.center (alpha left))
      realLeft (matchLigand left), ← certificate.graphEq]
  have rightZ : frame.rootAtomicNumberAt input.certified right =
      certificate.m.mol.atomZ
        (certificate.m.ligandAtomAt certificate.center (alpha right)) := by
    rw [TetraStereo.OneCenter.rootAtomicNumberAt_eq_atomZ_of_real input.certified frame right
      (certificate.m.ligandAtomAt certificate.center (alpha right))
      realRight (matchLigand right), ← certificate.graphEq]
  have atomZEq : certificate.m.mol.atomZ
        (certificate.m.ligandAtomAt certificate.center (alpha left)) =
      certificate.m.mol.atomZ
        (certificate.m.ligandAtomAt certificate.center (alpha right)) := by
    rw [← leftZ, ← rightZ]
    exact equal
  exact different (alpha.injective (certificate.zInjective atomZEq))

/-! ## Physical terminal twins read `none` -/







theorem referenceState_eq_none_of_actualPhysicalTerminalTwinLeaves
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (twins : ActualPhysicalTerminalTwinLeaves input target) :
    LocalizedUniversalReference.referenceState input target = none := by
  obtain ⟨centerAtom, leftAtom, rightAtom, targetCurrent, tetrahedral,
    leftNeighbors, rightNeighbors, leftNe, zEq, massEq, _chargeEq⟩ := twins
  exact TetraStereo.OneCenter.referenceState_eq_none_of_physical_terminalTwinLeaves_of_tetrahedralRoot
    input singleBonded acyclic noDouble target centerAtom leftAtom rightAtom
    targetCurrent tetrahedral leftNeighbors rightNeighbors leftNe rootTetrahedral zEq massEq

/-! ## Sparse reference state on the physical source domain -/

/-- **Weak physical sparse domain.**  On a target whose original root is tetrahedral, any
of the three physical source alternatives makes the actual reference state `none` or an
uppercase chiral label.  The separated-frame alternative needs no coordinate or geometry
success; the twin alternative needs no supplied outward data. -/
theorem referenceState_sparse_of_actualPhysicalSparseSource
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (source : ActualPhysicalSparseSource input target) :
    LocalizedRule4bSparseLabel
      (LocalizedUniversalReference.referenceState input target) := by
  rcases source with noncandidate | separated | twins
  · exact Or.inl
      (referenceState_eq_none_of_actualPhysicalNoncandidate input noDouble target noncandidate)
  · exact referenceState_sparse_of_actualPhysicalZSeparatedFrame input noDouble target separated
  · exact Or.inl
      (referenceState_eq_none_of_actualPhysicalTerminalTwinLeaves input singleBonded acyclic
        noDouble target rootTetrahedral twins)

/-- **Actual dependency reader sparse.**  If every strict dependency cursor of `target` has a
physical sparse source and the target's stored root is tetrahedral, then the actual
dependency reader over the generated reference state returns `none` or an uppercase
chiral label at every cursor.  Non-dependencies read `none` by definition. -/
theorem localizedDependencyLabel_sparse_of_actualPhysicalSparseSource
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (source : ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      input.certified.LocalizedDepthDependency cursor.occurrence target →
        ActualPhysicalSparseSource input cursor.occurrence)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input)) :
    LocalizedRule4bSparseLabel
      (input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target)
        cursor) := by
  unfold localizedDependencyLabel
  split_ifs with dependency
  · have cursorRootTetrahedral :
        input.certified.moleculeGraph.IsTetrahedralCenter cursor.occurrence.1.root := by
      rw [dependency.1]
      exact rootTetrahedral
    exact referenceState_sparse_of_actualPhysicalSparseSource input singleBonded acyclic
      noDouble cursor.occurrence cursorRootTetrahedral (source cursor dependency)
  · exact Or.inl rfl

/-! ## Strong calibrated endpoint -/

/-- The actual dependency reader of the generated reference state at a target. -/
def actualReferenceDependencyRead
    (input : LocalizedUniversalReference.Input)
    (target : LocalizedUniversalReference.Occurrence input) :
    input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input) → Option LocalizedAuxiliaryLabel :=
  input.certified.localizedDependencyLabel target
    (input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) target)

/-- **Strong positive endpoint.**  A physical certificate yields an actual successful
four-ligand frame, its constructed physical ligand-slot permutation, root-Z separation, a safe
tracked order with zero pseudo comparisons, an actual uppercase chiral reference state, and the
normalized written sign `configurationSign cfg center * permHandedness alpha`.

The cofactor `permHandedness alpha` is the frame-slot reindexing sign; when `alpha` is even the
written sign is exactly the physical configuration sign. -/
theorem exists_chiral_of_actualPhysicalRigidSeparatedCertificate
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (certificate : ActualPhysicalRigidSeparatedCertificate input target) :
    ∃ (rs : RS) (tracked : TrackedLocalizedLigandOrder)
      (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)),
      input.certified.localizedOccurrenceFourLigandFrame? target = some frame ∧
        (∀ i, (frame.cursorAt i).occurrence.1.node.current? =
          some (certificate.m.ligandAtomAt certificate.center (alpha i))) ∧
        input.certified.ConstitutionallyAtomicNumberSeparatedFrame frame ∧
        tracked.pseudoComparisons = 0 ∧
        LocalizedUniversalReference.referenceState input target = some (.chiral rs) ∧
        TetraStereo.OneCenter.rationalVolumeSign
          (CartesianPoint3.orientedVolume
            (certificate.physicalPointAt (alpha 0))
            (certificate.physicalPointAt (alpha 1))
            (certificate.physicalPointAt (alpha 2))
            (certificate.physicalPointAt (alpha 3))) =
          certificate.m.configurationSign certificate.cfg certificate.center *
            TetraStereo.OneCenter.permHandedness alpha := by
  obtain ⟨frame, alpha, frameComputed, matchLigand, separated⟩ :=
    exists_frameAndSeparated_of_actualPhysicalRigidSeparatedCertificate
      input singleBonded acyclic target certificate
  let pointsAt : Fin 4 → CartesianPoint3 :=
    fun index => certificate.physicalPointAt (alpha index)
  have spatial : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt index) =
        some (pointsAt index) := by
    intro index
    simp [localizedRerootCursorSpatialPoint?, matchLigand index,
      certificate.pointAt (alpha index), pointsAt]
  let calibration : TetraStereo.OneCenter.PhysicalFrameCalibration
      certificate.m certificate.cfg certificate.center alpha pointsAt :=
    { physicalPointAt := certificate.physicalPointAt
      calibrated := fun _index => rfl
      nondegenerate := certificate.nondegenerate
      sign_eq := certificate.sign_eq }
  have writtenNondegenerate : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0 :=
    calibration.written_nondegenerate
  have writtenParity :
      AuthoritativeChemicalInput.RationalTetrahedralInputParity
        [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3]
        (TetraStereo.OneCenter.parityOfVolumeSign
          (TetraStereo.OneCenter.rationalVolumeSign
            (CartesianPoint3.orientedVolume
              (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3)))) :=
    TetraStereo.OneCenter.rationalTetrahedralInputParity_parityOfVolumeSign
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) writtenNondegenerate
  have tetrahedral :
      input.certified.moleculeGraph.IsTetrahedralCenter certificate.center.1 :=
    input.certified.isTetrahedralCenter_of_physicalLigandEquiv
      certificate.m certificate.graphEq certificate.center
  have memCenter : certificate.center.1 ∈ input.certified.tetrahedralCenterSet :=
    (input.certified.moleculeGraph.mem_tetrahedralCenterSet certificate.center.1).mpr
      tetrahedral
  let centerF : input.certified.TetrahedralCenter :=
    ⟨certificate.center.1, memCenter⟩
  have centerReal : input.certified.RealTetrahedralCenterNode target.1.node centerF :=
    ⟨input.certified.carrierOccurrence_provenance_real singleBonded acyclic target,
      certificate.centerAt⟩
  obtain ⟨tracked, _trackedComputed, pseudoZero, state⟩ :=
    referenceState_reader_eq_chiral_of_physicalFrame
      input noDouble target frame
      (input.certified.localizedOccurrenceFourLigandFrame?_sound target frame frameComputed)
      separated centerF centerReal pointsAt spatial
      (TetraStereo.OneCenter.parityOfVolumeSign
        (TetraStereo.OneCenter.rationalVolumeSign
          (CartesianPoint3.orientedVolume
            (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3))))
      writtenParity
  have signNormalized :
      TetraStereo.OneCenter.rationalVolumeSign
        (CartesianPoint3.orientedVolume
          (certificate.physicalPointAt (alpha 0))
          (certificate.physicalPointAt (alpha 1))
          (certificate.physicalPointAt (alpha 2))
          (certificate.physicalPointAt (alpha 3))) =
        certificate.m.configurationSign certificate.cfg certificate.center *
          TetraStereo.OneCenter.permHandedness alpha := by
    simpa [pointsAt] using calibration.sign_eq_configurationSign_mul
  exact ⟨_, tracked, frame, alpha, frameComputed, matchLigand, separated,
    pseudoZero, state, signNormalized⟩

/-! ## Strong physical source disjunction -/

/-- The strong physical source domain: physically not a detected candidate, or physical terminal
twins, or a full rigid Z-separated calibration certificate.  The last alternative is a
`Nonempty` because it is a structure of actual physical data. -/
def ActualPhysicalStrongSource
    (input : LocalizedUniversalReference.Input)
    (target : LocalizedUniversalReference.Occurrence input) : Prop :=
  ActualPhysicalNoncandidate input target ∨
    ActualPhysicalTerminalTwinLeaves input target ∨
      Nonempty (ActualPhysicalRigidSeparatedCertificate input target)

/-- **Strong case API.**  On the strong physical source domain, each alternative is returned
together with its actual reader outcome: `none` for noncandidates and physical terminal twins,
and an actual uppercase chiral label for rigid Z-separated calibrated certificates. -/
theorem actualPhysicalStrongSource_cases
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (source : ActualPhysicalStrongSource input target) :
    (ActualPhysicalNoncandidate input target ∧
        LocalizedUniversalReference.referenceState input target = none) ∨
      (ActualPhysicalTerminalTwinLeaves input target ∧
        LocalizedUniversalReference.referenceState input target = none) ∨
      (Nonempty (ActualPhysicalRigidSeparatedCertificate input target) ∧
        ∃ rs : RS,
          LocalizedUniversalReference.referenceState input target = some (.chiral rs)) := by
  rcases source with noncandidate | twins | certificate
  · exact Or.inl ⟨noncandidate,
      referenceState_eq_none_of_actualPhysicalNoncandidate input noDouble target noncandidate⟩
  · exact Or.inr (Or.inl ⟨twins,
      referenceState_eq_none_of_actualPhysicalTerminalTwinLeaves input singleBonded acyclic
        noDouble target rootTetrahedral twins⟩)
  · obtain ⟨certificate⟩ := certificate
    obtain ⟨rs, _tracked, _frame, _alpha, _computed, _match, _separated, _pseudo, state,
      _sign⟩ :=
      exists_chiral_of_actualPhysicalRigidSeparatedCertificate
        input singleBonded acyclic noDouble target certificate
    exact Or.inr (Or.inr ⟨⟨certificate⟩, ⟨rs, state⟩⟩)





theorem actualPhysicalZSeparatedFrame_of_actualPhysicalRigidSeparatedCertificate
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : LocalizedUniversalReference.Occurrence input)
    (certificate : ActualPhysicalRigidSeparatedCertificate input target) :
    ActualPhysicalZSeparatedFrame input target := by
  obtain ⟨frame, _alpha, frameComputed, _match, separated⟩ :=
    exists_frameAndSeparated_of_actualPhysicalRigidSeparatedCertificate
      input singleBonded acyclic target certificate
  exact ⟨frame, frameComputed, separated⟩

/-- Every strong physical source is a weak physical sparse source. -/
theorem actualPhysicalSparseSource_of_actualPhysicalStrongSource
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : LocalizedUniversalReference.Occurrence input)
    (source : ActualPhysicalStrongSource input target) :
    ActualPhysicalSparseSource input target := by
  rcases source with noncandidate | twins | certificate
  · exact Or.inl noncandidate
  · exact Or.inr (Or.inr twins)
  · obtain ⟨certificate⟩ := certificate
    exact Or.inr (Or.inl
      (actualPhysicalZSeparatedFrame_of_actualPhysicalRigidSeparatedCertificate
        input singleBonded acyclic target certificate))

/-- **Inventory transfer.**  A per-dependency strong physical inventory yields a per-dependency
weak sparse source, with no additional frame premise. -/
theorem actualPhysicalSparseSource_of_strongInventory
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : LocalizedUniversalReference.Occurrence input)
    (inventory : ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      input.certified.LocalizedDepthDependency cursor.occurrence target →
        ActualPhysicalStrongSource input cursor.occurrence) :
    ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      input.certified.LocalizedDepthDependency cursor.occurrence target →
        ActualPhysicalSparseSource input cursor.occurrence :=
  fun cursor dependency =>
    actualPhysicalSparseSource_of_actualPhysicalStrongSource input singleBonded acyclic
      cursor.occurrence (inventory cursor dependency)

/-- The actual dependency reader is sparse under a per-cursor strong physical inventory. -/
theorem actualReferenceDependencyRead_sparse_of_strongInventory
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (inventory : ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      input.certified.LocalizedDepthDependency cursor.occurrence target →
        ActualPhysicalStrongSource input cursor.occurrence) :
    ∀ cursor, LocalizedRule4bSparseLabel
      (actualReferenceDependencyRead input target cursor) := by
  intro cursor
  exact localizedDependencyLabel_sparse_of_actualPhysicalSparseSource
    input singleBonded acyclic noDouble target rootTetrahedral
    (actualPhysicalSparseSource_of_strongInventory input singleBonded acyclic target inventory)
    cursor

/-! ## Geometry-free physical neighbor-Z domain -/

/-- The target's current atom is a physical multi-center center on a molecule with the certified
graph, and atomic number is injective on that molecule's own ligand enumeration.  No frame,
coordinates, nondegeneracy, calibration or label is mentioned. -/
def ActualPhysicalNeighborZInjective
    (input : LocalizedUniversalReference.Input)
    (target : LocalizedUniversalReference.Occurrence input) : Prop :=
  ∃ (m : MultiCenterMolecule input.certified.Atom)
    (_graphEq : m.mol = input.certified.moleculeGraph)
    (center : m.Center),
    target.1.node.current? = some center.1 ∧
      Function.Injective (fun i => m.mol.atomZ (m.ligandAtomAt center i))

/-- Physical ligand atomic-number injectivity makes the actual frame root-Z-separated.  The
argument only uses real provenance of the actual frame slots and the constructed ligand-slot
permutation; no geometry, frame success or separation is assumed. -/
theorem constitutionallyAtomicNumberSeparatedFrame_of_physicalLigandZInjective
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    {m : MultiCenterMolecule input.certified.Atom}
    (graphEq : m.mol = input.certified.moleculeGraph)
    (center : m.Center)
    (alpha : Equiv.Perm (Fin 4))
    (matchLigand : ∀ i, (frame.cursorAt i).occurrence.1.node.current? =
      some (m.ligandAtomAt center (alpha i)))
    (zInjective : Function.Injective (fun i => m.mol.atomZ (m.ligandAtomAt center i))) :
    input.certified.ConstitutionallyAtomicNumberSeparatedFrame frame := by
  intro left right different equal
  have realLeft : (frame.cursorAt left).occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom :=
    input.certified.carrierOccurrence_provenance_real singleBonded acyclic
      (frame.cursorAt left).occurrence
  have realRight : (frame.cursorAt right).occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom :=
    input.certified.carrierOccurrence_provenance_real singleBonded acyclic
      (frame.cursorAt right).occurrence
  have leftZ : frame.rootAtomicNumberAt input.certified left =
      m.mol.atomZ (m.ligandAtomAt center (alpha left)) := by
    rw [TetraStereo.OneCenter.rootAtomicNumberAt_eq_atomZ_of_real input.certified frame left
      (m.ligandAtomAt center (alpha left)) realLeft (matchLigand left), ← graphEq]
  have rightZ : frame.rootAtomicNumberAt input.certified right =
      m.mol.atomZ (m.ligandAtomAt center (alpha right)) := by
    rw [TetraStereo.OneCenter.rootAtomicNumberAt_eq_atomZ_of_real input.certified frame right
      (m.ligandAtomAt center (alpha right)) realRight (matchLigand right), ← graphEq]
  have atomZEq : m.mol.atomZ (m.ligandAtomAt center (alpha left)) =
      m.mol.atomZ (m.ligandAtomAt center (alpha right)) := by
    rw [← leftZ, ← rightZ]
    exact equal
  exact different (alpha.injective (zInjective atomZEq))




theorem actualPhysicalZSeparatedFrame_of_actualPhysicalNeighborZInjective
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : LocalizedUniversalReference.Occurrence input)
    (physical : ActualPhysicalNeighborZInjective input target) :
    ActualPhysicalZSeparatedFrame input target := by
  obtain ⟨m, graphEq, center, centerAt, zInjective⟩ := physical
  obtain ⟨frame, alpha, frameComputed, matchLigand⟩ :=
    input.certified.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation
      singleBonded acyclic (carrierFuel_adequate input) target centerAt m graphEq center rfl
  exact ⟨frame, frameComputed,
    constitutionallyAtomicNumberSeparatedFrame_of_physicalLigandZInjective
      input singleBonded acyclic frame graphEq center alpha matchLigand zInjective⟩

/-- The geometry-free physical source domain: physically not a candidate, or physical neighbor-Z
injectivity, or physical terminal twins. -/
def ActualPhysicalGeometryFreeSparseSource
    (input : LocalizedUniversalReference.Input)
    (target : LocalizedUniversalReference.Occurrence input) : Prop :=
  ActualPhysicalNoncandidate input target ∨
    ActualPhysicalNeighborZInjective input target ∨
      ActualPhysicalTerminalTwinLeaves input target

/-- The geometry-free physical source domain is contained in the weak sparse source domain. -/
theorem actualPhysicalSparseSource_of_actualPhysicalGeometryFreeSparseSource
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : LocalizedUniversalReference.Occurrence input)
    (source : ActualPhysicalGeometryFreeSparseSource input target) :
    ActualPhysicalSparseSource input target := by
  rcases source with noncandidate | physical | twins
  · exact Or.inl noncandidate
  · exact Or.inr (Or.inl
      (actualPhysicalZSeparatedFrame_of_actualPhysicalNeighborZInjective
        input singleBonded acyclic target physical))
  · exact Or.inr (Or.inr twins)




theorem referenceState_sparse_of_actualPhysicalGeometryFreeSparseSource
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (source : ActualPhysicalGeometryFreeSparseSource input target) :
    LocalizedRule4bSparseLabel
      (LocalizedUniversalReference.referenceState input target) :=
  referenceState_sparse_of_actualPhysicalSparseSource input singleBonded acyclic noDouble
    target rootTetrahedral
    (actualPhysicalSparseSource_of_actualPhysicalGeometryFreeSparseSource
      input singleBonded acyclic target source)

/-- The actual dependency reader is sparse under a per-cursor geometry-free physical inventory. -/
theorem actualReferenceDependencyRead_sparse_of_geometryFreeInventory
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (inventory : ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      input.certified.LocalizedDepthDependency cursor.occurrence target →
        ActualPhysicalGeometryFreeSparseSource input cursor.occurrence) :
    ∀ cursor, LocalizedRule4bSparseLabel
      (actualReferenceDependencyRead input target cursor) := by
  intro cursor
  exact localizedDependencyLabel_sparse_of_actualPhysicalSparseSource
    input singleBonded acyclic noDouble target rootTetrahedral
    (fun cursor dependency =>
      actualPhysicalSparseSource_of_actualPhysicalGeometryFreeSparseSource
        input singleBonded acyclic cursor.occurrence (inventory cursor dependency))
    cursor

/-- **A detected tetrahedral top center makes the final occurrence's stored root tetrahedral.** -/
theorem isTetrahedralCenter_root_of_localizedFinalOccurrence
    (input : LocalizedUniversalReference.Input)
    (topCenter : input.certified.TetrahedralCenter) :
    input.certified.moleculeGraph.IsTetrahedralCenter
      (input.certified.localizedFinalOccurrence
        (LocalizedUniversalReference.carrierFuel input) topCenter).1.root := by
  rw [AuxiliaryContextIntegrity.localizedFinalOccurrence_root input.certified
    (LocalizedUniversalReference.carrierFuel input) topCenter]
  exact (input.certified.moleculeGraph.mem_tetrahedralCenterSet topCenter.1).mp topCenter.2

/-- **Actual top-root dependency reader.**  At the actual final occurrence of a detected
tetrahedral top center, every cursor of the actual dependency reader of the generated reference
state reads `none` or an uppercase chiral label, assuming the geometry-free physical source at
every strict dependency cursor.  No base root-tetrahedral premise remains. -/
theorem actualReferenceDependencyRead_sparse_of_geometryFreeFinalOccurrence
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (topCenter : input.certified.TetrahedralCenter)
    (inventory : ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      input.certified.LocalizedDepthDependency cursor.occurrence
        (input.certified.localizedFinalOccurrence
          (LocalizedUniversalReference.carrierFuel input) topCenter) →
        ActualPhysicalGeometryFreeSparseSource input cursor.occurrence) :
    ∀ cursor, LocalizedRule4bSparseLabel
      (actualReferenceDependencyRead input
        (input.certified.localizedFinalOccurrence
          (LocalizedUniversalReference.carrierFuel input) topCenter) cursor) :=
  actualReferenceDependencyRead_sparse_of_geometryFreeInventory
    input singleBonded acyclic noDouble
    (input.certified.localizedFinalOccurrence
      (LocalizedUniversalReference.carrierFuel input) topCenter)
    (isTetrahedralCenter_root_of_localizedFinalOccurrence input topCenter)
    inventory







theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_sparse_of_physicalInventory
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (inventory : ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      input.certified.LocalizedDepthDependency cursor.occurrence target →
        ActualPhysicalStrongSource input cursor.occurrence)
    (stage : LocalizedCumulativeRule45Stage)
    (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (key : input.certified.LocalizedRerootCumulativeRule45Key)
    (computed : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      stage (actualReferenceDependencyRead input target) fuel cursor = some key) :
    LocalizedLabelLayersSparse key.labels :=
  input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_sparse
    stage (actualReferenceDependencyRead input target)
    (actualReferenceDependencyRead_sparse_of_strongInventory
      input singleBonded acyclic noDouble target rootTetrahedral inventory)
    fuel cursor key computed



theorem actual_stage_alignment_capstone_of_physicalInventory
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (inventory : ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      input.certified.LocalizedDepthDependency cursor.occurrence target →
        ActualPhysicalStrongSource input cursor.occurrence)
    (leftCursor rightCursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (rule4aLeftFuel rule4aRightFuel rule4bLeftFuel rule4bRightFuel : Nat)
    (leftReference rightReference : RS)
    (aL aR bL bR : input.certified.LocalizedRerootCumulativeRule45Key)
    (aLComputed : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a (actualReferenceDependencyRead input target) rule4aLeftFuel leftCursor = some aL)
    (aRComputed : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a (actualReferenceDependencyRead input target) rule4aRightFuel rightCursor = some aR)
    (bLComputed : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b leftReference) (actualReferenceDependencyRead input target) rule4bLeftFuel
      leftCursor = some bL)
    (bRComputed : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b rightReference) (actualReferenceDependencyRead input target) rule4bRightFuel
      rightCursor = some bR)
    (rule4aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys aL aR = Ordering.eq)
    (descriptorTie : OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority bL.descriptor bR.descriptor = Ordering.eq) :
    (input.certified.localizedRerootCumulativeRule45Observable bL =
        input.certified.localizedRerootCumulativeRule45Observable bR) ∧
      bR.labels = if leftReference = rightReference then bL.labels
        else reflectUppercaseRankedLabels bL.labels :=
  input.certified.actual_stage_alignment_capstone
    (actualReferenceDependencyRead input target)
    (actualReferenceDependencyRead_sparse_of_strongInventory
      input singleBonded acyclic noDouble target rootTetrahedral inventory)
    leftCursor rightCursor rule4aLeftFuel rule4aRightFuel rule4bLeftFuel rule4bRightFuel
    leftReference rightReference aL aR bL bR
    aLComputed aRComputed bLComputed bRComputed rule4aTie descriptorTie




theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_sparse_of_geometryFreeInventory
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (inventory : ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      input.certified.LocalizedDepthDependency cursor.occurrence target →
        ActualPhysicalGeometryFreeSparseSource input cursor.occurrence)
    (stage : LocalizedCumulativeRule45Stage)
    (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (key : input.certified.LocalizedRerootCumulativeRule45Key)
    (computed : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      stage (actualReferenceDependencyRead input target) fuel cursor = some key) :
    LocalizedLabelLayersSparse key.labels :=
  input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_sparse
    stage (actualReferenceDependencyRead input target)
    (actualReferenceDependencyRead_sparse_of_geometryFreeInventory
      input singleBonded acyclic noDouble target rootTetrahedral inventory)
    fuel cursor key computed




theorem actual_stage_alignment_capstone_of_geometryFreeInventory
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (inventory : ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      input.certified.LocalizedDepthDependency cursor.occurrence target →
        ActualPhysicalGeometryFreeSparseSource input cursor.occurrence)
    (leftCursor rightCursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (rule4aLeftFuel rule4aRightFuel rule4bLeftFuel rule4bRightFuel : Nat)
    (leftReference rightReference : RS)
    (aL aR bL bR : input.certified.LocalizedRerootCumulativeRule45Key)
    (aLComputed : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a (actualReferenceDependencyRead input target) rule4aLeftFuel leftCursor = some aL)
    (aRComputed : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a (actualReferenceDependencyRead input target) rule4aRightFuel rightCursor = some aR)
    (bLComputed : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b leftReference) (actualReferenceDependencyRead input target) rule4bLeftFuel
      leftCursor = some bL)
    (bRComputed : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b rightReference) (actualReferenceDependencyRead input target) rule4bRightFuel
      rightCursor = some bR)
    (rule4aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys aL aR = Ordering.eq)
    (descriptorTie : OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority bL.descriptor bR.descriptor = Ordering.eq) :
    (input.certified.localizedRerootCumulativeRule45Observable bL =
        input.certified.localizedRerootCumulativeRule45Observable bR) ∧
      bR.labels = if leftReference = rightReference then bL.labels
        else reflectUppercaseRankedLabels bL.labels :=
  input.certified.actual_stage_alignment_capstone
    (actualReferenceDependencyRead input target)
    (actualReferenceDependencyRead_sparse_of_geometryFreeInventory
      input singleBonded acyclic noDouble target rootTetrahedral inventory)
    leftCursor rightCursor rule4aLeftFuel rule4aRightFuel rule4bLeftFuel rule4bRightFuel
    leftReference rightReference aL aR bL bR
    aLComputed aRComputed bLComputed bRComputed rule4aTie descriptorTie




theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_sparse_of_geometryFreeFinalOccurrence
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (topCenter : input.certified.TetrahedralCenter)
    (inventory : ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      input.certified.LocalizedDepthDependency cursor.occurrence
        (input.certified.localizedFinalOccurrence
          (LocalizedUniversalReference.carrierFuel input) topCenter) →
        ActualPhysicalGeometryFreeSparseSource input cursor.occurrence)
    (stage : LocalizedCumulativeRule45Stage)
    (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (key : input.certified.LocalizedRerootCumulativeRule45Key)
    (computed : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      stage
      (actualReferenceDependencyRead input
        (input.certified.localizedFinalOccurrence
          (LocalizedUniversalReference.carrierFuel input) topCenter))
      fuel cursor = some key) :
    LocalizedLabelLayersSparse key.labels :=
  buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_sparse_of_geometryFreeInventory
    input singleBonded acyclic noDouble
    (input.certified.localizedFinalOccurrence
      (LocalizedUniversalReference.carrierFuel input) topCenter)
    (isTetrahedralCenter_root_of_localizedFinalOccurrence input topCenter)
    inventory stage fuel cursor key computed




theorem actual_stage_alignment_capstone_of_geometryFreeFinalOccurrence
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (topCenter : input.certified.TetrahedralCenter)
    (inventory : ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      input.certified.LocalizedDepthDependency cursor.occurrence
        (input.certified.localizedFinalOccurrence
          (LocalizedUniversalReference.carrierFuel input) topCenter) →
        ActualPhysicalGeometryFreeSparseSource input cursor.occurrence)
    (leftCursor rightCursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (rule4aLeftFuel rule4aRightFuel rule4bLeftFuel rule4bRightFuel : Nat)
    (leftReference rightReference : RS)
    (aL aR bL bR : input.certified.LocalizedRerootCumulativeRule45Key)
    (aLComputed : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a
      (actualReferenceDependencyRead input
        (input.certified.localizedFinalOccurrence
          (LocalizedUniversalReference.carrierFuel input) topCenter))
      rule4aLeftFuel leftCursor = some aL)
    (aRComputed : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a
      (actualReferenceDependencyRead input
        (input.certified.localizedFinalOccurrence
          (LocalizedUniversalReference.carrierFuel input) topCenter))
      rule4aRightFuel rightCursor = some aR)
    (bLComputed : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b leftReference)
      (actualReferenceDependencyRead input
        (input.certified.localizedFinalOccurrence
          (LocalizedUniversalReference.carrierFuel input) topCenter))
      rule4bLeftFuel leftCursor = some bL)
    (bRComputed : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b rightReference)
      (actualReferenceDependencyRead input
        (input.certified.localizedFinalOccurrence
          (LocalizedUniversalReference.carrierFuel input) topCenter))
      rule4bRightFuel rightCursor = some bR)
    (rule4aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys aL aR = Ordering.eq)
    (descriptorTie : OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority bL.descriptor bR.descriptor = Ordering.eq) :
    (input.certified.localizedRerootCumulativeRule45Observable bL =
        input.certified.localizedRerootCumulativeRule45Observable bR) ∧
      bR.labels = if leftReference = rightReference then bL.labels
        else reflectUppercaseRankedLabels bL.labels :=
  actual_stage_alignment_capstone_of_geometryFreeInventory
    input singleBonded acyclic noDouble
    (input.certified.localizedFinalOccurrence
      (LocalizedUniversalReference.carrierFuel input) topCenter)
    (isTetrahedralCenter_root_of_localizedFinalOccurrence input topCenter)
    inventory leftCursor rightCursor rule4aLeftFuel rule4aRightFuel rule4bLeftFuel
    rule4bRightFuel leftReference rightReference aL aR bL bR
    aLComputed aRComputed bLComputed bRComputed rule4aTie descriptorTie

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.referenceState_eq_none_of_actualPhysicalNoncandidate
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frame_and_safeTracked_of_spatialEvidence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45Descriptor?_sparse_of_separatedFrame
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.referenceState_sparse_of_actualPhysicalZSeparatedFrame
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.referenceState_eq_none_of_actualPhysicalTerminalTwinLeaves
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.referenceState_sparse_of_actualPhysicalSparseSource
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDependencyLabel_sparse_of_actualPhysicalSparseSource
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierFuel_adequate
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.dependency_current_ne_topAtom_of_finalOccurrence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualPhysicalNoncandidate
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualPhysicalZSeparatedFrame
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualPhysicalTerminalTwinLeaves
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualPhysicalSparseSource
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualPhysicalRigidSeparatedCertificate
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_frameAndSeparated_of_actualPhysicalRigidSeparatedCertificate
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualReferenceDependencyRead
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_chiral_of_actualPhysicalRigidSeparatedCertificate
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualPhysicalStrongSource
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPhysicalStrongSource_cases
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPhysicalZSeparatedFrame_of_actualPhysicalRigidSeparatedCertificate
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPhysicalSparseSource_of_actualPhysicalStrongSource
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPhysicalSparseSource_of_strongInventory
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualReferenceDependencyRead_sparse_of_strongInventory
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_sparse_of_physicalInventory
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actual_stage_alignment_capstone_of_physicalInventory
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualPhysicalNeighborZInjective
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.constitutionallyAtomicNumberSeparatedFrame_of_physicalLigandZInjective
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPhysicalZSeparatedFrame_of_actualPhysicalNeighborZInjective
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualPhysicalGeometryFreeSparseSource
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPhysicalSparseSource_of_actualPhysicalGeometryFreeSparseSource
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.referenceState_sparse_of_actualPhysicalGeometryFreeSparseSource
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualReferenceDependencyRead_sparse_of_geometryFreeInventory
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.isTetrahedralCenter_root_of_localizedFinalOccurrence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualReferenceDependencyRead_sparse_of_geometryFreeFinalOccurrence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_sparse_of_geometryFreeInventory
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actual_stage_alignment_capstone_of_geometryFreeInventory
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_sparse_of_geometryFreeFinalOccurrence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actual_stage_alignment_capstone_of_geometryFreeFinalOccurrence

end CertifiedLocalizedCIPInput

end OneCenter
end TetraStereo
