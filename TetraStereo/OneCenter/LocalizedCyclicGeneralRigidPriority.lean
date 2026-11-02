import TetraStereo.OneCenter.DeclarativeCIPBoundaryComponentReconstruction
import TetraStereo.OneCenter.LocalizedActualOutwardRule1bEquivalence
import TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback
import TetraStereo.OneCenter.LocalizedRootwardSeparatedArmBridge
import TetraStereo.OneCenter.LocalizedConstitutionallyRigidFrameNormalization
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000







































namespace TetraStereo.OneCenter
namespace LocalizedCyclicGeneralRigidPriority

open CertifiedLocalizedCIPInput

/-! ## Reader-free constitutional separation -/

section Separation

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-- Two cursors are constitutionally separated: every pair of successful rule-major builds at
them, at any stages, readers and fuels, has a non-tied constitutional comparison. -/
def ConstitutionallySeparated (left right : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∀ (stageL stageR : LocalizedCumulativeRule45Stage)
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuelL fuelR : Nat) (keyL keyR : input.LocalizedRerootCumulativeRule45Key),
    input.buildRuleMajorCumulativeWithRead? stageL readL fuelL left = some keyL →
    input.buildRuleMajorCumulativeWithRead? stageR readR fuelR right = some keyR →
    OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional ≠ Ordering.eq

/-- One pair of successful builds with a non-tied constitutional comparison separates the two
cursors for every stage, reader and fuel. -/
theorem constitutionallySeparated_of_builds
    {left right : input.LocalizedRerootCursor carrierFuel}
    {stageL stageR : LocalizedCumulativeRule45Stage}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuelL fuelR : Nat} {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (builtL : input.buildRuleMajorCumulativeWithRead? stageL readL fuelL left = some keyL)
    (builtR : input.buildRuleMajorCumulativeWithRead? stageR readR fuelR right = some keyR)
    (strict : OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional ≠
      Ordering.eq) :
    ConstitutionallySeparated left right := by
  intro stageL' stageR' readL' readR' fuelL' fuelR' keyL' keyR' builtL' builtR'
  rw [RetainedConstitutionalReaderIndependence.ruleMajorBuild_constitutional_compare_congr
    stageL' stageR' stageL stageR readL' readR' readL readR left right
    builtL' builtR' builtL builtR]
  exact strict

/-- Separation is symmetric. -/
theorem ConstitutionallySeparated.symm
    {left right : input.LocalizedRerootCursor carrierFuel}
    (separated : ConstitutionallySeparated left right) :
    ConstitutionallySeparated right left := by
  intro stageL stageR readL readR fuelL fuelR keyL keyR builtL builtR tie
  have columns :=
    (officialRuleMajorKey_compare_eq_iff keyL.constitutional keyR.constitutional).mp tie
  exact separated stageR stageL readR readL fuelR fuelL keyR keyL builtR builtL
    ((officialRuleMajorKey_compare_eq_iff keyR.constitutional keyL.constitutional).mpr
      ⟨columns.1.symm, columns.2.1.symm, columns.2.2.symm⟩)

/-- `left` is constitutionally above `right`: every pair of successful rule-major builds at them,
at any stages, readers and fuels, compares `gt` on the constitutional columns. -/
def ConstitutionallyAbove (left right : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∀ (stageL stageR : LocalizedCumulativeRule45Stage)
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuelL fuelR : Nat) (keyL keyR : input.LocalizedRerootCumulativeRule45Key),
    input.buildRuleMajorCumulativeWithRead? stageL readL fuelL left = some keyL →
    input.buildRuleMajorCumulativeWithRead? stageR readR fuelR right = some keyR →
    OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional = Ordering.gt

/-- One pair of successful builds comparing `gt` makes `left` constitutionally above `right`
for every stage, reader and fuel. -/
theorem constitutionallyAbove_of_builds
    {left right : input.LocalizedRerootCursor carrierFuel}
    {stageL stageR : LocalizedCumulativeRule45Stage}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuelL fuelR : Nat} {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (builtL : input.buildRuleMajorCumulativeWithRead? stageL readL fuelL left = some keyL)
    (builtR : input.buildRuleMajorCumulativeWithRead? stageR readR fuelR right = some keyR)
    (above : OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional =
      Ordering.gt) :
    ConstitutionallyAbove left right := by
  intro stageL' stageR' readL' readR' fuelL' fuelR' keyL' keyR' builtL' builtR'
  rw [RetainedConstitutionalReaderIndependence.ruleMajorBuild_constitutional_compare_congr
    stageL' stageR' stageL stageR readL' readR' readL readR left right
    builtL' builtR' builtL builtR]
  exact above

/-- A Rule-1a decision between two Rule-4a builds of the older cumulative builder, at one reader
and one fuel, separates the cursors. -/
theorem constitutionallySeparated_of_rule1a_ne
    {left right : input.LocalizedRerootCursor carrierFuel}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (builtL : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a read fuel left =
      some keyL)
    (builtR : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a read fuel right =
      some keyR)
    (decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyL.constitutional.rule1a keyR.constitutional.rule1a ≠ Ordering.eq) :
    ConstitutionallySeparated left right := by
  refine constitutionallySeparated_of_builds
    ((input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized read fuel left).trans builtL)
    ((input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized read fuel right).trans builtR)
    ?_
  intro tie
  apply decisive
  exact (compareSparseLayers_compareNat_eq_iff _ _).mpr
    ((officialRuleMajorKey_compare_eq_iff _ _).mp tie).1

/-- Off-diagonal constitutional strictness of a four-ligand frame. -/
def FrameConstitutionalStrict (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    Prop :=
  ∀ left right : Fin 4, left ≠ right →
    ConstitutionallySeparated (frame.cursorAt left) (frame.cursorAt right)

/-- Strictness from one separated distinguished slot and separated remaining pairs. -/
theorem frameConstitutionalStrict_of_distinguished
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) (distinguished : Fin 4)
    (fromDistinguished : ∀ other, other ≠ distinguished →
      ConstitutionallySeparated (frame.cursorAt distinguished) (frame.cursorAt other))
    (remaining : ∀ left right, left ≠ distinguished → right ≠ distinguished → left ≠ right →
      ConstitutionallySeparated (frame.cursorAt left) (frame.cursorAt right)) :
    FrameConstitutionalStrict frame := by
  intro left right distinct
  by_cases leftD : left = distinguished
  · subst leftD
    exact fromDistinguished right (Ne.symm distinct)
  · by_cases rightD : right = distinguished
    · subst rightD
      exact (fromDistinguished left leftD).symm
    · exact remaining left right leftD rightD distinct

/-- The accepted parent-slot Rule-1a separation, made reader-free. -/
theorem constitutionallySeparated_of_armRule1aSeparated
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    {distinguished : Fin 4}
    (separated : input.ArmConstitutionalRule1aSeparated frame distinguished) :
    ∀ other, other ≠ distinguished →
      ConstitutionallySeparated (frame.cursorAt distinguished) (frame.cursorAt other) := by
  intro other otherNe
  obtain ⟨keyD, builtD⟩ := input.exists_buildRuleMajorCumulativeWithRead_at_twice .rule4a
    (fun _ => none) (frame.cursorAt distinguished)
    (input.frameCursor_valid target frame computed distinguished)
  obtain ⟨keyO, builtO⟩ := input.exists_buildRuleMajorCumulativeWithRead_at_twice .rule4a
    (fun _ => none) (frame.cursorAt other) (input.frameCursor_valid target frame computed other)
  have oldD : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a (fun _ => none)
      (2 * (carrierFuel + 1)) (frame.cursorAt distinguished) = some keyD :=
    (input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized (fun _ => none)
      (2 * (carrierFuel + 1)) (frame.cursorAt distinguished)).symm.trans builtD
  have oldO : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a (fun _ => none)
      (2 * (carrierFuel + 1)) (frame.cursorAt other) = some keyO :=
    (input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized (fun _ => none)
      (2 * (carrierFuel + 1)) (frame.cursorAt other)).symm.trans builtO
  exact constitutionallySeparated_of_rule1a_ne oldD oldO
    (separated other otherNe keyD keyO oldD oldO)

/-- Every frame cursor is an actual executable child of the target-start cursor. -/
theorem frame_cursorAt_mem_executable
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (index : Fin 4) :
    frame.cursorAt index ∈ input.executableLocalizedRerootChildren
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) := by
  rw [← input.localizedOccurrenceFourLigandFrame_cursors_eq_executable target frame computed]
  exact List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index)

/-- Two outward frame slots form an actual outward sibling pair at the target-start cursor. -/
theorem outwardSiblingPair_of_frame
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    {left right : Fin 4}
    (leftOut : IsLocalizedActualFrameOutwardCursor input target (frame.cursorAt left))
    (rightOut : IsLocalizedActualFrameOutwardCursor input target (frame.cursorAt right)) :
    ∃ pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair input carrierFuel,
      pair.target = { occurrence := target, previous? := none } ∧
        pair.left = frame.cursorAt left ∧ pair.right = frame.cursorAt right := by
  obtain ⟨leftSlot, leftAddress⟩ := leftOut
  obtain ⟨rightSlot, rightAddress⟩ := rightOut
  refine LocalizedActualOutwardRule1bEquivalence.exists_actualOutwardSiblingPair_of_children
    input target (frame.cursorAt left) (frame.cursorAt right)
    (frame_cursorAt_mem_executable target frame computed left)
    (frame_cursorAt_mem_executable target frame computed right) ?_ ?_
  · rw [leftAddress]
    simp
  · rw [rightAddress]
    simp

/-- Distinct frame slots are distinct cursors. -/
theorem frame_cursorAt_ne
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    {left right : Fin 4} (distinct : left ≠ right) :
    frame.cursorAt left ≠ frame.cursorAt right := fun same =>
  distinct (input.localizedOccurrenceFourLigandFrame_cursorAt_injective target frame computed
    same)

end Separation

/-! ## The parent slot inside a tied root arm -/

section Parent

open LocalizedRootwardConstitutionalSeparation (carrierFuel)

/-- Inside a Rule-1a tied root arm, the actual parent slot of a real nonroot target is
reader-free separated from each other slot, and each other slot is outward. All premises are
the accepted bridge's: the root arm tie, the target's real provenance and its root-branch
membership. -/
theorem parentSlot_separated_of_rootArmRule1aTie
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (rootCursor : input.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : input.LocalizedCIPOccurrence (carrierFuel input))
    (targetReal : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (inside : input.RootBranchContains armCursor.occurrence target)
    (frame : input.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (nonroot : target.1.address ≠ []) :
    ∃ parentIndex : Fin 4,
      IsLocalizedActualFrameParentCursor input target (frame.cursorAt parentIndex) ∧
        ∀ other, other ≠ parentIndex →
          IsLocalizedActualFrameOutwardCursor input target (frame.cursorAt other) ∧
            ConstitutionallySeparated (frame.cursorAt parentIndex) (frame.cursorAt other) := by
  obtain ⟨parentIndex, _certificate, _parentEq, parentClass, others⟩ :=
    input.actualFrame_parentIndex target frame computed nonroot
  have separated := armConstitutionalRule1aSeparated_of_rootArmRule1aTie input singleBonded
    rootCursor rootAddress armCursor armCursor' armMem armMem' armDistinct armReal armReal'
    armRead armRead' armKey armKey' armBuilt armBuilt' tie target targetReal inside frame
    computed nonroot parentIndex parentClass
  refine ⟨parentIndex, parentClass, fun other otherNe => ⟨(others other otherNe).1, ?_⟩⟩
  exact constitutionallySeparated_of_armRule1aSeparated target frame computed separated other
    otherNe

/-- **Assembly seam for frame strictness.** Inside a Rule-1a tied root arm, a real nonroot target
whose outward frame pairs are separated has a constitutionally strict frame. The outward
hypothesis is the remaining upstream obligation, quantified over actual outward sibling pairs
of distinct cursors; it is not a final premise. -/
theorem frameConstitutionalStrict_of_rootArmRule1aTie
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (rootCursor : input.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : input.LocalizedCIPOccurrence (carrierFuel input))
    (targetReal : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (inside : input.RootBranchContains armCursor.occurrence target)
    (frame : input.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (nonroot : target.1.address ≠ [])
    (outward : ∀ pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair input
        (carrierFuel input),
      pair.target = { occurrence := target, previous? := none } →
      pair.left ≠ pair.right → ConstitutionallySeparated pair.left pair.right) :
    FrameConstitutionalStrict frame := by
  obtain ⟨parentIndex, _parentClass, parentSep⟩ :=
    parentSlot_separated_of_rootArmRule1aTie input singleBonded rootCursor rootAddress
      armCursor armCursor' armMem armMem' armDistinct armReal armReal' armRead armRead'
      armKey armKey' armBuilt armBuilt' tie target targetReal inside frame computed nonroot
  refine frameConstitutionalStrict_of_distinguished frame parentIndex
    (fun other otherNe => (parentSep other otherNe).2) ?_
  intro left right leftNe rightNe distinct
  obtain ⟨pair, pairTarget, pairLeft, pairRight⟩ :=
    outwardSiblingPair_of_frame target frame computed (parentSep left leftNe).1
      (parentSep right rightNe).1
  have separated := outward pair pairTarget (by
    rw [pairLeft, pairRight]
    exact frame_cursorAt_ne target frame computed distinct)
  rw [pairLeft, pairRight] at separated
  exact separated

end Parent

/-! ## Rigidity forbids same-boundary residual equivalences of distinct neighbors -/

section Rigidity

open RetainedCoherentSymmetry BoundaryComponentReconstruction

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A residual path-tree equivalence between two distinct neighbors `a ≠ b` of a boundary atom
`c`, with the same ordered boundary on both sides, contradicts constitutional rigidity at `c`.
The witnessed reconstruction gives a molecular automorphism fixing the whole boundary, hence
`c`, and sending `a` to `b`; rigidity forces it to fix `a`. -/
theorem sameBoundaryResidualEquiv_false_of_rigid {m : MoleculeGraph V} {B : List V}
    {c a b : V} (rigid : ConstitutionallyRigidGraphAt m c) (hc : c ∈ B) (ha : a ∉ B)
    (hca : m.Adj c a) (hab : a ≠ b) (e : ResidualPathTreeEquiv m B B a b) : False := by
  obtain ⟨π, hπ, hfix, hπab, -, -⟩ := exists_sameBoundary_automorphism e ha
  have fixedA : π a = a := rigid ⟨π, hπ⟩ (hfix c hc) a hca
  exact hab (fixedA.symm.trans hπab)

/-- Equivalent form: under rigidity at `c`, no same-boundary residual path-tree equivalence
relates two distinct outside neighbors of a boundary atom. -/
theorem isEmpty_sameBoundaryResidualEquiv_of_rigid {m : MoleculeGraph V} {B : List V}
    {c a b : V} (rigid : ConstitutionallyRigidGraphAt m c) (hc : c ∈ B) (ha : a ∉ B)
    (hca : m.Adj c a) (hab : a ≠ b) : IsEmpty (ResidualPathTreeEquiv m B B a b) :=
  ⟨fun e => sameBoundaryResidualEquiv_false_of_rigid rigid hc ha hca hab e⟩

end Rigidity

/-! ## Physical rigidity at the detected centers -/

/-- A physically calibrated general-rigid center is graph-rigid at its atom. -/
theorem constitutionallyRigidGraphAt_of_physicalGeneralRigid
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (center : input.detectedMultiCenterMolecule.Center)
    (calibrated : ActualPhysicalGeneralRigidCalibratedCenter input
      input.detectedMultiCenterMolecule cfg center) :
    ConstitutionallyRigidGraphAt input.moleculeGraph center.1 :=
  constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input center calibrated.1

/-! ## Endpoint: strictness at a rigid auxiliary target in a tied root arm -/

section Endpoint

open LocalizedRootwardConstitutionalSeparation (carrierFuel)

/-- **Constitutional off-diagonal strictness at a rigid auxiliary target.** Let a real nonroot
target lie in an actual root arm whose Rule-1a table ties with another distinct real root arm.
If the target atom is graph-rigid, its actual four-ligand frame is constitutionally strict. The
input is simple-bonded with constant formal charge; rings are allowed.

The parent slot is separated by the accepted rootward bridge. Outward pairs are separated by
`outwardSiblings_separated_of_rigidTarget`. Real/real pairs go through the boundary readback and
the witnessed reconstruction automorphism, contradicting rigidity. Real/ring and ring/ring pairs
are excluded by their Rule-1b values. No comparator law, label, sort success or acyclicity is
assumed. -/
theorem frameConstitutionalStrict_of_rootArmRule1aTie_of_rigid
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (rootCursor : input.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : input.LocalizedCIPOccurrence (carrierFuel input))
    (targetReal : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (inside : input.RootBranchContains armCursor.occurrence target)
    (frame : input.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (nonroot : target.1.address ≠ [])
    {t : input.Atom} (ht : target.1.node.current? = some t)
    (rigid : ConstitutionallyRigidGraphAt input.moleculeGraph t) :
    FrameConstitutionalStrict frame :=
  frameConstitutionalStrict_of_rootArmRule1aTie input singleBonded rootCursor rootAddress
    armCursor armCursor' armMem armMem' armDistinct armReal armReal' armRead armRead' armKey
    armKey' armBuilt armBuilt' tie target targetReal inside frame computed nonroot
    (LocalizedActualBoundaryObservationReadback.outwardSiblings_separated_of_rigidTarget input
      singleBonded charge target targetReal ht rigid)

/-- **Physical form.** Rigidity is read from a physically calibrated general-rigid detected
center at the target atom. -/
theorem frameConstitutionalStrict_of_rootArmRule1aTie_of_physicalRigid
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (rootCursor : input.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : input.LocalizedCIPOccurrence (carrierFuel input))
    (targetReal : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (inside : input.RootBranchContains armCursor.occurrence target)
    (frame : input.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (nonroot : target.1.address ≠ [])
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (center : input.detectedMultiCenterMolecule.Center)
    (ht : target.1.node.current? = some center.1)
    (calibrated : ActualPhysicalGeneralRigidCalibratedCenter input
      input.detectedMultiCenterMolecule cfg center) :
    FrameConstitutionalStrict frame :=
  frameConstitutionalStrict_of_rootArmRule1aTie_of_rigid input singleBonded charge rootCursor
    rootAddress armCursor armCursor' armMem armMem' armDistinct armReal armReal' armRead
    armRead' armKey armKey' armBuilt armBuilt' tie target targetReal inside frame computed
    nonroot ht (constitutionallyRigidGraphAt_of_physicalGeneralRigid input cfg center calibrated)

end Endpoint

private theorem mem_of_getLast?_eq {α : Type*} : ∀ {l : List α} {a : α},
    l.getLast? = some a → a ∈ l
  | [], _, h => by simp at h
  | [_], a, h => by
      simp at h
      simp [h]
  | _ :: y :: rest, _, h => by
      rw [List.getLast?_cons_cons] at h
      exact List.mem_cons_of_mem _ (mem_of_getLast?_eq (l := y :: rest) h)

/-- A real carrier occurrence at a nonempty address does not sit on its outer root atom: its
history is duplicate-free, starts at the current atom and ends at the root. -/
theorem current_ne_root_of_nonroot (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (nonroot : occurrence.1.address ≠ [])
    {atom : input.Atom} (current : occurrence.1.node.current? = some atom) :
    atom ≠ occurrence.1.root := by
  obtain ⟨nodup, headEq⟩ :=
    LocalizedActualBoundaryObservationReadback.occurrence_history_facts input occurrence real
  have lastEq := input.frameCarrierOccurrence_history_getLast_eq_root occurrence
  have derived := (input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2
  have depthEq :=
    (OutwardRule1bObserverEquivalence.carrierOccurrence_ranked_depth input derived).2
  have addressPos : 0 < occurrence.1.address.length := List.length_pos_of_ne_nil nonroot
  unfold OfficialCIPNode.depth at depthEq
  rw [current] at headEq
  intro same
  cases hist : occurrence.1.node.history with
  | nil =>
      rw [hist] at depthEq
      simp at depthEq
      omega
  | cons first rest =>
      rw [hist] at headEq nodup lastEq depthEq
      have firstEq : atom = first := by simpa using headEq
      cases rest with
      | nil =>
          simp at depthEq
          omega
      | cons second rest' =>
          rw [List.getLast?_cons_cons] at lastEq
          have rootMem := mem_of_getLast?_eq lastEq
          have firstFresh := (List.nodup_cons.mp nodup).1
          rw [← same, firstEq] at rootMem
          exact firstFresh rootMem

/-- In the general-rigid physical domain, every nonroot center that is not a physical terminal
twin is calibrated and graph-rigid. -/
theorem physicalGeneralRigid_of_domain
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input input.detectedMultiCenterMolecule cfg root)
    (center : input.detectedMultiCenterMolecule.Center) (nonroot : center ≠ root)
    (notTwin : ¬ ActualPhysicalTerminalTwinCenter input input.detectedMultiCenterMolecule
      center) :
    ActualPhysicalGeneralRigidCalibratedCenter input input.detectedMultiCenterMolecule cfg
        center ∧
      ConstitutionallyRigidGraphAt input.moleculeGraph center.1 := by
  rcases domain.centerCase center nonroot with twin | calibrated
  · exact absurd twin notTwin
  · exact ⟨calibrated,
      constitutionallyRigidGraphAt_of_physicalGeneralRigid input cfg center calibrated⟩

end LocalizedCyclicGeneralRigidPriority
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.constitutionallySeparated_of_builds
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.ConstitutionallySeparated.symm
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.constitutionallyAbove_of_builds
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.constitutionallySeparated_of_rule1a_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.frameConstitutionalStrict_of_distinguished
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.constitutionallySeparated_of_armRule1aSeparated
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.frame_cursorAt_mem_executable
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.outwardSiblingPair_of_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.frame_cursorAt_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.parentSlot_separated_of_rootArmRule1aTie
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.frameConstitutionalStrict_of_rootArmRule1aTie
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.sameBoundaryResidualEquiv_false_of_rigid
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.isEmpty_sameBoundaryResidualEquiv_of_rigid
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.constitutionallyRigidGraphAt_of_physicalGeneralRigid
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.current_ne_root_of_nonroot
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.physicalGeneralRigid_of_domain
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.frameConstitutionalStrict_of_rootArmRule1aTie_of_rigid
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority.frameConstitutionalStrict_of_rootArmRule1aTie_of_physicalRigid
