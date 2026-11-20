import TetraStereo.OneCenter.LocalizedRetainedDependencyLocality
import TetraStereo.OneCenter.LocalizedRootBranchAuxiliaryLocality
import TetraStereo.OneCenter.LocalizedOutwardWholeStateKeyAgreement
import TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000














































namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedStateReader

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput)

/-! ## Branch paths and the shared mosaic descriptor map -/

/-- The original-root atom path of a supplied occurrence: the unit path of its
`molecularFrameUnit`, i.e. the root-to-current atom path after the original root. -/
def branchPathOf {fuel : Nat} (branch : input.LocalizedCIPOccurrence fuel) : List input.Atom :=
  (input.molecularFrameUnit branch.1).path

/-- A descriptor map that reads `mapL` on consulted units whose unit path hextends `branchPath`,
and `mapR` on every other unit.  The test is the original-root path of the occurrence unit, so two
rings sharing atoms do not interfere: the unit is `⟨root, path⟩`, not the atom. -/
def branchMosaicMap (branchPath : List input.Atom)
    (mapL mapR : DescriptorMap (DetectedOccurrence input.moleculeGraph)) :
    DescriptorMap (DetectedOccurrence input.moleculeGraph) :=
  fun unit => if branchPath <+: unit.1.path then mapL unit else mapR unit

theorem branchPathOf_def {fuel : Nat} (branch : input.LocalizedCIPOccurrence fuel) :
    branchPathOf input branch = (input.molecularFrameUnit branch.1).path := rfl

/-! ## List algebra of branch prefixes -/

/-- Two distinct one-atom branches have no common extension.  This is the disjointness used for
the two outward arms; rings may share atoms, but a path cannot begin with two different atoms. -/
theorem singleton_prefix_not_of_ne {α : Type} {first second : α} (different : first ≠ second)
    (path : List α) (hprefix : [first] <+: path) : ¬ ([second] <+: path) := by
  obtain ⟨tail, rfl⟩ := hprefix
  intro secondPrefix
  obtain ⟨tail', equal⟩ := secondPrefix
  have head : first = second := by
    have heads := congrArg (fun values : List α => values.head?) equal
    simpa using heads.symm
  exact different head

/-- An atom-level sufficient form of the two-arm disjointness input: when both branch paths are
singletons of distinct atoms, no path hextends both.  This is the form in which `SimpleBonded`
tetrahedral geometry supplies the hypothesis (`canonicalLigandAtom_injective`). -/
theorem disjoint_of_singleton_branchPath_ne {firstAtom secondAtom : input.Atom}
    {branchPathL branchPathR : List input.Atom}
    (leftSingleton : branchPathL = [firstAtom])
    (rightSingleton : branchPathR = [secondAtom])
    (different : firstAtom ≠ secondAtom) :
    ∀ path : List input.Atom, branchPathL <+: path → ¬ (branchPathR <+: path) := by
  intro path leftPrefix
  rw [leftSingleton] at leftPrefix
  rw [rightSingleton]
  exact singleton_prefix_not_of_ne different path leftPrefix

/-! ## The branch path is the unit path of every extending unit -/

theorem branchPathOf_prefix_of_extends {fuel : Nat}
    {branch : input.LocalizedCIPOccurrence fuel} {unit : OccurrenceUnit input.Atom}
    (hextends : input.OccurrenceUnitExtendsRootBranch branch unit) :
    branchPathOf input branch <+: unit.path := by
  rw [branchPathOf_def]
  exact hextends.2

/-! ## Reading the shared map on and off the branch -/

theorem branchMosaicMap_of_prefix {branchPath : List input.Atom}
    {mapL mapR : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hprefix : branchPath <+: unit.1.path) :
    branchMosaicMap input branchPath mapL mapR unit = mapL unit := by
  unfold branchMosaicMap
  rw [if_pos hprefix]

theorem branchMosaicMap_of_not_prefix {branchPath : List input.Atom}
    {mapL mapR : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (noprefix : ¬ branchPath <+: unit.1.path) :
    branchMosaicMap input branchPath mapL mapR unit = mapR unit := by
  unfold branchMosaicMap
  rw [if_neg noprefix]

/-! ## Outward arms consult only units that extend their branch -/

section OutwardArm

variable {carrierFuel : Nat}

/-- Every occurrence unit consulted from an outward arm hextends that arm's own root branch.  The
address hprefix is `address_isPrefix_of_outward_reachable`, the history suffix is
`history_suffix_of_rootBranch`, and the unit form is `occurrenceUnit_extends_of_rootBranch`. -/
theorem unit_extends_of_outward_reachable
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {start cursor : input.LocalizedRerootCursor carrierFuel}
    (outward : OutwardRerootCursor input target start)
    (reachable : Relation.ReflTransGen (E input) start cursor) :
    input.OccurrenceUnitExtendsRootBranch start.occurrence
      (input.molecularFrameUnit cursor.occurrence.1) := by
  have reached := input.outward_reachable_cursor target start cursor outward reachable
  have prefixAddr :=
    input.address_isPrefix_of_outward_reachable target start cursor outward reachable
  have rootEq : start.occurrence.1.root = cursor.occurrence.1.root :=
    outward.2.1.1.trans reached.2.1.1.symm
  have suffix :=
    input.history_suffix_of_rootBranch start.occurrence cursor.occurrence rootEq prefixAddr
  exact input.occurrenceUnit_extends_of_rootBranch start.occurrence cursor.occurrence rootEq suffix

/-- On the left arm, the shared map agrees with the left map at every consulted unit. -/
theorem branchMosaicMap_eq_left_of_consult
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {start : input.LocalizedRerootCursor carrierFuel}
    (outward : OutwardRerootCursor input target start)
    (mapL mapR : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (consulted : input.ReachableArmDescriptorConsult target start unit) :
    branchMosaicMap input (branchPathOf input start.occurrence) mapL mapR unit = mapL unit := by
  obtain ⟨cursor, reachable, -, -, unitEq⟩ := consulted
  have hextends := unit_extends_of_outward_reachable input outward reachable
  rw [unitEq] at hextends
  exact branchMosaicMap_of_prefix input (branchPathOf_prefix_of_extends input hextends)

/-- On the right arm, the shared map agrees with the right map at every consulted unit, because
the two branch paths have no common extension. -/
theorem branchMosaicMap_eq_right_of_consult
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {startL startR : input.LocalizedRerootCursor carrierFuel}
    (outwardR : OutwardRerootCursor input target startR)
    (disjoint : ∀ path : List input.Atom,
      branchPathOf input startL.occurrence <+: path →
        ¬ (branchPathOf input startR.occurrence <+: path))
    (mapL mapR : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (consulted : input.ReachableArmDescriptorConsult target startR unit) :
    branchMosaicMap input (branchPathOf input startL.occurrence) mapL mapR unit = mapR unit := by
  obtain ⟨cursor, reachable, -, -, unitEq⟩ := consulted
  have hextends := unit_extends_of_outward_reachable input outwardR reachable
  rw [unitEq] at hextends
  have onRight := branchPathOf_prefix_of_extends input hextends
  exact branchMosaicMap_of_not_prefix input (fun onLeft => disjoint _ onLeft onRight)

/-! ## The actual reader of the shared map on each arm -/

theorem molecularReader_branchMosaicMap_eq_left
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {start : input.LocalizedRerootCursor carrierFuel}
    (outward : OutwardRerootCursor input target start)
    (mapL mapR : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor) :
    input.molecularReader
        (branchMosaicMap input (branchPathOf input start.occurrence) mapL mapR) target cursor =
      input.molecularReader mapL target cursor :=
  input.molecularReader_eq_of_reachableArmDescriptorConsult target start
    (branchMosaicMap input (branchPathOf input start.occurrence) mapL mapR) mapL
    (fun unit consulted =>
      branchMosaicMap_eq_left_of_consult input outward mapL mapR unit consulted)
    cursor reachable

theorem molecularReader_branchMosaicMap_eq_right
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {startL startR : input.LocalizedRerootCursor carrierFuel}
    (outwardR : OutwardRerootCursor input target startR)
    (disjoint : ∀ path : List input.Atom,
      branchPathOf input startL.occurrence <+: path →
        ¬ (branchPathOf input startR.occurrence <+: path))
    (mapL mapR : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) startR cursor) :
    input.molecularReader
        (branchMosaicMap input (branchPathOf input startL.occurrence) mapL mapR) target cursor =
      input.molecularReader mapR target cursor :=
  input.molecularReader_eq_of_reachableArmDescriptorConsult target startR
    (branchMosaicMap input (branchPathOf input startL.occurrence) mapL mapR) mapR
    (fun unit consulted =>
      branchMosaicMap_eq_right_of_consult input outwardR disjoint mapL mapR unit consulted)
    cursor reachable

/-! ## The same readback for two supplied raw states -/

theorem rawStateReader_branchMosaicMap_eq_left
    (stateL stateR : OccurrenceAuxState)
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {start : input.LocalizedRerootCursor carrierFuel}
    (outward : OutwardRerootCursor input target start)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor) :
    input.molecularReader
        (branchMosaicMap input (branchPathOf input start.occurrence)
          (rawStateDescriptorMap input stateL) (rawStateDescriptorMap input stateR))
        target cursor =
      rawStateReader input stateL target cursor :=
  (molecularReader_branchMosaicMap_eq_left input outward
      (rawStateDescriptorMap input stateL) (rawStateDescriptorMap input stateR) cursor
      reachable).trans
    (congrFun (rawStateReader_eq_molecularReader input stateL target).symm cursor)

theorem rawStateReader_branchMosaicMap_eq_right
    (stateL stateR : OccurrenceAuxState)
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {startL startR : input.LocalizedRerootCursor carrierFuel}
    (outwardR : OutwardRerootCursor input target startR)
    (disjoint : ∀ path : List input.Atom,
      branchPathOf input startL.occurrence <+: path →
        ¬ (branchPathOf input startR.occurrence <+: path))
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) startR cursor) :
    input.molecularReader
        (branchMosaicMap input (branchPathOf input startL.occurrence)
          (rawStateDescriptorMap input stateL) (rawStateDescriptorMap input stateR))
        target cursor =
      rawStateReader input stateR target cursor :=
  (molecularReader_branchMosaicMap_eq_right input outwardR disjoint
      (rawStateDescriptorMap input stateL) (rawStateDescriptorMap input stateR) cursor
      reachable).trans
    (congrFun (rawStateReader_eq_molecularReader input stateR target).symm cursor)

/-- At a real detected dependency of the left arm, the shared reader reads the left state's raw
fact label at the very same occurrence unit. -/
theorem branchMosaicReader_eq_rawStateLabel_left
    (stateL stateR : OccurrenceAuxState)
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {start : input.LocalizedRerootCursor carrierFuel}
    (outward : OutwardRerootCursor input target start)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor)
    (dependency : input.LocalizedDepthDependency cursor.occurrence target)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (detected : IsDetectedCenter input.moleculeGraph
      (input.molecularFrameUnit cursor.occurrence.1).atom) :
    input.molecularReader
        (branchMosaicMap input (branchPathOf input start.occurrence)
          (rawStateDescriptorMap input stateL) (rawStateDescriptorMap input stateR))
        target cursor =
      rawStateLabel? stateL (input.molecularFrameUnit cursor.occurrence.1) :=
  (rawStateReader_branchMosaicMap_eq_left input stateL stateR outward cursor reachable).trans
    (rawStateReader_of_real input stateL target cursor dependency real detected)

/-- At a real detected dependency of the right arm, the shared reader reads the right state's raw
fact label at the very same occurrence unit. -/
theorem branchMosaicReader_eq_rawStateLabel_right
    (stateL stateR : OccurrenceAuxState)
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {startL startR : input.LocalizedRerootCursor carrierFuel}
    (outwardR : OutwardRerootCursor input target startR)
    (disjoint : ∀ path : List input.Atom,
      branchPathOf input startL.occurrence <+: path →
        ¬ (branchPathOf input startR.occurrence <+: path))
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) startR cursor)
    (dependency : input.LocalizedDepthDependency cursor.occurrence target)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (detected : IsDetectedCenter input.moleculeGraph
      (input.molecularFrameUnit cursor.occurrence.1).atom) :
    input.molecularReader
        (branchMosaicMap input (branchPathOf input startL.occurrence)
          (rawStateDescriptorMap input stateL) (rawStateDescriptorMap input stateR))
        target cursor =
      rawStateLabel? stateR (input.molecularFrameUnit cursor.occurrence.1) :=
  (rawStateReader_branchMosaicMap_eq_right input stateL stateR outwardR disjoint cursor
      reachable).trans
    (rawStateReader_of_real input stateR target cursor dependency real detected)

/-- A cross-state reader tie at the two arm entries transfers to the single shared reader. -/
theorem molecularReader_tie_transfer
    (stateL stateR : OccurrenceAuxState)
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {startL startR : input.LocalizedRerootCursor carrierFuel}
    (outwardL : OutwardRerootCursor input target startL)
    (outwardR : OutwardRerootCursor input target startR)
    (disjoint : ∀ path : List input.Atom,
      branchPathOf input startL.occurrence <+: path →
        ¬ (branchPathOf input startR.occurrence <+: path))
    {left right : input.LocalizedRerootCursor carrierFuel}
    (reachableL : Relation.ReflTransGen (E input) startL left)
    (reachableR : Relation.ReflTransGen (E input) startR right)
    (tie :
      input.molecularReader (rawStateDescriptorMap input stateL) target left =
        input.molecularReader (rawStateDescriptorMap input stateR) target right) :
    input.molecularReader
        (branchMosaicMap input (branchPathOf input startL.occurrence)
          (rawStateDescriptorMap input stateL) (rawStateDescriptorMap input stateR))
        target left =
      input.molecularReader
        (branchMosaicMap input (branchPathOf input startL.occurrence)
          (rawStateDescriptorMap input stateL) (rawStateDescriptorMap input stateR))
        target right := by
  have leftEq :=
    molecularReader_branchMosaicMap_eq_left input outwardL
      (rawStateDescriptorMap input stateL) (rawStateDescriptorMap input stateR) left reachableL
  have rightEq :=
    molecularReader_branchMosaicMap_eq_right input outwardR disjoint
      (rawStateDescriptorMap input stateL) (rawStateDescriptorMap input stateR) right reachableR
  exact leftEq.trans (tie.trans rightEq.symm)

/-! ## Whole cumulative Rule-4/5 builds -/

theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_branchMosaicMap_eq_left
    (stage : LocalizedCumulativeRule45Stage)
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {start : input.LocalizedRerootCursor carrierFuel}
    (outward : OutwardRerootCursor input target start)
    (mapL mapR : DescriptorMap (DetectedOccurrence input.moleculeGraph)) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) start cursor →
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
        (input.molecularReader
          (branchMosaicMap input (branchPathOf input start.occurrence) mapL mapR) target)
        fuel cursor =
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
        (input.molecularReader mapL target) fuel cursor :=
  input.buildLocalizedRerootCumulativeRule45KeyWithRead?_congr_of_reachable stage
    (input.molecularReader
      (branchMosaicMap input (branchPathOf input start.occurrence) mapL mapR) target)
    (input.molecularReader mapL target) start
    (fun cursor reachable =>
      molecularReader_branchMosaicMap_eq_left input outward mapL mapR cursor reachable)

theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_branchMosaicMap_eq_right
    (stage : LocalizedCumulativeRule45Stage)
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {startL startR : input.LocalizedRerootCursor carrierFuel}
    (outwardR : OutwardRerootCursor input target startR)
    (disjoint : ∀ path : List input.Atom,
      branchPathOf input startL.occurrence <+: path →
        ¬ (branchPathOf input startR.occurrence <+: path))
    (mapL mapR : DescriptorMap (DetectedOccurrence input.moleculeGraph)) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) startR cursor →
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
        (input.molecularReader
          (branchMosaicMap input (branchPathOf input startL.occurrence) mapL mapR) target)
        fuel cursor =
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
        (input.molecularReader mapR target) fuel cursor :=
  input.buildLocalizedRerootCumulativeRule45KeyWithRead?_congr_of_reachable stage
    (input.molecularReader
      (branchMosaicMap input (branchPathOf input startL.occurrence) mapL mapR) target)
    (input.molecularReader mapR target) startR
    (fun cursor reachable =>
      molecularReader_branchMosaicMap_eq_right input outwardR disjoint mapL mapR cursor reachable)

/-- A cross-state cumulative Rule-4/5 build tie transfers to the single shared reader: the left
build and the right build are both the shared build, so they are equal there. -/
theorem cumulative_build_tie_transfer
    (stateL stateR : OccurrenceAuxState)
    (stage : LocalizedCumulativeRule45Stage)
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {startL startR : input.LocalizedRerootCursor carrierFuel}
    (outwardL : OutwardRerootCursor input target startL)
    (outwardR : OutwardRerootCursor input target startR)
    (disjoint : ∀ path : List input.Atom,
      branchPathOf input startL.occurrence <+: path →
        ¬ (branchPathOf input startR.occurrence <+: path))
    {left right : input.LocalizedRerootCursor carrierFuel}
    (fuel : Nat)
    (reachableL : Relation.ReflTransGen (E input) startL left)
    (reachableR : Relation.ReflTransGen (E input) startR right)
    (tie :
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
          (input.molecularReader (rawStateDescriptorMap input stateL) target) fuel left =
        input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
          (input.molecularReader (rawStateDescriptorMap input stateR) target) fuel right) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
        (input.molecularReader
          (branchMosaicMap input (branchPathOf input startL.occurrence)
            (rawStateDescriptorMap input stateL) (rawStateDescriptorMap input stateR)) target)
        fuel left =
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
        (input.molecularReader
          (branchMosaicMap input (branchPathOf input startL.occurrence)
            (rawStateDescriptorMap input stateL) (rawStateDescriptorMap input stateR)) target)
        fuel right := by
  have leftEq :=
    buildLocalizedRerootCumulativeRule45KeyWithRead?_branchMosaicMap_eq_left input stage
      outwardL (rawStateDescriptorMap input stateL) (rawStateDescriptorMap input stateR)
      fuel left reachableL
  have rightEq :=
    buildLocalizedRerootCumulativeRule45KeyWithRead?_branchMosaicMap_eq_right input stage
      outwardR disjoint (rawStateDescriptorMap input stateL) (rawStateDescriptorMap input stateR)
      fuel right reachableR
  exact leftEq.trans (tie.trans rightEq.symm)

end OutwardArm

end

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.singleton_prefix_not_of_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.disjoint_of_singleton_branchPath_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.branchPathOf_def
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.branchPathOf_prefix_of_extends
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.branchMosaicMap_of_prefix
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.branchMosaicMap_of_not_prefix
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.unit_extends_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.branchMosaicMap_eq_left_of_consult
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.branchMosaicMap_eq_right_of_consult
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.molecularReader_branchMosaicMap_eq_left
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.molecularReader_branchMosaicMap_eq_right
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.rawStateReader_branchMosaicMap_eq_left
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.rawStateReader_branchMosaicMap_eq_right
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.branchMosaicReader_eq_rawStateLabel_left
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.branchMosaicReader_eq_rawStateLabel_right
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.molecularReader_tie_transfer
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.buildLocalizedRerootCumulativeRule45KeyWithRead?_branchMosaicMap_eq_left
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.buildLocalizedRerootCumulativeRule45KeyWithRead?_branchMosaicMap_eq_right
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness.cumulative_build_tie_transfer
