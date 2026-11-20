import TetraStereo.OneCenter.LocalizedActualBoundaryPathReadingCorrespondence
import TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode
import TetraStereo.OneCenter.LocalizedActualCanonicalConstitutionalRefinement
import TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathReconstruction
import TetraStereo.OneCenter.LocalizedChemicalRingWitnessFactMatch
import TetraStereo.OneCenter.LocalizedChemicalRingActualComparisonLabelMatch
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-!
**What an actual root prior tie says about generated labels**, for an arbitrary raw state.

Equal Rule-1 through Rule-4c prior keys of two root slots leave Rule 5 free, so they do not give
equal labels. They give exactly one of two things: no uppercase label in the first arm, or one
Boolean `mirror` such that along every prescribed detected-terminal path, under an automorphism
realizing that path, uppercase labels correspond (reflected when `mirror` holds) and lowercase
labels are equal. The Boolean is the relation of the two selected Rule-4b references.

The quantifier is FOR EACH path THERE EXISTS an automorphism; `mirror` is common to all paths.
No rigid center, reader law, physical sign, successful label or desired comparison is assumed.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusPriorTie

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedCumulativeDecoratedTree LocalizedActualBoundaryPathRealization
open LocalizedActualOutwardRule1bEquivalence LocalizedActualBoundaryPathReadingCorrespondence
open LocalizedActualBoundaryObservationReadback LocalizedCyclicMatchedReadingDecode
open LocalizedChemicalRingActualComparisonLabelMatch
open LocalizedChemicalRingPrescribedPathReconstruction LocalizedChemicalRingColoredReconstruction
open LocalizedChemicalRingWitnessFactMatch LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedPromotedRanking (frames slot_valid)

noncomputable section
open scoped Classical

/-- Correspondence of two optional labels: uppercase reflected when `mirror` holds, lowercase
unchanged. Absent or non-matching first labels impose nothing. -/
def LabelCorr (mirror : Bool) (first second : Option LocalizedAuxiliaryLabel) : Prop :=
  (∀ d : RS, first = some (.chiral d) →
    second = some (.chiral (if mirror then RS.swap d else d))) ∧
  (∀ x, first = some (.pseudoasymmetric x) → second = some (.pseudoasymmetric x))

private theorem lowercase_corr (own other : RS) (first second : Option LocalizedAuxiliaryLabel)
    (same : localizedCumulativeRule45Priority (.rule4c own) first =
      localizedCumulativeRule45Priority (.rule4c other) second) (x)
    (lower : first = some (.pseudoasymmetric x)) : second = some (.pseudoasymmetric x) := by
  subst lower
  have expanded : [localizedRule4aPriority (some (.pseudoasymmetric x)),
      localizedRule4bPriority own (some (.pseudoasymmetric x)),
      localizedRule4cPriority (some (.pseudoasymmetric x))] =
    [localizedRule4aPriority second, localizedRule4bPriority other second,
      localizedRule4cPriority second] := same
  rcases second with _ | (d | y)
  · simp [localizedRule4aPriority] at expanded
  · simp [localizedRule4aPriority] at expanded
  · cases x <;> cases y <;> simp [localizedRule4cPriority] at expanded ⊢

private theorem first_two {x y z x' y' z' : Nat} (same : [x, y, z] = [x', y', z']) :
    [x, y] = [x', y'] := by
  simp only [List.cons.injEq, and_true] at same ⊢
  exact ⟨same.1, same.2.1⟩

private theorem opposite_corr (own : RS) (first second : Option LocalizedAuxiliaryLabel)
    (same : localizedCumulativeRule45Priority (.rule4c own) first =
      localizedCumulativeRule45Priority (.rule4c (RS.swap own)) second) :
    LabelCorr true first second := by
  refine ⟨?_, lowercase_corr own (RS.swap own) first second same⟩
  intro d upper
  subst upper
  have expanded : [localizedRule4aPriority (some (.chiral d)),
      localizedRule4bPriority own (some (.chiral d)),
      localizedRule4cPriority (some (.chiral d))] =
    [localizedRule4aPriority second, localizedRule4bPriority (RS.swap own) second,
      localizedRule4cPriority second] := same
  exact rule4bOpposite_priority_chiral own d second (first_two expanded)

private theorem same_corr (own : RS) (first second : Option LocalizedAuxiliaryLabel)
    (same : localizedCumulativeRule45Priority (.rule4c own) first =
      localizedCumulativeRule45Priority (.rule4c own) second) :
    LabelCorr false first second := by
  refine ⟨?_, lowercase_corr own own first second same⟩
  intro d upper
  subst upper
  have expanded : [localizedRule4aPriority (some (.chiral d)),
      localizedRule4bPriority own (some (.chiral d)),
      localizedRule4cPriority (some (.chiral d))] =
    [localizedRule4aPriority second, localizedRule4bPriority own second,
      localizedRule4cPriority second] := same
  exact rule4bSame_priority_chiral own d second (first_two expanded)

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = .realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)

private theorem frame_computed :
    input.localizedOccurrenceFourLigandFrame? target =
      some (frames input single state target real unit targetUnit).frame := by
  rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
  exact (frames input single state target real unit targetUnit).frameComputed

/-- At the empty address the actual frame slots are outward siblings. -/
private def slotPair (rootAddress : target.1.address = []) (i j : Fin 4) :
    ActualOutwardSiblingPair input (retainedCarrierFuel input) where
  target := { occurrence := target, previous? := none }
  left := (frames input single state target real unit targetUnit).frame.cursorAt i
  right := (frames input single state target real unit targetUnit).frame.cursorAt j
  leftPrevious := input.executableLocalizedRerootChildren_previous _ _
    ((frames input single state target real unit targetUnit).childAt i)
  rightPrevious := input.executableLocalizedRerootChildren_previous _ _
    ((frames input single state target real unit targetUnit).childAt j)
  leftRoot := input.localizedRerootChildren_root_eq _ _ _
    (input.executableLocalizedRerootChildren_declarative _)
    ((frames input single state target real unit targetUnit).childAt i)
  rightRoot := input.localizedRerootChildren_root_eq _ _ _
    (input.executableLocalizedRerootChildren_declarative _)
    ((frames input single state target real unit targetUnit).childAt j)
  leftSlot := Classical.choose
    (input.localizedOccurrenceFourLigandFrame_root_all_outward target _
      (frame_computed input single state target real unit targetUnit) rootAddress i).2
  rightSlot := Classical.choose
    (input.localizedOccurrenceFourLigandFrame_root_all_outward target _
      (frame_computed input single state target real unit targetUnit) rootAddress j).2
  leftAddress := Classical.choose_spec
    (input.localizedOccurrenceFourLigandFrame_root_all_outward target _
      (frame_computed input single state target real unit targetUnit) rootAddress i).2
  rightAddress := Classical.choose_spec
    (input.localizedOccurrenceFourLigandFrame_root_all_outward target _
      (frame_computed input single state target real unit targetUnit) rootAddress j).2

private theorem target_node (rootAddress : target.1.address = []) :
    target.1.node = OfficialCIPNode.root target.1.root := by
  have eq := input.declarativeLocalizedOccurrence_eq_root_of_address_nil
    ((input.mem_localizedOccurrences_iff _ _).mp target.2) rootAddress
  simpa using congrArg (fun occurrence => occurrence.node) eq

private theorem slot_real (rootAddress : target.1.address = []) (slot : Fin 4) :
    ((frames input single state target real unit targetUnit).frame.cursorAt
      slot).occurrence.1.node.provenance = .realAtom := by
  let pair := slotPair input single state target real unit targetUnit rootAddress slot slot
  have node := target_node input target rootAddress
  have current : target.1.node.current? = some target.1.root := by rw [node]; rfl
  have member := outwardChild_node_mem input pair.target pair.left pair.leftRoot pair.leftSlot
    pair.leftAddress
  obtain ⟨atom, nodeEq, adjacent, _⟩ :=
    (mem_executableOfficialCIPChildren_iff input single target.1.node current real _).mp member
  have fresh : atom ∉ target.1.node.history := by
    rw [node]
    change atom ∉ [target.1.root]
    rw [List.mem_singleton]
    intro same
    rw [same] at adjacent
    exact (Nat.lt_irrefl 0) (by simpa only [MoleculeGraph.Adj, input.moleculeGraph.bond_self] using adjacent)
  change pair.left.occurrence.1.node.provenance = .realAtom
  rw [nodeEq, OfficialCIPNode.extend_provenance, OfficialCIPNode.childProvenance_real _ _ fresh]

private abbrev theRead := input.molecularReader (rawStateDescriptorMap input state) target

private theorem arm_label {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (retainedCarrierFuel input) → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor (retainedCarrierFuel input)}
    (arm : input.RuleMajorContextArm (retainedCarrierFuel input) stage read cursor)
    (address : List ℕ) (node : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input))
    (lookup : arm.tree.decoratedSubtreeAt? address = some node) : node.label = read node.source := by
  have realized := realizes_of_decoratedSubtreeAt?
    arm.tree (LocalizedRuleMajorSortTrace.realizes_of_trace arm.trace) address node lookup
  rw [realized]
  rfl

/-- Two tied actual arms at root slots locate any prescribed path and its automorphic image at
one common ranked address, and the node labels there are the raw facts at those two histories. -/
theorem arms_path_labels (rootAddress : target.1.address = [])
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (left right : Fin 4) (a b : input.Atom)
    (currentL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.current? = some a)
    (currentR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.current? = some b)
    {stageL stageR : LocalizedCumulativeRule45Stage}
    (armL : input.RuleMajorContextArm (retainedCarrierFuel input) stageL (theRead input state target)
      ((frames input single state target real unit targetUnit).frame.cursorAt left))
    (armR : input.RuleMajorContextArm (retainedCarrierFuel input) stageR (theRead input state target)
      ((frames input single state target real unit targetUnit).frame.cursorAt right))
    (tie : OfficialRuleMajorKey.compare armL.key.constitutional armR.key.constitutional = .eq)
    (path : List input.Atom) (valid : ResidualObsPath input.moleculeGraph [target.1.root] a path)
    (detected : IsDetectedCenter input.moleculeGraph (pathTerminal path valid.nonempty)) :
    ∃ π : Equiv.Perm input.Atom, input.moleculeGraph.IsAutomorphism π ∧
      π target.1.root = target.1.root ∧ π a = b ∧
      ∃ (address : List ℕ) (nodeL nodeR : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input)),
        armL.tree.decoratedSubtreeAt? address = some nodeL ∧
        armR.tree.decoratedSubtreeAt? address = some nodeR ∧
        nodeL.label = (state.factAt? (rawPathNode target.1.root path)).map factLabel ∧
        nodeR.label = (state.factAt? (rawPathNode target.1.root (path.map π))).map factLabel := by
  let pair := slotPair input single state target real unit targetUnit rootAddress left right
  obtain ⟨a', b', ha, hb, e, corr⟩ := contextArms_equiv_with_same_address input single charge pair
    real (slot_real input single state target real unit targetUnit rootAddress left)
    (slot_real input single state target real unit targetUnit rootAddress right) armL armR tie
  obtain rfl : a' = a := Option.some.inj (ha.symm.trans currentL)
  obtain rfl : b' = b := Option.some.inj (hb.symm.trans currentR)
  have history : pair.target.occurrence.1.node.history.reverse = [target.1.root] := by
    change target.1.node.history.reverse = [target.1.root]
    rw [target_node input target rootAddress]
    rfl
  have valid' : ResidualObsPath input.moleculeGraph pair.target.occurrence.1.node.history.reverse a' path := by
    rw [history]
    exact valid
  have outside : a' ∉ pair.target.occurrence.1.node.history.reverse :=
    valid'.outside a' (List.mem_of_head?_eq_some valid'.head)
  obtain ⟨π, aut, fixed, entry, _, _, image⟩ := exists_forced_color_preserving_aut e outside
    (fun _ => ()) (fun _ => rfl) ⟨path, valid'⟩
  obtain ⟨address, leftAt, rightAt⟩ := corr ⟨path, valid'⟩
  rw [sourceAtAddress?_toOfficialSourceTree] at leftAt rightAt
  obtain ⟨nodeL, lookupL, sourceL⟩ := Option.map_eq_some_iff.mp leftAt
  obtain ⟨nodeR, lookupR, sourceR⟩ := Option.map_eq_some_iff.mp rightAt
  have sourceR' : nodeR.source.occurrence.1.node = boundaryNode [target.1.root] (path.map π) :=
    sourceR.trans ((congrArg (boundaryNode _) image).trans
      (congrArg (fun B => boundaryNode B (path.map π)) history))
  have sourceL' : nodeL.source.occurrence.1.node = boundaryNode [target.1.root] path :=
    sourceL.trans (congrArg (fun B => boundaryNode B path) history)
  have lastL : path.getLast? = some (pathTerminal path valid.nonempty) :=
    List.getLast?_eq_some_getLast valid.nonempty
  have lastR : (path.map π).getLast? = some (π (pathTerminal path valid.nonempty)) := by
    rw [List.getLast?_map, lastL]
    rfl
  let graphAut : input.moleculeGraph.Aut := ⟨π, aut⟩
  have detectedR : IsDetectedCenter input.moleculeGraph (π (pathTerminal path valid.nonempty)) :=
    (input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card _).mp
      ((input.moleculeGraph.isTetrahedralCenter_apply_aut_iff graphAut _).mpr
        ((input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card _).mpr detected))
  refine ⟨π, aut, fixed _ (by rw [history]; simp), entry, address, nodeL, nodeR, lookupL, lookupR, ?_, ?_⟩
  · rw [arm_label input armL address nodeL lookupL]
    exact (congrFun (rawStateReader_eq_molecularReader input state target) nodeL.source).symm.trans
      (reader_eq_path_fact single state target rootAddress _ path _ lastL detected sourceL')
  · rw [arm_label input armR address nodeR lookupR]
    exact (congrFun (rawStateReader_eq_molecularReader input state target) nodeR.source).symm.trans
      (reader_eq_path_fact single state target rootAddress _ (path.map π) _ lastR detectedR sourceR')

private theorem uniform_built (slot : Fin 4) :
    input.buildRuleMajorCompoundRule45KeyWith?
      (fun stage => input.buildRuleMajorCumulativeWithRead? stage (theRead input state target)
        (2 * (retainedCarrierFuel input + 1)))
      ((frames input single state target real unit targetUnit).frame.cursorAt slot) =
      some ((frames input single state target real unit targetUnit).compounds slot) := by
  have built := frame_uniform_built (rawStateDescriptorMap input state) target
    (frames input single state target real unit targetUnit) slot
  rwa [((frames input single state target real unit targetUnit).stages slot).a.sourceEq] at built

private theorem arm_exists (stage : LocalizedCumulativeRule45Stage) (slot : Fin 4) :
    Nonempty (input.RuleMajorContextArm (retainedCarrierFuel input) stage (theRead input state target)
      ((frames input single state target real unit targetUnit).frame.cursorAt slot)) :=
  input.exists_ruleMajorContextArm (retainedCarrierFuel input) stage (theRead input state target) _
    (slot_valid input single state target real unit targetUnit slot)

private theorem arms_tie {left right : Fin 4} {stageL stageR : LocalizedCumulativeRule45Stage}
    (armL : input.RuleMajorContextArm (retainedCarrierFuel input) stageL (theRead input state target)
      ((frames input single state target real unit targetUnit).frame.cursorAt left))
    (armR : input.RuleMajorContextArm (retainedCarrierFuel input) stageR (theRead input state target)
      ((frames input single state target real unit targetUnit).frame.cursorAt right))
    (rule4aTie : input.compareLocalizedRerootCumulativeRule45Keys
      ((frames input single state target real unit targetUnit).compounds left).prior.rule4aKey
      ((frames input single state target real unit targetUnit).compounds right).prior.rule4aKey = .eq) :
    OfficialRuleMajorKey.compare armL.key.constitutional armR.key.constitutional = .eq := by
  rw [RetainedConstitutionalReaderIndependence.ruleMajorBuild_constitutional_compare_congr
    stageL stageR .rule4a .rule4a (theRead input state target) (theRead input state target)
    (theRead input state target) (theRead input state target) _ _ armL.built armR.built
    (compound_components _ _ (uniform_built input single state target real unit targetUnit left)).1
    (compound_components _ _ (uniform_built input single state target real unit targetUnit right)).1]
  exact (officialRuleMajorKey_compare_eq_iff _ _).mpr
    (cumulativeRule45Tie_constitutional_columns input _ _ rule4aTie)

/-- A no-reference reading means the actual Rule-4a arm carries no uppercase label. -/
private theorem uppercase_free_of_none {slot : Fin 4}
    {reading : input.LocalizedRerootRule4bcReading}
    (member : reading ∈ ((frames input single state target real unit targetUnit).compounds slot).prior.readings)
    (noReference : reading.reference? = none)
    (arm : input.RuleMajorContextArm (retainedCarrierFuel input) .rule4a (theRead input state target)
      ((frames input single state target real unit targetUnit).frame.cursorAt slot)) :
    UppercaseFree arm.tree := by
  obtain ⟨builtA, readings, hr, ranked, _⟩ := compound_components _ _
    (uniform_built input single state target real unit targetUnit slot)
  have empty : localizedRule4bReferencesFromRankedLabels
      ((frames input single state target real unit targetUnit).compounds slot).prior.rule4aKey.rankedLabels = [] := by
    rw [ranked, mem_rankReadings] at member
    have referenceMem := rule4bcReadings_reference_mem _ _ _ readings hr reading member
    rw [noReference] at referenceMem
    generalize localizedRule4bReferencesFromRankedLabels
      ((frames input single state target real unit targetUnit).compounds slot).prior.rule4aKey.rankedLabels =
        references at referenceMem ⊢
    cases references with
    | nil => rfl
    | cons first rest => simp [localizedRule4bcReferenceAlternatives] at referenceMem
  have keyEq := arm_key_eq_of_built arm builtA
  have viewBuilt : input.buildLocalizedRerootCumulativeRule45Key? .rule4a target
      (input.molecularView (rawStateDescriptorMap input state) target)
      (2 * (retainedCarrierFuel input + 1))
      ((frames input single state target real unit targetUnit).frame.cursorAt slot) =
      some ((frames input single state target real unit targetUnit).compounds slot).prior.rule4aKey := by
    rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel,
      ← input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized]
    exact builtA
  have free := (input.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_iff_labels_chiralFree
    .rule4a target _ _ _ _ viewBuilt).mp empty
  have labelMatch : arm.tree.labelTable = arm.key.labels :=
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace arm.trace).labelMatch
  apply uppercaseFree_of_labelTable
  rw [labelMatch, keyEq]
  exact free

/-- One tied pair of Rule-4c arms with equal descriptor columns gives equal priorities at every
prescribed path and its image. -/
private theorem priorities_at_path (rootAddress : target.1.address = [])
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (left right : Fin 4) (a b : input.Atom)
    (currentL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.current? = some a)
    (currentR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.current? = some b)
    {stageL stageR : LocalizedCumulativeRule45Stage}
    (armL : input.RuleMajorContextArm (retainedCarrierFuel input) stageL (theRead input state target)
      ((frames input single state target real unit targetUnit).frame.cursorAt left))
    (armR : input.RuleMajorContextArm (retainedCarrierFuel input) stageR (theRead input state target)
      ((frames input single state target real unit targetUnit).frame.cursorAt right))
    (tie : OfficialRuleMajorKey.compare armL.key.constitutional armR.key.constitutional = .eq)
    (descriptors : armL.key.descriptor = armR.key.descriptor)
    (path : List input.Atom) (valid : ResidualObsPath input.moleculeGraph [target.1.root] a path)
    (detected : IsDetectedCenter input.moleculeGraph (pathTerminal path valid.nonempty)) :
    ∃ π : Equiv.Perm input.Atom, input.moleculeGraph.IsAutomorphism π ∧
      π target.1.root = target.1.root ∧ π a = b ∧
      localizedCumulativeRule45Priority stageL
          ((state.factAt? (rawPathNode target.1.root path)).map factLabel) =
        localizedCumulativeRule45Priority stageR
          ((state.factAt? (rawPathNode target.1.root (path.map π))).map factLabel) := by
  obtain ⟨π, aut, fixed, entry, address, nodeL, nodeR, lookupL, lookupR, labelL, labelR⟩ :=
    arms_path_labels input single state target real unit targetUnit rootAddress charge left right a b
      currentL currentR armL armR tie path valid detected
  have tables := (arm_descriptor_table armL).trans (descriptors.trans (arm_descriptor_table armR).symm)
  have column := column_eq_at_address
    (fun node => localizedCumulativeRule45Priority stageL node.label)
    (fun node => localizedCumulativeRule45Priority stageR node.label)
    address armL.tree armR.tree nodeL nodeR tables lookupL lookupR
  refine ⟨π, aut, fixed, entry, ?_⟩
  rw [← labelL, ← labelR]
  exact column

/-- **Decoding an actual root prior tie.** -/
theorem prior_tie_path_cases (rootAddress : target.1.address = [])
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (left right : Fin 4) (a b : input.Atom)
    (currentL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.current? = some a)
    (currentR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.current? = some b)
    (tie : (ofLex (rawStateKeys input single state target real unit targetUnit left)).1 =
      (ofLex (rawStateKeys input single state target real unit targetUnit right)).1) :
    (∀ (path : List input.Atom) (valid : ResidualObsPath input.moleculeGraph [target.1.root] a path),
      IsDetectedCenter input.moleculeGraph (pathTerminal path valid.nonempty) →
      ∀ d : RS, (state.factAt? (rawPathNode target.1.root path)).map factLabel ≠ some (.chiral d)) ∨
    ∃ mirror : Bool, ∀ (path : List input.Atom)
      (valid : ResidualObsPath input.moleculeGraph [target.1.root] a path),
      IsDetectedCenter input.moleculeGraph (pathTerminal path valid.nonempty) →
      ∃ π : Equiv.Perm input.Atom, input.moleculeGraph.IsAutomorphism π ∧
        π target.1.root = target.1.root ∧ π a = b ∧
        LabelCorr mirror ((state.factAt? (rawPathNode target.1.root path)).map factLabel)
          ((state.factAt? (rawPathNode target.1.root (path.map π))).map factLabel) := by
  have comparison := (frames input single state target real unit targetUnit).priorComparison
    (rawStateDescriptorMap_tetrahedral input state) single unit targetUnit left right
  have keysTie : compare
      (ofLex ((frames input single state target real unit targetUnit).retainedKeys unit left)).1
      (ofLex ((frames input single state target real unit targetUnit).retainedKeys unit right)).1 = .eq :=
    (completeLigandPriorKey_compare_eq_iff _ _).mpr tie
  obtain ⟨rule4aTie, -, readings4b, readings4c⟩ :=
    (input.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff _ _).mp (comparison.trans keysTie)
  obtain ⟨_, readingsL, hrL, rankedL, _⟩ := compound_components _ _
    (uniform_built input single state target real unit targetUnit left)
  obtain ⟨_, readingsR, hrR, rankedR, _⟩ := compound_components _ _
    (uniform_built input single state target real unit targetUnit right)
  obtain ⟨headL, tailL, eqL⟩ := List.exists_cons_of_ne_nil
    (compound_priorReadings_ne_nil _ _ (uniform_built input single state target real unit targetUnit left))
  obtain ⟨headR, tailR, eqR⟩ := List.exists_cons_of_ne_nil
    (compound_priorReadings_ne_nil _ _ (uniform_built input single state target real unit targetUnit right))
  have memberL : headL ∈ ((frames input single state target real unit targetUnit).compounds left).prior.readings := by
    rw [eqL]
    exact List.mem_cons_self
  have memberR : headR ∈ ((frames input single state target real unit targetUnit).compounds right).prior.readings := by
    rw [eqR]
    exact List.mem_cons_self
  have sourceL : headL ∈ readingsL := by
    have present := memberL
    rwa [rankedL, mem_rankReadings] at present
  have sourceR : headR ∈ readingsR := by
    have present := memberR
    rwa [rankedR, mem_rankReadings] at present
  rw [eqL, eqR] at readings4b readings4c
  simp only [compareLocalizedRerootCompoundRule4bReadings, List.compareLex_cons_cons,
    compareLocalizedRerootRule4bcReadingsByRule4b, Ordering.byKey, Ordering.then_eq_eq] at readings4b
  simp only [compareLocalizedRerootCompoundRule4cReadings, List.compareLex_cons_cons,
    Ordering.byKey, Ordering.then_eq_eq] at readings4c
  have head4b := (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mp readings4b.1
  have head4c := (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mp readings4c.1
  cases referenceL : headL.reference? with
  | none =>
      left
      intro path valid detected d same
      obtain ⟨armL⟩ := arm_exists input single state target real unit targetUnit .rule4a left
      obtain ⟨armR⟩ := arm_exists input single state target real unit targetUnit .rule4a right
      have free := uppercase_free_of_none input single state target real unit targetUnit memberL
        referenceL armL
      obtain ⟨_, _, _, _, address, nodeL, _, lookupL, _, labelL, _⟩ :=
        arms_path_labels input single state target real unit targetUnit rootAddress charge left right
          a b currentL currentR armL armR
          (arms_tie input single state target real unit targetUnit armL armR rule4aTie)
          path valid detected
      exact free address nodeL lookupL d (labelL.trans same)
  | some own =>
      right
      cases referenceR : headR.reference? with
      | none =>
          exfalso
          obtain ⟨armL⟩ := arm_exists input single state target real unit targetUnit (.rule4b own) left
          obtain ⟨armR⟩ := arm_exists input single state target real unit targetUnit .rule4a right
          have keyL := arm_key_eq_of_built armL
            (rule4bcReadings_built _ _ _ readingsL hrL headL sourceL own referenceL).1
          have keyR := arm_key_eq_of_built armR
            (rule4bcReadings_none_built _ _ _ readingsR hrR headR sourceR referenceR)
          exact rule4b_descriptor_ne_rule4a armL armR (by rw [keyL, keyR]; exact head4b)
      | some other =>
          obtain ⟨armL⟩ := arm_exists input single state target real unit targetUnit (.rule4c own) left
          obtain ⟨armR⟩ := arm_exists input single state target real unit targetUnit (.rule4c other) right
          have keyL := arm_key_eq_of_built armL
            (rule4bcReadings_built _ _ _ readingsL hrL headL sourceL own referenceL).2
          have keyR := arm_key_eq_of_built armR
            (rule4bcReadings_built _ _ _ readingsR hrR headR sourceR other referenceR).2
          have descriptors : armL.key.descriptor = armR.key.descriptor := by
            rw [keyL, keyR]
            exact head4c
          have matched := priorities_at_path input single state target real unit targetUnit rootAddress
            charge left right a b currentL currentR armL armR
            (arms_tie input single state target real unit targetUnit armL armR rule4aTie) descriptors
          by_cases same : other = own
          · subst same
            refine ⟨false, fun path valid detected => ?_⟩
            obtain ⟨π, aut, fixed, entry, priority⟩ := matched path valid detected
            exact ⟨π, aut, fixed, entry, same_corr other _ _ priority⟩
          · have opposite : other = RS.swap own := by
              cases own <;> cases other <;> first | exact absurd rfl same | rfl
            subst opposite
            refine ⟨true, fun path valid detected => ?_⟩
            obtain ⟨π, aut, fixed, entry, priority⟩ := matched path valid detected
            exact ⟨π, aut, fixed, entry, opposite_corr own _ _ priority⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusPriorTie

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusPriorTie.LabelCorr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusPriorTie.arms_path_labels
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusPriorTie.prior_tie_path_cases
