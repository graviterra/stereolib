import TetraStereo.OneCenter.LocalizedActualSiblingPhysicalKind
import TetraStereo.OneCenter.LocalizedChiralStageExtension
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false













































namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

variable {input : LocalizedUniversalReference.Input}

/-! ## Definitions -/







def ActualSlotPhysicalSetup.NoPhysicalMarkedBranch (setup : ActualSlotPhysicalSetup input) : Prop :=
  ∀ y : input.certified.Atom,
    y ∈ ActualSlotCut input setup.root.1 setup.oAtom → ¬ PhysicalMarkedAtom input setup.root y

/-! ## The actual reader and the actual production builder -/

/-- **The actual generated reader is the production restricted dependency label.**  Both sides are
the same definition: the reader of `ActualReaderPhysicalBranchInverse.dependencyReader` reads the
production target `topTarget input setup.c` through the production view
`referenceDependencyView input setup.c`.  This is a definitional identity, so no read agreement is
assumed anywhere below. -/
theorem dependencyReader_eq_productionReader (setup : ActualSlotPhysicalSetup input) :
    ActualReaderPhysicalBranchInverse.dependencyReader input setup.c =
      fun cursor =>
        input.certified.localizedDependencyLabel
          (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
          (referenceDependencyView input setup.c) cursor :=
  rfl

/-- **The `WithRead?` builder driven by the actual reader is the actual production builder.**  The
equality is a full `Option` equality at every stage, fuel and cursor: a fail-closed `none` is
preserved and a successful compilation is the same key. -/
theorem buildWithRead_dependencyReader_eq_build (setup : ActualSlotPhysicalSetup input)
    (stage : LocalizedCumulativeRule45Stage) (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input)) :
    input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
        (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) fuel cursor =
      input.certified.buildLocalizedRerootCumulativeRule45Key? stage
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
        (referenceDependencyView input setup.c) fuel cursor := by
  rw [dependencyReader_eq_productionReader setup]
  exact input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
    stage (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
    (referenceDependencyView input setup.c) fuel cursor




theorem actualChildReachable_iff_reflTransGen
    {certified : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {start target : certified.LocalizedRerootCursor carrierFuel} :
    certified.ActualChildReachable start target ↔
      Relation.ReflTransGen (E certified) start target :=
  Iff.rfl








theorem physicalReader_noPseudo (setup : ActualSlotPhysicalSetup input) :
    ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      Relation.ReflTransGen (E input.certified) setup.tree.source cursor →
        LocalizedNoPseudoLabel
          (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c cursor) := by
  intro cursor reachable
  rcases reachable_cursor_reader_none_or_chiral setup reachable with noneEq | ⟨rs, chiralEq⟩
  · rw [noneEq]
    simp [LocalizedNoPseudoLabel]
  · rw [chiralEq]
    simp [LocalizedNoPseudoLabel]

/-! ## Rule-4c and Rule-5 stage extension of the actual production builder -/

/-- **Actual Rule-4c extension.**  At every cursor actually reachable from the physical slot cursor
and every fuel, the actual production Rule-4c build is the exact key extension of the actual
production Rule-4b build at the same reference.  The equality is a full `Option` equality, so it
holds whether or not either build succeeds. -/
theorem physical_rule4c_extension (setup : ActualSlotPhysicalSetup input) (reference : RS)
    (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (reachable : input.certified.ActualChildReachable setup.tree.source cursor) :
    input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule4c reference)
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
        (referenceDependencyView input setup.c) fuel cursor =
      Option.map
        (input.certified.extendLocalizedRerootCumulativeRule45Key
          extendLocalizedRule4bPriorityToRule4c)
        (input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule4b reference)
          (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
          (referenceDependencyView input setup.c) fuel cursor) := by
  rw [← buildWithRead_dependencyReader_eq_build setup (.rule4c reference) fuel cursor,
    ← buildWithRead_dependencyReader_eq_build setup (.rule4b reference) fuel cursor]
  exact buildLocalizedRerootCumulativeRule45KeyWithRead?_rule4c_extension input.certified reference
    (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) setup.tree.source
    (physicalReader_noPseudo setup) fuel cursor reachable

/-- **Actual Rule-5 extension.**  The actual production Rule-5 build is the exact key extension of
the actual production Rule-4b build.  The Rule-4b and Rule-5 references are independent: no
relation between them is assumed. -/
theorem physical_rule5_extension (setup : ActualSlotPhysicalSetup input)
    (rule4bReference rule5Reference : RS) (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (reachable : input.certified.ActualChildReachable setup.tree.source cursor) :
    input.certified.buildLocalizedRerootCumulativeRule45Key?
        (.rule5 rule4bReference rule5Reference)
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
        (referenceDependencyView input setup.c) fuel cursor =
      Option.map
        (input.certified.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference))
        (input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule4b rule4bReference)
          (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
          (referenceDependencyView input setup.c) fuel cursor) := by
  rw [← buildWithRead_dependencyReader_eq_build setup
      (.rule5 rule4bReference rule5Reference) fuel cursor,
    ← buildWithRead_dependencyReader_eq_build setup (.rule4b rule4bReference) fuel cursor]
  exact buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5_extension input.certified
    rule4bReference rule5Reference
    (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) setup.tree.source
    (physicalReader_noPseudo setup) fuel cursor reachable

/-- **Actual all-depth descriptor projection.**  Taking the first two components of every addressed
descriptor entry of the actual Rule-5 build recovers the actual Rule-4b descriptor exactly, at every
depth and whether or not the builds succeed.  This is the projection a `rule5_descriptor` consumer
needs; the addresses are untouched. -/
theorem physical_rule5_descriptor_projection (setup : ActualSlotPhysicalSetup input)
    (rule4bReference rule5Reference : RS) (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (reachable : input.certified.ActualChildReachable setup.tree.source cursor) :
    Option.map
        (fun built : input.certified.LocalizedRerootCumulativeRule45Key =>
          built.descriptor.map
            (List.map fun entry : OfficialSparseEntry (List Nat) =>
              (entry.1, entry.2.take 2)))
        (input.certified.buildLocalizedRerootCumulativeRule45Key?
          (.rule5 rule4bReference rule5Reference)
          (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
          (referenceDependencyView input setup.c) fuel cursor) =
      Option.map (fun built : input.certified.LocalizedRerootCumulativeRule45Key =>
          built.descriptor)
        (input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule4b rule4bReference)
          (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
          (referenceDependencyView input setup.c) fuel cursor) := by
  rw [← buildWithRead_dependencyReader_eq_build setup
      (.rule5 rule4bReference rule5Reference) fuel cursor,
    ← buildWithRead_dependencyReader_eq_build setup (.rule4b rule4bReference) fuel cursor]
  exact buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5_descriptor_projection
    input.certified rule4bReference rule5Reference
    (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) setup.tree.source
    (physicalReader_noPseudo setup) fuel cursor reachable

/-- **Actual Rule-4c success.**  A successful actual production Rule-4b build at a reachable cursor
yields the successful actual production Rule-4c build of the exact extended key, at the same cursor
and the same fuel.  The witness key is the actual builder output; no key is selected. -/
theorem physical_rule4c_success (setup : ActualSlotPhysicalSetup input) (reference : RS)
    (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (reachable : input.certified.ActualChildReachable setup.tree.source cursor)
    (key : input.certified.LocalizedRerootCumulativeRule45Key)
    (computed : input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule4b reference)
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c) fuel cursor = some key) :
    input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule4c reference)
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
        (referenceDependencyView input setup.c) fuel cursor =
      some
        (input.certified.extendLocalizedRerootCumulativeRule45Key
          extendLocalizedRule4bPriorityToRule4c key) := by
  rw [physical_rule4c_extension setup reference fuel cursor reachable, computed]
  rfl

/-- **Actual Rule-5 success.**  A successful actual production Rule-4b build yields the successful
actual production Rule-5 build of the exact extended key, at the same cursor and fuel. -/
theorem physical_rule5_success (setup : ActualSlotPhysicalSetup input)
    (rule4bReference rule5Reference : RS) (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (reachable : input.certified.ActualChildReachable setup.tree.source cursor)
    (key : input.certified.LocalizedRerootCumulativeRule45Key)
    (computed : input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule4b rule4bReference)
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c) fuel cursor = some key) :
    input.certified.buildLocalizedRerootCumulativeRule45Key?
        (.rule5 rule4bReference rule5Reference)
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
        (referenceDependencyView input setup.c) fuel cursor =
      some
        (input.certified.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference) key) := by
  rw [physical_rule5_extension setup rule4bReference rule5Reference fuel cursor reachable, computed]
  rfl

/-! ## Descriptor images of actual builds -/




theorem physical_descriptorImage_of_admitted (setup : ActualSlotPhysicalSetup input)
    (stage : LocalizedCumulativeRule45Stage)
    (admitted : Option LocalizedAuxiliaryLabel → Prop)
    (admittedReads : ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      Relation.ReflTransGen (E input.certified) setup.tree.source cursor →
        admitted (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c cursor))
    (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (reachable : input.certified.ActualChildReachable setup.tree.source cursor)
    (key : input.certified.LocalizedRerootCumulativeRule45Key)
    (computed : input.certified.buildLocalizedRerootCumulativeRule45Key? stage
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c) fuel cursor = some key) :
    LocalizedStageDescriptorImage stage admitted key.descriptor := by
  have sameBuild := buildWithRead_dependencyReader_eq_build setup stage fuel cursor
  rw [← sameBuild] at computed
  exact buildLocalizedRerootCumulativeRule45KeyWithRead?_descriptorImage input.certified stage
    admitted (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) setup.tree.source
    admittedReads fuel cursor reachable key computed



theorem physical_descriptorImage (setup : ActualSlotPhysicalSetup input)
    (stage : LocalizedCumulativeRule45Stage) (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (reachable : input.certified.ActualChildReachable setup.tree.source cursor)
    (key : input.certified.LocalizedRerootCumulativeRule45Key)
    (computed : input.certified.buildLocalizedRerootCumulativeRule45Key? stage
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c) fuel cursor = some key) :
    LocalizedStageDescriptorImage stage LocalizedNoPseudoLabel key.descriptor :=
  physical_descriptorImage_of_admitted setup stage LocalizedNoPseudoLabel
    (physicalReader_noPseudo setup) fuel cursor reachable key computed

/-- **All-depth `take 2` recovery of the Rule-4c descriptor.**  For every depth, projecting the first
two components of each addressed entry of the extended Rule-4c descriptor recovers exactly the
Rule-4b descriptor sphere.  The hypothesis is the derived descriptor image; the addresses are
untouched. -/
theorem physical_rule4c_descriptor_take_two (setup : ActualSlotPhysicalSetup input)
    {reference : RS} {key : input.certified.LocalizedRerootCumulativeRule45Key}
    (image : LocalizedStageDescriptorImage (.rule4b reference) LocalizedNoPseudoLabel
      key.descriptor)
    (depth : Nat) :
    (((input.certified.extendLocalizedRerootCumulativeRule45Key
        extendLocalizedRule4bPriorityToRule4c key).descriptor.getD depth []).map
      (fun entry : OfficialSparseEntry (List Nat) => (entry.1, entry.2.take 2))) =
      key.descriptor.getD depth [] := by
  rw [extendLocalizedRerootCumulativeRule45Key_descriptor,
    extendLocalizedPriorityLayers_getD, List.map_map]
  have step : (key.descriptor.getD depth []).map
      ((fun entry : OfficialSparseEntry (List Nat) => (entry.1, entry.2.take 2)) ∘
        extendLocalizedPriorityEntry extendLocalizedRule4bPriorityToRule4c) =
      (key.descriptor.getD depth []).map id := by
    apply List.map_congr_left
    intro entry entryMem
    simp only [Function.comp_apply, extendLocalizedPriorityEntry_fst,
      extendLocalizedPriorityEntry_snd]
    rw [extendLocalizedRule4bPriorityToRule4c_take_two reference
      (image.getD depth entry entryMem)]
    rfl
  rw [step, List.map_id]

/-- **All-depth `take 2` recovery of the Rule-5 descriptor.** -/
theorem physical_rule5_descriptor_take_two (setup : ActualSlotPhysicalSetup input)
    {rule4bReference rule5Reference : RS}
    {key : input.certified.LocalizedRerootCumulativeRule45Key}
    (image : LocalizedStageDescriptorImage (.rule4b rule4bReference) LocalizedNoPseudoLabel
      key.descriptor)
    (depth : Nat) :
    (((input.certified.extendLocalizedRerootCumulativeRule45Key
        (extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference)
        key).descriptor.getD depth []).map
      (fun entry : OfficialSparseEntry (List Nat) => (entry.1, entry.2.take 2))) =
      key.descriptor.getD depth [] := by
  rw [extendLocalizedRerootCumulativeRule45Key_descriptor,
    extendLocalizedPriorityLayers_getD, List.map_map]
  have step : (key.descriptor.getD depth []).map
      ((fun entry : OfficialSparseEntry (List Nat) => (entry.1, entry.2.take 2)) ∘
        extendLocalizedPriorityEntry
          (extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference)) =
      (key.descriptor.getD depth []).map id := by
    apply List.map_congr_left
    intro entry entryMem
    simp only [Function.comp_apply, extendLocalizedPriorityEntry_fst,
      extendLocalizedPriorityEntry_snd]
    rw [extendLocalizedRule4bPriorityToRule5_take_two rule4bReference rule5Reference
      (image.getD depth entry entryMem)]
    rfl
  rw [step, List.map_id]









/-- **The pure physical branch domain is the empty alternative or a unique nearest centre.**  This
records that `NoPhysicalMarkedBranch` is precisely the reader-independent empty (zero eligible
physical centres) alternative of `PhysicalBranchDomain`; the second alternative is unchanged. -/
theorem physicalBranchDomain_iff_empty_or_unique (setup : ActualSlotPhysicalSetup input) :
    PhysicalBranchDomain input setup.root setup.oAtom ↔
      setup.NoPhysicalMarkedBranch ∨
        ∃ (center : input.certified.Atom) (distance : Nat),
          PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance :=
  Iff.rfl





theorem noPhysicalMarkedBranch_iff_branchMarkedDescriptor_eq_none
    (setup : ActualSlotPhysicalSetup input) :
    setup.NoPhysicalMarkedBranch ↔
      ∀ (y : input.certified.Atom),
        y ∈ ActualSlotCut input setup.root.1 setup.oAtom →
          branchMarkedDescriptor input setup.c setup.frame setup.frameComputed setup.slot
            setup.singleBonded setup.acyclic setup.oAtom setup.oObserved y = none := by
  constructor
  · intro empty y yMem
    cases marked : branchMarkedDescriptor input setup.c setup.frame setup.frameComputed setup.slot
        setup.singleBonded setup.acyclic setup.oAtom setup.oObserved y with
    | none => rfl
    | some descriptor =>
        exact absurd
          (physicalMarkedAtom_of_branchMarkedDescriptor_eq_some input setup.c setup.frame
            setup.frameComputed setup.slot setup.singleBonded setup.acyclic setup.hcharge
            setup.noDouble (input.certified.canonicalReindexConfiguration setup.cfg)
            setup.globalDomain setup.oAtom setup.oObserved yMem marked)
          (empty y yMem)
  · intro zero y yMem marked
    obtain ⟨descriptor, markedEq⟩ :=
      exists_branchMarkedDescriptor_eq_some_of_physicalMarked input setup.c setup.frame
        setup.frameComputed setup.slot setup.singleBonded setup.acyclic setup.hcharge
        setup.noDouble (input.certified.canonicalReindexConfiguration setup.cfg)
        setup.globalDomain setup.oAtom setup.oObserved yMem marked
    rw [zero y yMem] at markedEq
    cases markedEq

/-- **The physical empty branch forces the actual reader to be absent at every reachable cursor.**
At each cursor actually reachable from the slot cursor the occurrence is a strict-depth dependency of
the final target, so its current atom lies in the physical cut branch by the general actual cut
correspondence, and the general rigid / terminal-twin classification leaves only three cases: a
noncandidate and a physical terminal twin already read `none`, while a positive general-rigid
occurrence would make the current atom a physically marked branch atom, contradicting emptiness.
No reader value, `noReads` hypothesis, selected list or build success is assumed. -/
theorem physical_noReads (setup : ActualSlotPhysicalSetup input)
    (empty : setup.NoPhysicalMarkedBranch) :
    ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      Relation.ReflTransGen (E input.certified) setup.tree.source cursor →
        ActualReaderPhysicalBranchInverse.dependencyReader input setup.c cursor = none := by
  intro cursor reachable
  rw [reachable_cursor_reader_eq_state setup reachable]
  rcases actualStrictDependency_classification_generalRigid input setup.singleBonded
      setup.acyclic setup.hcharge setup.noDouble
      (input.certified.canonicalReindexConfiguration setup.cfg)
      ⟨setup.c.1, setup.c.2⟩ setup.globalDomain ⟨setup.c.1, setup.c.2⟩ rfl cursor
      (reachable_cursor_dependency setup reachable).1 with
    ⟨_, noneEq⟩ | ⟨_, noneEq⟩ | ⟨center, positive⟩
  · exact noneEq
  · exact noneEq
  · obtain ⟨_rs, _tracked, _frame, _alpha, _pointAt, currentEq, notTwin, _rest⟩ := positive
    exfalso
    have branchMem : center.1 ∈ ActualSlotCut input setup.root.1 setup.oAtom :=
      input.certified.actualReachable_current_mem_cutBranch_general setup.singleBonded
        setup.acyclic (globalCarrierFuel_adequate input) setup.tree.source
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c) setup.tree_previousEq
        setup.tree_valid setup.tree_oObserved
        (ActualReaderPhysicalBranchInverse.topTarget_current input setup.c) setup.incomingEdge
        cursor reachable currentEq
    have notRoot : center.1 ≠ setup.root.1 :=
      AcyclicCutBranchAutomorphism.cutBranch_ne_center input.certified.moleculeGraph branchMem
    exact empty center.1 branchMem ⟨notRoot, ⟨center.2, notTwin⟩⟩

/-- **The physical empty branch kills the actual reader (actual reachability form).** -/
theorem physical_reader_none_of_empty (setup : ActualSlotPhysicalSetup input)
    (empty : setup.NoPhysicalMarkedBranch) :
    ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      input.certified.ActualChildReachable setup.tree.source cursor →
        ActualReaderPhysicalBranchInverse.dependencyReader input setup.c cursor = none := by
  intro cursor reachable
  exact physical_noReads setup empty cursor reachable

/-- **Actual no-reference Rule-4c extension on the empty physical branch.**  At every reachable
cursor and every fuel, the actual production Rule-4c build without a Rule-4b reference is the exact
key extension of the actual production Rule-4a build.  The all-absent reader hypothesis is derived
from the physical empty branch, not assumed. -/
theorem physical_rule4cNoReference_extension (setup : ActualSlotPhysicalSetup input)
    (empty : setup.NoPhysicalMarkedBranch) (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (reachable : input.certified.ActualChildReachable setup.tree.source cursor) :
    input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4cNoReference
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
        (referenceDependencyView input setup.c) fuel cursor =
      Option.map
        (input.certified.extendLocalizedRerootCumulativeRule45Key
          extendLocalizedRule4aPriorityToRule4cNoReference)
        (input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4a
          (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
          (referenceDependencyView input setup.c) fuel cursor) := by
  rw [← buildWithRead_dependencyReader_eq_build setup .rule4cNoReference fuel cursor,
    ← buildWithRead_dependencyReader_eq_build setup .rule4a fuel cursor]
  exact buildLocalizedRerootCumulativeRule45KeyWithRead?_rule4cNoReference_extension
    input.certified (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c)
    setup.tree.source (physical_noReads setup empty) fuel cursor reachable

/-- **Actual no-reference Rule-5 extension on the empty physical branch.** -/
theorem physical_rule5NoRule4bReference_extension (setup : ActualSlotPhysicalSetup input)
    (empty : setup.NoPhysicalMarkedBranch) (rule5Reference : RS) (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (reachable : input.certified.ActualChildReachable setup.tree.source cursor) :
    input.certified.buildLocalizedRerootCumulativeRule45Key?
        (.rule5NoRule4bReference rule5Reference)
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
        (referenceDependencyView input setup.c) fuel cursor =
      Option.map
        (input.certified.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4aPriorityToRule5NoRule4bReference rule5Reference))
        (input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4a
          (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
          (referenceDependencyView input setup.c) fuel cursor) := by
  rw [← buildWithRead_dependencyReader_eq_build setup
      (.rule5NoRule4bReference rule5Reference) fuel cursor,
    ← buildWithRead_dependencyReader_eq_build setup .rule4a fuel cursor]
  exact buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5NoRule4bReference_extension
    input.certified rule5Reference
    (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) setup.tree.source
    (physical_noReads setup empty) fuel cursor reachable

/-- **Actual no-reference Rule-4c success on the empty physical branch.**  A successful actual
Rule-4a build yields the successful actual no-reference Rule-4c build of the exact extended key at
the same cursor and fuel. -/
theorem physical_rule4cNoReference_success (setup : ActualSlotPhysicalSetup input)
    (empty : setup.NoPhysicalMarkedBranch) (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (reachable : input.certified.ActualChildReachable setup.tree.source cursor)
    (key : input.certified.LocalizedRerootCumulativeRule45Key)
    (computed : input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4a
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c) fuel cursor = some key) :
    input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4cNoReference
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
        (referenceDependencyView input setup.c) fuel cursor =
      some
        (input.certified.extendLocalizedRerootCumulativeRule45Key
          extendLocalizedRule4aPriorityToRule4cNoReference key) := by
  rw [physical_rule4cNoReference_extension setup empty fuel cursor reachable, computed]
  rfl

/-- **Actual no-reference Rule-5 success on the empty physical branch.** -/
theorem physical_rule5NoRule4bReference_success (setup : ActualSlotPhysicalSetup input)
    (empty : setup.NoPhysicalMarkedBranch) (rule5Reference : RS) (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (reachable : input.certified.ActualChildReachable setup.tree.source cursor)
    (key : input.certified.LocalizedRerootCumulativeRule45Key)
    (computed : input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4a
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c) fuel cursor = some key) :
    input.certified.buildLocalizedRerootCumulativeRule45Key?
        (.rule5NoRule4bReference rule5Reference)
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
        (referenceDependencyView input setup.c) fuel cursor =
      some
        (input.certified.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4aPriorityToRule5NoRule4bReference rule5Reference) key) := by
  rw [physical_rule5NoRule4bReference_extension setup empty rule5Reference fuel cursor reachable,
    computed]
  rfl

/-! ## Part C: actual build success on the physical branch

Nothing below assumes a successful build: the Rule-4a / Rule-4b keys are the actual outputs of the
production builder at the proved adequacy bound, and the Rule-4c/Rule-5 keys are the exact key
extensions of those very keys. -/






theorem localizedRule5StageFor_some_eq (reference commonReference : RS) :
    localizedRule5StageFor (some reference) commonReference = .rule5 reference commonReference :=
  rfl

/-- **Every entry of a successful actual Rule-4a build reads an absent observation** when the
physical branch is empty.  This is the all-`none` descriptor image that the no-reference projections
need. -/
theorem physical_noReads_descriptorImage (setup : ActualSlotPhysicalSetup input)
    (empty : setup.NoPhysicalMarkedBranch) (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (reachable : input.certified.ActualChildReachable setup.tree.source cursor)
    (key : input.certified.LocalizedRerootCumulativeRule45Key)
    (computed : input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4a
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c) fuel cursor = some key) :
    LocalizedStageDescriptorImage .rule4a (fun label => label = none) key.descriptor :=
  physical_descriptorImage_of_admitted setup .rule4a (fun label => label = none)
    (physical_noReads setup empty) fuel cursor reachable key computed

/-- **All-depth `take 1` recovery of the no-reference Rule-4c descriptor.** -/
theorem physical_rule4cNoReference_descriptor_take_one (setup : ActualSlotPhysicalSetup input)
    {key : input.certified.LocalizedRerootCumulativeRule45Key}
    (image : LocalizedStageDescriptorImage .rule4a (fun label => label = none) key.descriptor)
    (depth : Nat) :
    (((input.certified.extendLocalizedRerootCumulativeRule45Key
        extendLocalizedRule4aPriorityToRule4cNoReference key).descriptor.getD depth []).map
      (fun entry : OfficialSparseEntry (List Nat) => (entry.1, entry.2.take 1))) =
      key.descriptor.getD depth [] := by
  rw [extendLocalizedRerootCumulativeRule45Key_descriptor,
    extendLocalizedPriorityLayers_getD, List.map_map]
  have step : (key.descriptor.getD depth []).map
      ((fun entry : OfficialSparseEntry (List Nat) => (entry.1, entry.2.take 1)) ∘
        extendLocalizedPriorityEntry extendLocalizedRule4aPriorityToRule4cNoReference) =
      (key.descriptor.getD depth []).map id := by
    apply List.map_congr_left
    intro entry entryMem
    simp only [Function.comp_apply, extendLocalizedPriorityEntry_fst,
      extendLocalizedPriorityEntry_snd]
    rw [extendLocalizedRule4aPriorityToRule4cNoReference_take_one
      (image.getD depth entry entryMem)]
    rfl
  rw [step, List.map_id]

/-- **All-depth `take 1` recovery of the no-reference Rule-5 descriptor.** -/
theorem physical_rule5NoRule4bReference_descriptor_take_one
    (setup : ActualSlotPhysicalSetup input) (rule5Reference : RS)
    {key : input.certified.LocalizedRerootCumulativeRule45Key}
    (image : LocalizedStageDescriptorImage .rule4a (fun label => label = none) key.descriptor)
    (depth : Nat) :
    (((input.certified.extendLocalizedRerootCumulativeRule45Key
        (extendLocalizedRule4aPriorityToRule5NoRule4bReference rule5Reference)
        key).descriptor.getD depth []).map
      (fun entry : OfficialSparseEntry (List Nat) => (entry.1, entry.2.take 1))) =
      key.descriptor.getD depth [] := by
  rw [extendLocalizedRerootCumulativeRule45Key_descriptor,
    extendLocalizedPriorityLayers_getD, List.map_map]
  have step : (key.descriptor.getD depth []).map
      ((fun entry : OfficialSparseEntry (List Nat) => (entry.1, entry.2.take 1)) ∘
        extendLocalizedPriorityEntry
          (extendLocalizedRule4aPriorityToRule5NoRule4bReference rule5Reference)) =
      (key.descriptor.getD depth []).map id := by
    apply List.map_congr_left
    intro entry entryMem
    simp only [Function.comp_apply, extendLocalizedPriorityEntry_fst,
      extendLocalizedPriorityEntry_snd]
    rw [extendLocalizedRule4aPriorityToRule5NoRule4bReference_take_one rule5Reference
      (image.getD depth entry entryMem)]
    rfl
  rw [step, List.map_id]

/-- **Actual Rule-4b/4c/5 keys exist at every reachable cursor, at the production adequacy fuel.**
The Rule-4b key is the actual production build (derived from cursor validity, not assumed); the
Rule-4c and Rule-5 keys are the exact key extensions of that very Rule-4b key, with the same cursor
and fuel.  Constitutional, `labels` and `rankedLabels` are preserved and every descriptor sphere of
the extended keys recovers the Rule-4b sphere under the all-depth `take 2` projection.  The Rule-4b
and Rule-5 references are independent. -/
theorem exists_physical_stage_keys (setup : ActualSlotPhysicalSetup input)
    (rule4bReference rule5Reference : RS)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (reachable : input.certified.ActualChildReachable setup.tree.source cursor) :
    ∃ (k4b k4c k5 : input.certified.LocalizedRerootCumulativeRule45Key),
      input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule4b rule4bReference)
          (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
          (referenceDependencyView input setup.c)
          (localizedOccurrenceRerootEvaluationFuel
            (LocalizedUniversalReference.carrierFuel input)) cursor = some k4b ∧
        input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule4c rule4bReference)
            (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
            (referenceDependencyView input setup.c)
            (localizedOccurrenceRerootEvaluationFuel
              (LocalizedUniversalReference.carrierFuel input)) cursor = some k4c ∧
          input.certified.buildLocalizedRerootCumulativeRule45Key?
              (.rule5 rule4bReference rule5Reference)
              (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
              (referenceDependencyView input setup.c)
              (localizedOccurrenceRerootEvaluationFuel
                (LocalizedUniversalReference.carrierFuel input)) cursor = some k5 ∧
            k4c = input.certified.extendLocalizedRerootCumulativeRule45Key
                extendLocalizedRule4bPriorityToRule4c k4b ∧
              k5 = input.certified.extendLocalizedRerootCumulativeRule45Key
                  (extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference) k4b ∧
                k4c.constitutional = k4b.constitutional ∧
                  k5.constitutional = k4b.constitutional ∧
                    k4c.labels = k4b.labels ∧ k5.labels = k4b.labels ∧
                      k4c.rankedLabels = k4b.rankedLabels ∧ k5.rankedLabels = k4b.rankedLabels ∧
                        (∀ depth : Nat,
                          (((k4c.descriptor.getD depth []).map
                            (fun entry : OfficialSparseEntry (List Nat) =>
                              (entry.1, entry.2.take 2))) =
                            k4b.descriptor.getD depth [])) ∧
                          (∀ depth : Nat,
                            (((k5.descriptor.getD depth []).map
                              (fun entry : OfficialSparseEntry (List Nat) =>
                                (entry.1, entry.2.take 2))) =
                              k4b.descriptor.getD depth [])) := by
  obtain ⟨k4b, computed⟩ :=
    input.certified.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
      (.rule4b rule4bReference) (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c) cursor
      (reachable_cursor_dependency setup reachable).2
  have computed' : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (.rule4b rule4bReference) (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input)) cursor = some k4b := by
    simpa only [localizedOccurrenceRerootEvaluationFuel] using computed
  let k4c := input.certified.extendLocalizedRerootCumulativeRule45Key
    extendLocalizedRule4bPriorityToRule4c k4b
  let k5 := input.certified.extendLocalizedRerootCumulativeRule45Key
    (extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference) k4b
  have image : LocalizedStageDescriptorImage (.rule4b rule4bReference) LocalizedNoPseudoLabel
      k4b.descriptor :=
    physical_descriptorImage setup (.rule4b rule4bReference) _ cursor reachable k4b computed'
  refine ⟨k4b, k4c, k5, computed', ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact physical_rule4c_success setup rule4bReference _ cursor reachable k4b computed'
  · exact physical_rule5_success setup rule4bReference rule5Reference _ cursor reachable k4b computed'
  · intro depth
    exact physical_rule4c_descriptor_take_two setup image depth
  · intro depth
    exact physical_rule5_descriptor_take_two setup image depth

/-- **Actual Rule-4b/4c/5 keys exist at the physical slot cursor.**  The slot cursor is the source of
the actual slot tree, so this is the zero-step instance of `exists_physical_stage_keys`; the witness
keys are the actual production outputs. -/
theorem exists_physical_stage_keys_at_slot (setup : ActualSlotPhysicalSetup input)
    (rule4bReference rule5Reference : RS) :
    ∃ (k4b k4c k5 : input.certified.LocalizedRerootCumulativeRule45Key),
      input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule4b rule4bReference)
          (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
          (referenceDependencyView input setup.c)
          (localizedOccurrenceRerootEvaluationFuel
            (LocalizedUniversalReference.carrierFuel input))
          (setup.frame.cursorAt setup.slot) = some k4b ∧
        input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule4c rule4bReference)
            (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
            (referenceDependencyView input setup.c)
            (localizedOccurrenceRerootEvaluationFuel
              (LocalizedUniversalReference.carrierFuel input))
            (setup.frame.cursorAt setup.slot) = some k4c ∧
          input.certified.buildLocalizedRerootCumulativeRule45Key?
              (.rule5 rule4bReference rule5Reference)
              (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
              (referenceDependencyView input setup.c)
              (localizedOccurrenceRerootEvaluationFuel
                (LocalizedUniversalReference.carrierFuel input))
              (setup.frame.cursorAt setup.slot) = some k5 ∧
            k4c = input.certified.extendLocalizedRerootCumulativeRule45Key
                extendLocalizedRule4bPriorityToRule4c k4b ∧
              k5 = input.certified.extendLocalizedRerootCumulativeRule45Key
                  (extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference) k4b := by
  have reachable : input.certified.ActualChildReachable setup.tree.source
      (setup.frame.cursorAt setup.slot) := by
    rw [setup.tree_source]
    exact Relation.ReflTransGen.refl
  obtain ⟨k4b, k4c, k5, h4b, h4c, h5, h4cEq, h5Eq, _rest⟩ :=
    exists_physical_stage_keys setup rule4bReference rule5Reference
      (setup.frame.cursorAt setup.slot) reachable
  exact ⟨k4b, k4c, k5, h4b, h4c, h5, h4cEq, h5Eq⟩

/-- **Actual no-reference Rule-4c/Rule-5 keys exist at every reachable cursor on the empty physical
branch.**  The Rule-4a key is the actual production build (derived from cursor validity); the
no-reference Rule-4c and Rule-5 keys are its exact key extensions, with preserved constitutional,
`labels` and `rankedLabels` and the all-depth `take 1` descriptor projection. -/
theorem exists_physical_noReference_stage_keys (setup : ActualSlotPhysicalSetup input)
    (empty : setup.NoPhysicalMarkedBranch) (rule5Reference : RS)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (reachable : input.certified.ActualChildReachable setup.tree.source cursor) :
    ∃ (k4a k4c k5 : input.certified.LocalizedRerootCumulativeRule45Key),
      input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4a
          (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
          (referenceDependencyView input setup.c)
          (localizedOccurrenceRerootEvaluationFuel
            (LocalizedUniversalReference.carrierFuel input)) cursor = some k4a ∧
        input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4cNoReference
            (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
            (referenceDependencyView input setup.c)
            (localizedOccurrenceRerootEvaluationFuel
              (LocalizedUniversalReference.carrierFuel input)) cursor = some k4c ∧
          input.certified.buildLocalizedRerootCumulativeRule45Key?
              (.rule5NoRule4bReference rule5Reference)
              (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
              (referenceDependencyView input setup.c)
              (localizedOccurrenceRerootEvaluationFuel
                (LocalizedUniversalReference.carrierFuel input)) cursor = some k5 ∧
            k4c = input.certified.extendLocalizedRerootCumulativeRule45Key
                extendLocalizedRule4aPriorityToRule4cNoReference k4a ∧
              k5 = input.certified.extendLocalizedRerootCumulativeRule45Key
                  (extendLocalizedRule4aPriorityToRule5NoRule4bReference rule5Reference) k4a ∧
                k4c.constitutional = k4a.constitutional ∧
                  k5.constitutional = k4a.constitutional ∧
                    k4c.labels = k4a.labels ∧ k5.labels = k4a.labels ∧
                      k4c.rankedLabels = k4a.rankedLabels ∧ k5.rankedLabels = k4a.rankedLabels ∧
                        (∀ depth : Nat,
                          (((k4c.descriptor.getD depth []).map
                            (fun entry : OfficialSparseEntry (List Nat) =>
                              (entry.1, entry.2.take 1))) =
                            k4a.descriptor.getD depth [])) ∧
                          (∀ depth : Nat,
                            (((k5.descriptor.getD depth []).map
                              (fun entry : OfficialSparseEntry (List Nat) =>
                                (entry.1, entry.2.take 1))) =
                              k4a.descriptor.getD depth [])) := by
  obtain ⟨k4a, computed⟩ :=
    input.certified.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice .rule4a
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c) cursor
      (reachable_cursor_dependency setup reachable).2
  have computed' : input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4a
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input)) cursor = some k4a := by
    simpa only [localizedOccurrenceRerootEvaluationFuel] using computed
  let k4c := input.certified.extendLocalizedRerootCumulativeRule45Key
    extendLocalizedRule4aPriorityToRule4cNoReference k4a
  let k5 := input.certified.extendLocalizedRerootCumulativeRule45Key
    (extendLocalizedRule4aPriorityToRule5NoRule4bReference rule5Reference) k4a
  have image : LocalizedStageDescriptorImage .rule4a (fun label => label = none) k4a.descriptor :=
    physical_noReads_descriptorImage setup empty _ cursor reachable k4a computed'
  refine ⟨k4a, k4c, k5, computed', ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact physical_rule4cNoReference_success setup empty _ cursor reachable k4a computed'
  · exact physical_rule5NoRule4bReference_success setup empty rule5Reference _ cursor reachable
      k4a computed'
  · intro depth
    exact physical_rule4cNoReference_descriptor_take_one setup image depth
  · intro depth
    exact physical_rule5NoRule4bReference_descriptor_take_one setup rule5Reference image depth





theorem physical_empty_selected_references (setup : ActualSlotPhysicalSetup input)
    (empty : setup.NoPhysicalMarkedBranch) :
    localizedRule4bReferencesFromRankedLabels setup.key.prior.rule4aKey.rankedLabels = [] ∧
      setup.key.prior.references = [] ∧
        ∃ reading : input.certified.LocalizedRerootRule4bcReading,
          setup.key.prior.readings = [reading] ∧ reading.reference? = none := by
  rcases setup.physicalReferenceSelection_pointwise (Or.inl empty) with
    ⟨rankedEmpty, refsEmpty, reading, readingsEq, refNone, _notMarked, _rest⟩ |
      ⟨_c, _d, _descriptor, unique, _marked, _ranked, _refs, _reading, _descriptorEq, _rest⟩
  · exact ⟨rankedEmpty, refsEmpty, reading, readingsEq, refNone⟩
  · exact absurd unique.2.1 (empty _ unique.1)







theorem physical_selected_reference_of_unique (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance) :
    ∃ descriptor : RS,
      branchMarkedDescriptor input setup.c setup.frame setup.frameComputed setup.slot
          setup.singleBonded setup.acyclic setup.oAtom setup.oObserved center = some descriptor ∧
        localizedRule4bReferencesFromRankedLabels
            setup.key.prior.rule4aKey.rankedLabels = [descriptor] ∧
          setup.key.prior.references = [descriptor] ∧
            (∃ reading : input.certified.LocalizedRerootRule4bcReading,
              setup.key.prior.readings = [reading] ∧ reading.reference? = some descriptor) ∧
              descriptor = RS.ofHandedness (setup.positionSense (setup.nearestPosition unique)
                (setup.nearestPosition_marked unique)) := by
  rcases setup.physicalReferenceSelection_pointwise (Or.inr ⟨center, distance, unique⟩) with
    ⟨_ranked, _refs, _reading, _readingsEq, _refNone, notMarked, _rest⟩ |
      ⟨c', d', descriptor, unique', markedEq, ranked, refs, readingData, descriptorEq, _rest⟩
  · exact absurd (setup.nearestPosition_marked unique)
      (notMarked (setup.nearestPosition unique))
  · -- Two reader-free unique-nearest data of the same physical branch determine the same centre.
    obtain ⟨mem₁, marked₁, sphere₁, earlier₁, nearest₁⟩ := unique
    obtain ⟨mem₂, marked₂, sphere₂, earlier₂, _nearest₂⟩ := unique'
    obtain ⟨walk₁, path₁, length₁⟩ := sphere₁
    obtain ⟨walk₂, path₂, length₂⟩ := sphere₂
    -- `obtain` clears the destructed structure hypothesis; reconstruct the same reader-free
    -- unique-nearest datum so the final equation is stated at the given centre.
    have uniqueNearest : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance :=
      ⟨mem₁, marked₁, ⟨walk₁, path₁, length₁⟩, earlier₁, nearest₁⟩
    have le₁ : distance ≤ d' := by
      by_contra h
      exact earlier₁ c' mem₂ marked₂ walk₂ path₂ (by rw [length₂]; exact Nat.lt_of_not_le h)
    have le₂ : d' ≤ distance := by
      by_contra h
      exact earlier₂ center mem₁ marked₁ walk₁ path₁
        (by rw [length₁]; exact Nat.lt_of_not_le h)
    have distances : distance = d' := Nat.le_antisymm le₁ le₂
    have centerEq : center = c' :=
      (nearest₁ c' mem₂ marked₂ walk₂ path₂ (by rw [length₂]; exact distances.symm)).symm
    have bm : branchMarkedDescriptor input setup.c setup.frame setup.frameComputed setup.slot
        setup.singleBonded setup.acyclic setup.oAtom setup.oObserved c' =
        branchMarkedDescriptor input setup.c setup.frame setup.frameComputed setup.slot
          setup.singleBonded setup.acyclic setup.oAtom setup.oObserved center := by
      rw [centerEq]
    have markedEqCenter : branchMarkedDescriptor input setup.c setup.frame setup.frameComputed
        setup.slot setup.singleBonded setup.acyclic setup.oAtom setup.oObserved center =
        some descriptor :=
      bm.symm.trans markedEq
    have descriptorEq' : descriptor = RS.ofHandedness
        (setup.positionSense (setup.nearestPosition uniqueNearest)
          (setup.nearestPosition_marked uniqueNearest)) :=
      Option.some.inj (markedEq.symm.trans
        (bm.trans (setup.branchMarkedDescriptor_nearestPosition uniqueNearest)))
    exact ⟨descriptor, markedEqCenter, ranked, refs, readingData, descriptorEq'⟩






theorem physical_nearest_stage_keys (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance)
    (rule5Reference : RS) :
    ∃ (descriptor : RS) (k4b k4c k5 : input.certified.LocalizedRerootCumulativeRule45Key),
      branchMarkedDescriptor input setup.c setup.frame setup.frameComputed setup.slot
          setup.singleBonded setup.acyclic setup.oAtom setup.oObserved center = some descriptor ∧
        setup.key.prior.references = [descriptor] ∧
          input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule4b descriptor)
              (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
              (referenceDependencyView input setup.c)
              (localizedOccurrenceRerootEvaluationFuel
                (LocalizedUniversalReference.carrierFuel input))
              (setup.frame.cursorAt setup.slot) = some k4b ∧
            input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule4c descriptor)
                (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
                (referenceDependencyView input setup.c)
                (localizedOccurrenceRerootEvaluationFuel
                  (LocalizedUniversalReference.carrierFuel input))
                (setup.frame.cursorAt setup.slot) = some k4c ∧
              input.certified.buildLocalizedRerootCumulativeRule45Key?
                  (.rule5 descriptor rule5Reference)
                  (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
                  (referenceDependencyView input setup.c)
                  (localizedOccurrenceRerootEvaluationFuel
                    (LocalizedUniversalReference.carrierFuel input))
                  (setup.frame.cursorAt setup.slot) = some k5 ∧
                k4c = input.certified.extendLocalizedRerootCumulativeRule45Key
                    extendLocalizedRule4bPriorityToRule4c k4b ∧
                  k5 = input.certified.extendLocalizedRerootCumulativeRule45Key
                      (extendLocalizedRule4bPriorityToRule5 descriptor rule5Reference) k4b := by
  obtain ⟨descriptor, markedEq, _ranked, refs, _readingData, _descriptorEq⟩ :=
    physical_selected_reference_of_unique setup unique
  obtain ⟨k4b, k4c, k5, h4b, h4c, h5, h4cEq, h5Eq⟩ :=
    exists_physical_stage_keys_at_slot setup descriptor rule5Reference
  exact ⟨descriptor, k4b, k4c, k5, markedEq, refs, h4b, h4c, h5, h4cEq, h5Eq⟩

/-- **Physical stage-extension closure.**  The physical branch domain splits into exactly two cases,
and in each the actual production builder is instantiated without any reader, selection or build
success premise:

* **empty branch** -- the actual reader is absent at every reachable cursor, the actual selector
  returns no reference (`references = []` and `reference? = none`), and at every reachable cursor the
  actual no-reference Rule-4c and Rule-5 builds are the exact key extensions of the actual Rule-4a
  build;
* **unique nearest centre** -- the actual selector's reference is exposed with its actual label, and
  the actual Rule-4b/4c/5 builds at the slot cursor succeed at that reference with the Rule-4c/5 keys
  the exact key extensions of the actual Rule-4b key.

Deeper marked centres are unrestricted and the Rule-5 reference is arbitrary.  The all-depth
descriptor and field-preservation statements are the corresponding theorems above. -/
theorem physical_stage_extension_closure (setup : ActualSlotPhysicalSetup input)
    (branchDomain : PhysicalBranchDomain input setup.root setup.oAtom) :
    (setup.NoPhysicalMarkedBranch ∧
        localizedRule4bReferencesFromRankedLabels setup.key.prior.rule4aKey.rankedLabels = [] ∧
          setup.key.prior.references = [] ∧
            (∀ (rule5Reference : RS)
                (cursor : input.certified.LocalizedRerootCursor
                  (LocalizedUniversalReference.carrierFuel input))
                (reachable : input.certified.ActualChildReachable setup.tree.source cursor),
              ∃ (k4a k4c k5 : input.certified.LocalizedRerootCumulativeRule45Key),
                input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4a
                    (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
                    (referenceDependencyView input setup.c)
                    (localizedOccurrenceRerootEvaluationFuel
                      (LocalizedUniversalReference.carrierFuel input)) cursor = some k4a ∧
                  input.certified.buildLocalizedRerootCumulativeRule45Key? .rule4cNoReference
                      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
                      (referenceDependencyView input setup.c)
                      (localizedOccurrenceRerootEvaluationFuel
                        (LocalizedUniversalReference.carrierFuel input)) cursor = some k4c ∧
                    input.certified.buildLocalizedRerootCumulativeRule45Key?
                        (.rule5NoRule4bReference rule5Reference)
                        (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
                        (referenceDependencyView input setup.c)
                        (localizedOccurrenceRerootEvaluationFuel
                          (LocalizedUniversalReference.carrierFuel input)) cursor = some k5 ∧
                      k4c = input.certified.extendLocalizedRerootCumulativeRule45Key
                          extendLocalizedRule4aPriorityToRule4cNoReference k4a ∧
                        k5 = input.certified.extendLocalizedRerootCumulativeRule45Key
                            (extendLocalizedRule4aPriorityToRule5NoRule4bReference rule5Reference)
                            k4a)) ∨
      (∃ (center : input.certified.Atom) (distance : Nat) (descriptor : RS),
        PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance ∧
          branchMarkedDescriptor input setup.c setup.frame setup.frameComputed setup.slot
              setup.singleBonded setup.acyclic setup.oAtom setup.oObserved center = some descriptor ∧
            setup.key.prior.references = [descriptor] ∧
              (∀ (rule5Reference : RS),
                ∃ (k4b k4c k5 : input.certified.LocalizedRerootCumulativeRule45Key),
                  input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule4b descriptor)
                      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
                      (referenceDependencyView input setup.c)
                      (localizedOccurrenceRerootEvaluationFuel
                        (LocalizedUniversalReference.carrierFuel input))
                      (setup.frame.cursorAt setup.slot) = some k4b ∧
                    input.certified.buildLocalizedRerootCumulativeRule45Key? (.rule4c descriptor)
                        (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
                        (referenceDependencyView input setup.c)
                        (localizedOccurrenceRerootEvaluationFuel
                          (LocalizedUniversalReference.carrierFuel input))
                        (setup.frame.cursorAt setup.slot) = some k4c ∧
                      input.certified.buildLocalizedRerootCumulativeRule45Key?
                          (.rule5 descriptor rule5Reference)
                          (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
                          (referenceDependencyView input setup.c)
                          (localizedOccurrenceRerootEvaluationFuel
                            (LocalizedUniversalReference.carrierFuel input))
                          (setup.frame.cursorAt setup.slot) = some k5 ∧
                        k4c = input.certified.extendLocalizedRerootCumulativeRule45Key
                            extendLocalizedRule4bPriorityToRule4c k4b ∧
                          k5 = input.certified.extendLocalizedRerootCumulativeRule45Key
                              (extendLocalizedRule4bPriorityToRule5 descriptor rule5Reference) k4b)) := by
  rcases branchDomain with empty | ⟨center, distance, unique⟩
  · obtain ⟨rankedEmpty, refsEmpty, _reading, _readingsEq, _refNone⟩ :=
      physical_empty_selected_references setup empty
    refine Or.inl ⟨empty, rankedEmpty, refsEmpty, ?_⟩
    intro rule5Reference cursor reachable
    obtain ⟨k4a, k4c, k5, h4a, h4c, h5, h4cEq, h5Eq, _rest⟩ :=
      exists_physical_noReference_stage_keys setup empty rule5Reference cursor reachable
    exact ⟨k4a, k4c, k5, h4a, h4c, h5, h4cEq, h5Eq⟩
  · obtain ⟨descriptor, markedEq, _ranked, refs, _readingData, _descriptorEq⟩ :=
      physical_selected_reference_of_unique setup unique
    refine Or.inr ⟨center, distance, descriptor, unique, markedEq, refs, ?_⟩
    intro rule5Reference
    obtain ⟨k4b, k4c, k5, h4b, h4c, h5, h4cEq, h5Eq⟩ :=
      exists_physical_stage_keys_at_slot setup descriptor rule5Reference
    exact ⟨k4b, k4c, k5, h4b, h4c, h5, h4cEq, h5Eq⟩

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.NoPhysicalMarkedBranch
assert_kernel_only TetraStereo.OneCenter.dependencyReader_eq_productionReader
assert_kernel_only TetraStereo.OneCenter.buildWithRead_dependencyReader_eq_build
assert_kernel_only TetraStereo.OneCenter.actualChildReachable_iff_reflTransGen
assert_kernel_only TetraStereo.OneCenter.physicalReader_noPseudo
assert_kernel_only TetraStereo.OneCenter.physical_rule4c_extension
assert_kernel_only TetraStereo.OneCenter.physical_rule5_extension
assert_kernel_only TetraStereo.OneCenter.physical_rule5_descriptor_projection
assert_kernel_only TetraStereo.OneCenter.physical_rule4c_success
assert_kernel_only TetraStereo.OneCenter.physical_rule5_success
assert_kernel_only TetraStereo.OneCenter.physical_descriptorImage_of_admitted
assert_kernel_only TetraStereo.OneCenter.physical_descriptorImage
assert_kernel_only TetraStereo.OneCenter.physical_rule4c_descriptor_take_two
assert_kernel_only TetraStereo.OneCenter.physical_rule5_descriptor_take_two
assert_kernel_only TetraStereo.OneCenter.physicalBranchDomain_iff_empty_or_unique
assert_kernel_only TetraStereo.OneCenter.noPhysicalMarkedBranch_iff_branchMarkedDescriptor_eq_none
assert_kernel_only TetraStereo.OneCenter.physical_noReads
assert_kernel_only TetraStereo.OneCenter.physical_reader_none_of_empty
assert_kernel_only TetraStereo.OneCenter.physical_rule4cNoReference_extension
assert_kernel_only TetraStereo.OneCenter.physical_rule5NoRule4bReference_extension
assert_kernel_only TetraStereo.OneCenter.physical_rule4cNoReference_success
assert_kernel_only TetraStereo.OneCenter.physical_rule5NoRule4bReference_success
assert_kernel_only TetraStereo.OneCenter.localizedRule5StageFor_some_eq
assert_kernel_only TetraStereo.OneCenter.physical_noReads_descriptorImage
assert_kernel_only TetraStereo.OneCenter.physical_rule4cNoReference_descriptor_take_one
assert_kernel_only TetraStereo.OneCenter.physical_rule5NoRule4bReference_descriptor_take_one
assert_kernel_only TetraStereo.OneCenter.exists_physical_stage_keys
assert_kernel_only TetraStereo.OneCenter.exists_physical_stage_keys_at_slot
assert_kernel_only TetraStereo.OneCenter.exists_physical_noReference_stage_keys
assert_kernel_only TetraStereo.OneCenter.physical_empty_selected_references
assert_kernel_only TetraStereo.OneCenter.physical_selected_reference_of_unique
assert_kernel_only TetraStereo.OneCenter.physical_nearest_stage_keys
assert_kernel_only TetraStereo.OneCenter.physical_stage_extension_closure
