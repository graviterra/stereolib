import TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3FrameAndComparison
import TetraStereo.UniversalProof.SourceNativePlanarParserOccurrenceProofs.SourceNativePlanarParserOccurrence
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo.UniversalProof.SourceNativePlanarParserCausalModelProofs.SourceNativePlanarParserCausalModel

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativeRule3ObserverFrame
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3RecursiveKey
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3FrameAndComparison
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativePlanarParserOccurrenceProofs.SourceNativePlanarParserOccurrence

















































/-! ## 1. Node-reader equality under no ordinary double bond -/

/-- A source with no ordinary double bond has no Rule-3 ordinary-double-bond edge at any node. -/
theorem not_edge_of_noDouble (source : AuthoritativeChemicalInput)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge node := by
  rintro ⟨_real, current, parent, _currentComputed, _parentComputed, ordinary⟩
  exact noDouble parent current ordinary

/-- On a source without any ordinary double bond the source-native planar node reader is exactly the
committed spatial node reader: both resolve every node to the structural-nonunit outcome.  This is a
proof from the two independent `..._eq_some_none_of_not_edge` laws, never an assumed callback
equality. -/
theorem aromaticCanonicalPlanarRule3Node?_eq_spatial_of_noDouble
    (source : AuthoritativeChemicalInput)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    aromaticCanonicalPlanarRule3Node? source node = source.aromaticCanonicalRule3SpatialNode? node := by
  rw [source.aromaticCanonicalRule3SpatialNode?_eq_some_none_of_not_edge node
        (not_edge_of_noDouble source noDouble node),
      aromaticCanonicalPlanarRule3Node?_eq_some_none_of_not_edge source node
        (not_edge_of_noDouble source noDouble node)]

/-- The planar observer's common physical-unit exclusion callback agrees with the committed spatial
exclusion reader under no ordinary double bond.  Structured after exclusion, an unresolved genuine
unit is preserved, but on a no-double source every node is a structural nonunit. -/
theorem observeExcept_planarObserver_eq_spatialNodeExcept_of_noDouble
    (source : AuthoritativeChemicalInput)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    observeExcept (planarObserver source) excluded node =
      source.aromaticCanonicalRule3SpatialNodeExcept? excluded node := by
  have planarNegative : (planarObserver source).observe node = some none := by
    show aromaticCanonicalPlanarRule3Node? source node = some none
    exact aromaticCanonicalPlanarRule3Node?_eq_some_none_of_not_edge source node
      (not_edge_of_noDouble source noDouble node)
  have spatialNegative : source.aromaticCanonicalRule3SpatialNode? node = some none :=
    source.aromaticCanonicalRule3SpatialNode?_eq_some_none_of_not_edge node
      (not_edge_of_noDouble source noDouble node)
  simp [observeExcept, aromaticCanonicalRule3SpatialNodeExcept?, planarNegative, spatialNegative]

/-! ## 2. Frame and Rules-3--5 key-builder equality -/

/-- Generic executable-frame coincidence: if an observer's own raw and exclusion-aware callbacks are
the committed spatial readers, then the generic two-pass frame builder is exactly the committed
spatial two-pass frame builder.  Only the existing whole-function compiler identities
(`buildAromaticCanonicalUncancelledRule3SpatialKey?_eq_with`,
`buildAromaticCanonicalRule3SpatialKeyExcept?_eq_with`) and `funext` are used; the observer callbacks
are explicit hypotheses, never assumed equalities. -/
theorem buildRule3ObserverFrame?_eq_spatial_of_observe_eq
    (source : AuthoritativeChemicalInput) (observer : Rule3Observer source)
    (observeEq : observer.observe = source.aromaticCanonicalRule3SpatialNode?)
    (exceptEq : ∀ excluded, observeExcept observer excluded =
      source.aromaticCanonicalRule3SpatialNodeExcept? excluded)
    {carrierFuel : Nat} (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    buildRule3ObserverFrame? observer fuel cursors =
      source.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel cursors := by
  unfold buildRule3ObserverFrame?
  unfold TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRule3CanonicalKeyFrame?
  rw [observeEq]
  simp_rw [exceptEq]
  rw [← source.buildAromaticCanonicalUncancelledRule3SpatialKey?_eq_with (carrierFuel := carrierFuel)]
  simp_rw [← source.buildAromaticCanonicalRule3SpatialKeyExcept?_eq_with
    (carrierFuel := carrierFuel)]

/-- The source-native planar two-pass Rule-3 frame is exactly the committed spatial two-pass frame on
a no-double source.  The planar observer callbacks are the committed spatial readers by section 1, so
the generic executable-frame coincidence applies at the actual planar observer. -/
theorem buildAromaticCanonicalPlanarRule3Frame?_eq_spatial_of_noDouble
    (source : AuthoritativeChemicalInput)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    {carrierFuel : Nat} (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    buildAromaticCanonicalPlanarRule3Frame? source fuel cursors =
      source.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel cursors :=
  buildRule3ObserverFrame?_eq_spatial_of_observe_eq source (planarObserver source)
    (funext fun node => aromaticCanonicalPlanarRule3Node?_eq_spatial_of_noDouble source noDouble node)
    (fun excluded => funext fun node =>
      observeExcept_planarObserver_eq_spatialNodeExcept_of_noDouble source noDouble excluded node)
    fuel cursors

/-- The source-native planar Rules-3--5 occurrence builder is exactly the committed spatial
Rules-3--5 occurrence builder on a no-double source, at the same target, view, rule fuel and returned
cursor positions.  The unchanged compound Rule-4/5 builder is shared. -/
theorem buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?_eq_spatial_of_noDouble
    (source : AuthoritativeChemicalInput)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame? source target view fuel cursors =
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame? target view fuel cursors := by
  unfold buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
  unfold TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
  rw [buildAromaticCanonicalPlanarRule3Frame?_eq_spatial_of_noDouble source noDouble fuel cursors]

/-! ## 3. Priority evidence and descriptor equality -/

/-- On a no-double source the actual planar constitution priority evidence is exactly the committed
constitution priority evidence at the same target, view and rule fuel: only the delegated key builder
changes, and it agrees by section 2. -/
theorem planarConstitutionParserRichPriorityEvidence?_eq_constitution_of_noDouble
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    planarConstitutionParserRichPriorityEvidence? molecule source agreement writtenExact target view
        ruleFuel =
      constitutionParserRichPriorityEvidence? molecule source agreement writtenExact target view
        ruleFuel := by
  unfold planarConstitutionParserRichPriorityEvidence?
  unfold constitutionParserRichPriorityEvidence?
  simp_rw [buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?_eq_spatial_of_noDouble
    source noDouble target view ruleFuel]

/-- The actual planar constitution descriptor is exactly the committed constitution descriptor on a
no-double source, so it inherits the already-established actual closed `R` emission without any
assumed equality. -/
theorem planarConstitutionParserRichDescriptor?_eq_constitution_of_noDouble
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    planarConstitutionParserRichDescriptor? molecule source agreement writtenExact target view ruleFuel =
      constitutionParserRichDescriptor? molecule source agreement writtenExact target view ruleFuel := by
  unfold planarConstitutionParserRichDescriptor?
  unfold constitutionParserRichDescriptor?
  rw [planarConstitutionParserRichPriorityEvidence?_eq_constitution_of_noDouble molecule source
    agreement writtenExact noDouble target view ruleFuel]

/-! ## 4. Own scheduled causal decode closure for the NEW planar semantics -/

section CausalModel

variable (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
  (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)

/-- The scheduled decode closure of the NEW planar auxiliary semantics: the generic occurrence
scheduler decodes its own closure over the actual depth dependency. -/
noncomputable def planarConstitutionParserRichScheduledState (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalAuxiliaryState carrierFuel :=
  DeclarativeCIP.OccurrenceScheduler.decode
    (source.aromaticCanonicalOccurrenceSystem
      (planarConstitutionParserRichAuxiliarySemantics molecule source agreement writtenExact
        carrierFuel ruleFuel))
    (@source.AromaticCanonicalDepthDependency carrierFuel)
    (DeclarativeCIP.OccurrenceScheduler.closure
      (source.aromaticCanonicalOccurrenceSystem
        (planarConstitutionParserRichAuxiliarySemantics molecule source agreement writtenExact
          carrierFuel ruleFuel))
      (@source.AromaticCanonicalDepthDependency carrierFuel))

/-- The decoded planar state is a genuine model of the NEW planar occurrence system. -/
theorem planarConstitutionParserRichScheduledState_cipModel (carrierFuel ruleFuel : Nat) :
    (source.aromaticCanonicalOccurrenceSystem
      (planarConstitutionParserRichAuxiliarySemantics molecule source agreement writtenExact
        carrierFuel ruleFuel)).CIPModel
      (planarConstitutionParserRichScheduledState molecule source agreement writtenExact
        carrierFuel ruleFuel) :=
  source.aromaticCanonicalSchedulerClosure_cipModel
    (planarConstitutionParserRichAuxiliarySemantics molecule source agreement writtenExact
      carrierFuel ruleFuel)

/-- Any NEW planar model evaluates the actual planar descriptor at every occurrence. -/
theorem planarConstitutionParserRichModel_evaluates {carrierFuel ruleFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (planarConstitutionParserRichAuxiliarySemantics molecule source agreement writtenExact
        carrierFuel ruleFuel)).CIPModel state)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    planarConstitutionParserRichDescriptor? molecule source agreement writtenExact target
      (source.aromaticCanonicalDependencyView state target) ruleFuel = state target := by
  have fixed := (source.aromaticCanonicalOccurrenceSystem
    (planarConstitutionParserRichAuxiliarySemantics molecule source agreement writtenExact
      carrierFuel ruleFuel)).cipModel_iff_executableStateStep_fixed
    (source.aromaticCanonicalDerivationStepCorrespondence
      (planarConstitutionParserRichAuxiliarySemantics molecule source agreement writtenExact
        carrierFuel ruleFuel)) state |>.mp model
  exact congrFun fixed target

/-- Any assigned NEW planar model output carries the complete independent planar descriptor meaning. -/
theorem planarConstitutionParserRichModel_output_sound {carrierFuel ruleFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (planarConstitutionParserRichAuxiliarySemantics molecule source agreement writtenExact
        carrierFuel ruleFuel)).CIPModel state)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (descriptor : AromaticCanonicalAuxiliaryLabel)
    (assigned : state target = some descriptor) :
    PlanarConstitutionParserRichDescriptorMeaning molecule source agreement writtenExact target
      (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor :=
  planarConstitutionParserRichDescriptor?_sound molecule source agreement writtenExact target _
    ruleFuel descriptor
    ((planarConstitutionParserRichModel_evaluates molecule source agreement writtenExact state model
      target).trans assigned)

/-- Every NEW planar model is the scheduled decode closure: the model is unique. -/
theorem planarConstitutionParserRichModel_unique (carrierFuel ruleFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (planarConstitutionParserRichAuxiliarySemantics molecule source agreement writtenExact
        carrierFuel ruleFuel)).CIPModel state) :
    state = planarConstitutionParserRichScheduledState molecule source agreement writtenExact
      carrierFuel ruleFuel := by
  obtain ⟨_canonical, _canonicalModel, unique⟩ :=
    existsUnique_planarConstitutionParserRichCIPModel molecule source agreement writtenExact
      carrierFuel ruleFuel
  exact (unique state model).trans
    (unique _ (planarConstitutionParserRichScheduledState_cipModel molecule source agreement
      writtenExact carrierFuel ruleFuel)).symm

end CausalModel

/-! ## 5. Closed actual CFClBrI planar `R` witness and its independent planar meaning -/

namespace ClosedPlanarParserModel

open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge.ConstitutionClosedWitness

/-- The NEW planar auxiliary semantics at the actual closed CFClBrI target. -/
noncomputable def parserSemantics : parserSource.AromaticCanonicalRuleSemantics 0 :=
  planarConstitutionParserRichAuxiliarySemantics annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact 0 2

/-- The scheduled decode closure of the NEW planar semantics at the actual closed source. -/
noncomputable def parserScheduledState : parserSource.AromaticCanonicalAuxiliaryState 0 :=
  planarConstitutionParserRichScheduledState annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact 0 2

/-- The internally constructed planar scheduled state is a genuine model. -/
theorem parserScheduledState_cipModel :
    (parserSource.aromaticCanonicalOccurrenceSystem parserSemantics).CIPModel parserScheduledState :=
  planarConstitutionParserRichScheduledState_cipModel annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact 0 2

/-- The actual planar constitution channel emits `R` for **every** dependency view at the actual
closed target.  The planar/spatial executable coincidence is proved from the actual source's
no-double certificate; no label, key, sort or selector is supplied. -/
theorem parser_actual_planar_descriptor_R
    (view : parserSource.AromaticCanonicalDependencyView parserTarget) :
    planarConstitutionParserRichDescriptor? annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact parserTarget view 2 = some (.chiral RS.R) := by
  rw [planarConstitutionParserRichDescriptor?_eq_constitution_of_noDouble annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact
    TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence.ClosedParserWitness.parserSource_no_ordinary_double_bond
    parserTarget view 2]
  exact TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel.ClosedConstitutionParserModel.parser_actual_constitution_descriptor_R
    view

/-- The actual internally constructed planar scheduled state has `R` at the closed target, from the
actual matrix evaluation equation and no supplied label. -/
theorem parser_scheduled_R : parserScheduledState parserTarget = some (.chiral RS.R) := by
  rw [← planarConstitutionParserRichModel_evaluates annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact parserScheduledState
    parserScheduledState_cipModel parserTarget]
  exact parser_actual_planar_descriptor_R _

/-- The scheduled planar `R` carries the complete independent NEW planar descriptor meaning,
including the NEW declarative planar Rules-3--5 key frame judgment. -/
theorem parser_scheduled_R_meaning :
    PlanarConstitutionParserRichDescriptorMeaning annotatedRawCF parserSource
      parserSource_annotationAgreement parserSource_writtenExact parserTarget
      (parserSource.aromaticCanonicalDependencyView parserScheduledState parserTarget) 2
      (.chiral RS.R) :=
  planarConstitutionParserRichModel_output_sound annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact parserScheduledState
    parserScheduledState_cipModel parserTarget (.chiral RS.R) parser_scheduled_R

end ClosedPlanarParserModel

end TetraStereo.UniversalProof.SourceNativePlanarParserCausalModelProofs.SourceNativePlanarParserCausalModel
