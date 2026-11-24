import TetraStereo.OneCenter.CertificateExport
import TetraStereo.OneCenter.OfficialCIPEngine
import TetraStereo.OneCenter.CIPRules
import TetraStereo.OneCenter.RS
import TetraStereo.Engine.LocalizedChemicalRingPublic
import TetraStereo.Engine.LocalizedChemicalRingPhysicalCertificate
import TetraStereo.Engine.LocalizedChemicalRingExport
import TetraStereo.OneCenter.LocalizedChemicalRingScalarSymmetry
import TetraStereo.Engine.LocalizedChemicalRingFrozenExecution
import TetraStereo.Engine.CentresRing
import TetraStereo.Engine.CentresRingPairList
import TetraStereo.Examples.CentresRingSpiroCasing
import TetraStereo.Engine.CentresSpiroSource
import TetraStereo.Engine.LocalizedChemicalRingDirectPromotion
import TetraStereo.Engine.RingSignedArm
import TetraStereo.Engine.RingCarbonReport
import TetraStereo.Engine.RingComparisonAgreement
import TetraStereo.Engine.RingConfiguredPriorities
import TetraStereo.Engine.RingConfiguredGeometry
import TetraStereo.Engine.RingFrameCoverage
import TetraStereo.Engine.RingRecursiveSignedReport
import TetraStereo.Engine.RingGroupedReport
import TetraStereo.Engine.RingSphereQueue
import TetraStereo.Engine.RingOccurrenceStereo
import TetraStereo.Engine.RingRebuiltStereo
import TetraStereo.Engine.RingRawRenumbering
import TetraStereo.Engine.RingGeometryCertificates
import TetraStereo.Engine.RingNestedFrameCoverage
import TetraStereo.Engine.RingConstitutionalCoverage
import TetraStereo.Engine.RingAtomicHorizon
import TetraStereo.Engine.RingCarbonCoverage
import TetraStereo.Engine.RingConstitutionalRefinements
import TetraStereo.Engine.RingRetainedConstitution
import TetraStereo.Engine.RingActivePairSoundness
import TetraStereo.Engine.RingActiveMagnitude
import TetraStereo.Engine.RingActiveCarbonReport
import TetraStereo.Engine.RingMolecularSchedule
import TetraStereo.Engine.RingScheduledCarbonReport
import TetraStereo.Engine.RingRetainedChemicalPreorder
import TetraStereo.Engine.RingNestedMagnitude
import TetraStereo.Engine.RingClosedPairCasing
import TetraStereo.Engine.RingClosedGroupOverlap
import TetraStereo.Engine.RingSiblingKeyObstruction
import TetraStereo.Engine.RingProximalUnit
import TetraStereo.Engine.RingReferenceFirstSphere
import TetraStereo.Engine.RingReferenceObservationSupport
import TetraStereo.Engine.RingSpherePublication
import TetraStereo.Engine.RingSphereSingleTieRefusal
import TetraStereo.Engine.RingParentGroupWidth
import TetraStereo.Engine.RingProximalPair
import TetraStereo.Engine.RingMarkedOrbitCancellation
import TetraStereo.Engine.RingFrozenWordDiagnosis
import TetraStereo.Engine.RingFIFOPopulation
import TetraStereo.Engine.RingFIFOCommutation
import TetraStereo.Engine.RingPendantPromotedKey
import TetraStereo.Engine.RingTerminalReferenceRoles
import TetraStereo.Engine.RingPinnedReferences
import TetraStereo.Engine.RingInsertionCasing
import TetraStereo.Engine.RingUniversalCompatibility
import TetraStereo.Engine.RingCalibratedCompatibility
import TetraStereo.Engine.RingJointObservations
import TetraStereo.Engine.RingPublicationEquivalence
import TetraStereo.Engine.RingPromotionSymmetry
import TetraStereo.Engine.RingLocalInversion
import TetraStereo.Engine.RingCursorStereo
import TetraStereo.Engine.RingTwoPairSeparation
import TetraStereo.Engine.RingDiscoveredCasing
import TetraStereo.Engine.RingOccurrenceTable
import TetraStereo.Engine.RingRule4bEquivalence
import TetraStereo.Engine.RecursiveRingCertificate
import TetraStereo.Examples.HexachlorocyclohexaneClassification

set_option autoImplicit false

namespace TetraStereo
namespace Engine

open OneCenter

/-- First deciding stereochemical rule and exact signed score on each geometry
of a constitutionally tied pair at the addressed molecular focus. -/
abbrev ringGroupedStereoComparison? := RingGroupedStereo.scheduledComparison?

/-- Every constitutional tie at the molecular publication frontier has one
signed result over all legal parent-group orders on each geometry. -/
abbrev ringGroupedStereoAtFrontier := @RingGroupedStereo.scheduled_frontier

/-- Two-geometry molecular report in canonical detected-centre order, with
an explicit absence for a completed refusal. -/
abbrev ringGroupedMolecularReport? := RingGroupedReport.report?

/-- The same molecular decisions for every carbon in input order. -/
abbrev ringGroupedCarbonReport? := RingGroupedReport.carbonReport?

abbrev ringGroupedMolecularReportCorrect := RingGroupedReport.molecular_report
abbrev ringGroupedCarbonReportCorrect := RingGroupedReport.carbon_report
abbrev ringGroupedReportExact := RingGroupedReport.correct_iff

/-- Try constitution first and generate auxiliaries only for a root with a remaining tie. -/
abbrev ringStagedReport? := RingSphereQueue.stagedReport
abbrev ringStagedReportExact := RingSphereQueue.staged_report_exact

/-- Rebuild the zero-mass priorities inside every stereo pass at each root and auxiliary centre. -/
abbrev ringRecursiveZeroMassReport? := RingRebuiltStereo.report?
abbrev ringRecursiveZeroMassReportExact := RingRebuiltStereo.report_exact

/-- Molecular occurrence comparisons with a rebuilt zero-duplicate-mass constitutional gate. -/
abbrev ringOccurrenceIncidentScore? := RingOccurrenceStereo.incidentScore?
abbrev ringOccurrenceMatrixEntry := @RingOccurrenceStereo.matrix_entry

/-- Signed geometry and unordered pair reversals determine the full frozen report. -/
abbrev ringGeometricCentreCriterion := @RingGeometryCriterion.at_centre
abbrev ringGeometricPublicationTransport := @RingGeometryTransport.Presentation.publications
abbrev ringConfiguredAutomorphismPublications := @RingGeometryTransport.automorphism_publications
/-- Search the raw atom, bond and coordinate data for an exact change of numbering. -/
abbrev ringFindRawRenumbering? := RingRawRenumbering.find?
/-- The search succeeds exactly when a raw renumbering exists. -/
abbrev ringFindRawRenumberingExact := @RingRawRenumbering.find_complete
/-- Transport every scheduled ring occurrence from the physical input bijection. -/
abbrev ringRawRenumberingPublications := @RingRawRenumbering.publications
/-- Transport the selected report rows, including their atom identifiers. -/
abbrev ringRawRenumberingReport := @RingRawRenumbering.report
/-- Independently enumerated full reports agree up to atom identifiers and row order. -/
abbrev ringRawRenumberingFullReport := @RingRawRenumbering.full_report
abbrev ringRefusalFromMarkedExchanges := @RingGeometryExchange.refuse_of_exchanges
abbrev ringTwoPairRefusalCriterion := @RingBridgedPairs.Pairs.refusal_iff
abbrev ringDescriptorFromCoupledBonds := @RingMarkedIncidence.coupled_descriptor
abbrev ringGeometryContext? := RingGeometryCertificates.prepare?
abbrev ringCheckGeometricRefusal? := @RingGeometryCertificates.Context.refusal?
abbrev ringCheckCoupledDescriptor? := @RingGeometryCertificates.Context.descriptor?

/-- Signed edge, including molecular parent-group comparison at a remaining tie. -/
abbrev ringSpherePriorityEdge? := RingSpherePriority.edge?

/-- Propagation of certified frozen observations on one original carrier. -/
abbrev ringSpherePublication := RingSpherePublication.atRoot

/-- All twelve directed comparisons and the ordinary-pair refusal for a
recognized one-pair frame whose two tied arms have no visible tetrahedral center. -/
abbrev ringSilentPairFrame_complete := @RingSphereSingleTieRefusal.complete

/-- Membership in the public report with replacement of older marks when
all equal-element neighbor pairs have the same two atom identities. -/
abbrev ringReport_replacement_of_common_neighbors :=
  RingReferenceObservationSupport.report_of_common_equal_element_neighbors

/-- Every detected tetrahedral center has either its constitutionally determined hand,
the exact remaining ligand comparisons, or a missing geometric reading. -/
abbrev ringConstitutionalReport := LocalizedChemicalRing.ConstitutionalPartition.Cached.report

/-- Automatic whole-carbon report. Each resolved row carries its molecular assignment
or refusal evidence; the complete report requires evidence at every carbon. -/
abbrev ringCertifiedCarbonReport? := RingCarbonCoverage.report?

/-- Each success supplies the molecular ranking or refusal evidence for every carbon. -/
abbrev ringActiveCarbonReport? := RingActiveCarbonReport.report?

/-- Whole carbon inventory with priority for resolved original-root molecular publications
and earlier carbon certificates at uncovered roots. Each refusal retains its evidence. -/
abbrev ringScheduledCarbonReport? := RingScheduledCarbonReport.report?

/-- Both geometry-specific labels of this addressed occurrence after the deeper
publications in the specified original digraph have been computed. -/
abbrev ringAuxiliaryPublication := RingMolecularSchedule.atRoot

/-- Rank a retained occurrence using its frozen deeper publications, including
closed pairs of constitutionally tied siblings carrying opposite hands. -/
abbrev ringGroupedAuxiliaryAssignment? := RingClosedPairAssignment.assign?

/-- Pass closed-group publications down the original-root distance schedule. -/
abbrev ringGroupedAuxiliaryPublication := RingClosedPairAssignment.atRoot

/-- Publish assignments and ordinary one-pair refusals for closed mixed
sibling groups in the same original-root distance schedule. -/
abbrev ringClosedGroupPublication := RingClosedGroupTie.atRoot

/-- Determine the exact accepted fixed-seed word for every FIFO order
respecting the molecular constitutional priority blocks, when certified. -/
abbrev ringChemicalPairWord? := @RingFIFOCommutation.chemicalWord?

/-- Exhaustive option for a small retained arm. Every emitted possibility
has a complete traversal respecting Rules 1a, 1b and 2. Missing publications
remain visible in the returned list. -/
abbrev ringConstitutionalPairWords := @RingFIFOAlternatives.chemicalPairWords

/-- On the actual scheduled molecular state, return a required unpublished
occurrence, a word certified across all constitutional refinements, or two
complete conflicting traversals. Intended for individual arm diagnostics. -/
abbrev diagnoseRingPairWord := @RingFrozenWordDiagnosis.diagnose

/-- Exact domain of the two-geometry evaluator's comparison on one geometry,
once its ordered addressed profiles have been produced. -/
theorem ringPairProfilesCovered_iff (a b : List (List RingNestedActivePair.Visit)) (rev : Bool) :
    (RingNestedActivePair.decide? a b rev).isSome = true ↔
      a.map (List.map RingNestedActivePair.topology) = b.map (List.map RingNestedActivePair.topology) :=
  RingPairGateCount.decide_iff rev

/-- For a label actually published at this occurrence, its lowercase case is
equivalent to odd parity of the doubled comparisons in its molecular ranking. -/
theorem ringAuxiliaryPublication_lower_iff {i : LocalizedChemicalRing.Input}
    {root : i.certified.Atom} {q : RingActivePairs.Site i} (on : q.val.root = root)
    {v : RingNestedActivePair.Labels} (hit : ringAuxiliaryPublication i root q = some (some v)) :
    RingJointObservations.isLower (some v.1) = true ↔
      ∃ a : RingNestedActivePair.Assignment i q
          (RingNestedActivePair.masked q (ringAuxiliaryPublication i root)),
        RingNestedActivePair.assign? i q (RingNestedActivePair.masked q (ringAuxiliaryPublication i root)) = some a ∧
        v = a.labels ∧ RingActivePairReport.doubled a.matrix % 2 = 1 := by
  apply RingNestedActivePair.publication_lower_iff
  exact (RingMolecularSchedule.atRoot_eq on).symm.trans hit

/-- Read the retained molecular trace, including real/duplicate status and original
closure origin, on two incident directions of the same occurrence. -/
def ringRetainedChemicalComparison? (i : LocalizedChemicalRing.Input) (focus left right : RingActivePairs.Site i) :=
  RingRetainedChemicalTrace.compareAt? i focus left right

theorem ringRetainedChemicalComparison_source {i : LocalizedChemicalRing.Input}
    {f a b : RingActivePairs.Site i} {t} (h : ringRetainedChemicalComparison? i f a b = some t) :
    RingRetainedConstitution.Incident i.certified f a b ∧ ∃ x y,
      RingRetainedChemicalTrace.Expansion i ⟨a,some f⟩ x ∧ RingRetainedChemicalTrace.Expansion i ⟨b,some f⟩ y ∧
      t = RingRetainedChemicalTrace.keyTrace x y := RingRetainedChemicalTrace.compareAt?_source h

/-- Every pair of distinct incident directions at a real focus of an admitted molecule
has a full constitutional trace. A constitutional equality passes to stereochemical rules. -/
theorem ringRetainedChemicalComparison_total (i : LocalizedChemicalRing.Input)
    (f a b : RingActivePairs.Site i)
    (incident : RingRetainedConstitution.Incident i.certified f a b) :
    ∃ t x y, ringRetainedChemicalComparison? i f a b = some t ∧
      RingRetainedChemicalTrace.Expansion i ⟨a,some f⟩ x ∧ RingRetainedChemicalTrace.Expansion i ⟨b,some f⟩ y ∧
      t = RingRetainedChemicalTrace.keyTrace x y :=
  RingRetainedChemicalCoverage.admitted_incident i f a b incident

/-- Across distinct constitutional classes all readers give the same strict
score on both geometries, even if some auxiliary publications are missing. -/
theorem ringAuxiliaryEdge_between_classes {i : LocalizedChemicalRing.Input}
    {f : RingActivePairs.Site i} (a b : RingRetainedChemicalPreorder.Direction i f)
    (incident : RingRetainedConstitution.Incident i.certified f a.val b.val)
    (different : RingRetainedChemicalPreorder.orderWord (RingRetainedChemicalPreorder.keyFor a) ≠
      RingRetainedChemicalPreorder.orderWord (RingRetainedChemicalPreorder.keyFor b)) :
    ∃ s : Int, (s = -1 ∨ s = 1) ∧ ∀ read : RingNestedActivePair.Reader i,
      (RingNestedActivePair.edge? i f a.val b.val read).map Subtype.val = some (s,s) := by
  obtain ⟨t,_,_,found,_,_,_⟩ := ringRetainedChemicalComparison_total i f a.val b.val incident
  change RingRetainedChemicalTrace.compareAt? i f a.val b.val = some t at found
  have attached := Option.attach_eq_some _ ⟨t,found⟩
  have source := RingRetainedChemicalPreorder.table_source a b incident
  rw [found,Option.map_some] at source
  cases result : cipTraceOutcome t with
  | eq => exact (different ((RingRetainedChemicalPreorder.table_tie a b).mp
      (source.symm.trans (congrArg some result)))).elim
  | lt => exact ⟨-1,Or.inl rfl,fun read => by
      simp only [RingNestedActivePair.edge?,attached,Option.bind_eq_bind,Option.bind_some]
      split <;> rename_i h <;> first | rfl | exact nomatch result.symm.trans h⟩
  | gt => exact ⟨1,Or.inr rfl,fun read => by
      simp only [RingNestedActivePair.edge?,attached,Option.bind_eq_bind,Option.bind_some]
      split <;> rename_i h <;> first | rfl | exact nomatch result.symm.trans h⟩

/-- The executable four-ligand frame uses an identical strict signed score for
every reader whenever the two physical slots belong to different classes. -/
theorem ringFrameScore_between_classes {i : LocalizedChemicalRing.Input} {f : RingActivePairs.Site i}
    (fr : RingNestedActivePair.Frame i f) (a b : Fin 4)
    (apart : RingRetainedChemicalPreorder.representative fr.direction a ≠
      RingRetainedChemicalPreorder.representative fr.direction b) :
    ∃ s : Int, (s = -1 ∨ s = 1) ∧ ∀ read : RingNestedActivePair.Reader i,
      fr.score? read a b = some (s,s) := by
  apply ringAuxiliaryEdge_between_classes (fr.direction a) (fr.direction b)
  · apply fr.incident
    exact fun same => apart (congrArg _ same)
  · intro same
    exact apart ((RingRetainedChemicalPreorder.class_iff fr.direction a b).mpr
      ((RingRetainedChemicalPreorder.table_tie _ _).mpr same))

section
open RingRetainedChemicalPreorder (representative)
open RingRetainedChemicalTrace (Reaches)

/-- Discharge strict constitutional comparisons before looking up either
stereo publication, so these pairs need no auxiliary schedule evaluation. -/
def ringPriorityEdge? (i : LocalizedChemicalRing.Input) (f a b : RingActivePairs.Site i)
    (read : RingNestedActivePair.Reader i) : Option (Int × Int) :=
  match (RingRetainedChemicalTrace.compareAt? i f a b).map cipTraceOutcome with
  | some .lt => some (-1,-1)
  | some .gt => some (1,1)
  | some .eq => RingProximalUnit.edge? i f a b read
  | none => none

theorem ringPriorityEdge_eq (i : LocalizedChemicalRing.Input) (f a b : RingActivePairs.Site i)
    (read : RingNestedActivePair.Reader i) : ringPriorityEdge? i f a b read = RingProximalUnit.edge? i f a b read := by
  unfold ringPriorityEdge?
  cases prior : RingRetainedChemicalTrace.compareAt? i f a b with
  | none =>
    simp only [Option.map_none]
    unfold RingProximalUnit.edge?
    split
    · rename_i c _
      exact nomatch prior.symm.trans c.earlier
    · simp only [RingNestedActivePair.edge?,Option.attach_eq_none_iff.mpr prior,Option.bind_eq_bind,Option.bind_none,Option.map_none]
  | some t =>
    simp only [Option.map_some]
    have attached := Option.attach_eq_some _ ⟨t,prior⟩
    cases score : cipTraceOutcome t with
    | eq => rfl
    | lt | gt =>
      apply Eq.symm
      apply RingProximalUnit.preserves (i := i) (f := f) (a := a) (b := b) (read := read)
      unfold RingNestedActivePair.edge?
      rw [attached]
      dsimp only [Option.bind_eq_bind,Option.bind_some]
      split <;> rename_i h <;> first | rfl | exact nomatch score.symm.trans h

/-- Compare two directed ligands on the actual original-root schedule. A
strict P-92 decision at the incident pair of published units short-circuits
the deeper stereo traversals. Ordinary priority is checked first in the rule
hierarchy, including when this shortcut applies. -/
def ringScheduledPriorityEdge? (i : LocalizedChemicalRing.Input) (f a b : RingActivePairs.Site i) :=
  ringPriorityEdge? i f a b (RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i f.val.root))

/-- Conditionally materialize the twelve directed scores, with the proximal
Rule 4a decision enabled at every eligible pair. -/
def ringPriorityMatrix? {i f} (fr : RingNestedActivePair.Frame i f) (read : RingNestedActivePair.Reader i) :=
  RingActivePairReport.matrix? (fun a b => ringPriorityEdge? i f (fr.direction a).val (fr.direction b).val read)

/-- A slot needs an auxiliary traversal precisely when another distinct slot
has the same constitutional priority. -/
def ringSlotHasTiedPartner {i f} (fr : RingNestedActivePair.Frame i f) (a : Fin 4) : Prop :=
  ∃ b, a ≠ b ∧ representative fr.direction a = representative fr.direction b

private theorem tied_frame_score {i f} (fr : RingNestedActivePair.Frame i f)
    (read : RingNestedActivePair.Reader i) {a b : Fin 4} (different : a ≠ b)
    (same : representative fr.direction a = representative fr.direction b) :
    let fuel := 2*(i.certified.certified.input.molecule.atomCount+2)+2
    (fr.score? read a b).isSome = true ↔
      (RingNestedActivePair.retainedLevels? i read fuel [⟨(fr.direction a).val,some f⟩]).isSome = true ∧
      (RingNestedActivePair.retainedLevels? i read fuel [⟨(fr.direction b).val,some f⟩]).isSome = true := by
  have inc := fr.incident different
  obtain ⟨t,_,_,found,_,_,_⟩ := ringRetainedChemicalComparison_total i f _ _ inc
  change RingRetainedChemicalTrace.compareAt? i f _ _ = some t at found
  have src := RingRetainedChemicalPreorder.table_source _ _ inc
  rw [found, Option.map_some, (RingRetainedChemicalPreorder.class_iff _ _ _).mp same] at src
  simpa only [RingNestedActivePair.Frame.score?,Option.isSome_map] using
    RingAtomicProfileShape.edge_iff_materialized (read := read) found (Option.some.inj src)

private theorem arm_covered {i f} (fr : RingNestedActivePair.Frame i f)
    (read : RingNestedActivePair.Reader i) (a : Fin 4) :
    let q : RingActivePairs.Arm i := ⟨(fr.direction a).val,some f⟩
    let fuel := 2*(i.certified.certified.input.molecule.atomCount+2)+2
    (RingNestedActivePair.retainedLevels? i read fuel [q]).isSome = true ↔
      ∀ t, Reaches i q t → RingAtomicProfileShape.Ready i read t := by
  classical
  have valid := (i.certified.mem_localizedRerootNeighborFrames_iff f.val (fr.direction a).val.val).mpr
    ⟨(fr.direction a).val.property,(fr.direction a).property⟩
  have failed := RingAtomicProfileShape.missing_iff read ⟨(fr.direction a).val,some f⟩ valid
  simpa only [Option.isSome_iff_ne_none,not_exists,not_and,not_not] using not_congr failed

/-- Exact comparison coverage for the whole frame. Only slots in repeated
constitutional classes need auxiliary publications and local sibling-order
certificates. Each such arm is tested independently of its comparison partners. -/
theorem ringFrameMatrixCovered_iff {i f} (fr : RingNestedActivePair.Frame i f)
    (read : RingNestedActivePair.Reader i) :
    (RingActivePairReport.matrix? (fr.score? read)).isSome = true ↔
      ∀ a, ringSlotHasTiedPartner fr a →
        ∀ t, Reaches i ⟨(fr.direction a).val,some f⟩ t → RingAtomicProfileShape.Ready i read t := by
  rw [RingActivePairReport.matrix?_complete]
  constructor
  · rintro haveScores a ⟨b,ne,same⟩
    exact (arm_covered fr read a).mp (((tied_frame_score fr read ne same).mp (haveScores a b ne)).1)
  · intro ready a b ne
    by_cases same : representative fr.direction a = representative fr.direction b
    · exact (tied_frame_score fr read ne same).mpr
        ⟨(arm_covered fr read a).mpr (ready a ⟨b,ne,same⟩),
         (arm_covered fr read b).mpr (ready b ⟨a,Ne.symm ne,same.symm⟩)⟩
    · obtain ⟨s,_,strict⟩ := ringFrameScore_between_classes fr a b same
      rw [strict read]
      rfl


/-- At a deepest unresolved publication, the matrix exists exactly when every
visited occurrence on a required arm admits the chemical sibling order and
shallow observations. All needed publication cells are already derived. -/
theorem ringFrontierMatrixCovered_iff {i f} (fr : RingNestedActivePair.Frame i f)
    {root : i.certified.Atom} (listed : f ∈ RingMolecularSchedule.frontier i root) :
    let read := RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)
    (RingActivePairReport.matrix? (fr.score? read)).isSome = true ↔
      ∀ a, ringSlotHasTiedPartner fr a → ∀ t, Reaches i ⟨(fr.direction a).val,some f⟩ t →
        ∃ row, RingRetainedSiblingOrder.chemicalChildren? i t = some row ∧
          RingNestedActivePair.ShallowOrder i read row.val := by
  dsimp only
  rw [ringFrameMatrixCovered_iff]
  apply forall_congr'
  intro a
  apply imp_congr_right
  intro _
  apply forall_congr'
  intro t
  apply imp_congr_right
  intro path
  exact RingFrontierProfileShape.ready_iff listed t
    ((RingFrontierProfileShape.reaches_root path).trans (fr.direction a).property.1)


/-- Exact remaining requirement with the proximal shortcut. A directed pair
in a repeated class needs its two deeper traversals only when Rule 4a has no
strict certificate at the incident units. Each failure is witnessed by two
specific siblings at one reachable molecular occurrence. -/
theorem ringPriorityMatrixAtFrontier_iff {i f} (fr : RingNestedActivePair.Frame i f)
    {root : i.certified.Atom} (listed : f ∈ RingMolecularSchedule.frontier i root) :
    let read := RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)
    (ringPriorityMatrix? fr read).isSome = true ↔
      ∀ a b, a ≠ b → representative fr.direction a = representative fr.direction b →
        (¬ Nonempty (RingProximalUnit.Certificate i f (fr.direction a).val (fr.direction b).val read)) →
        ∀ k ∈ [a,b], ∀ t, Reaches i ⟨(fr.direction k).val,some f⟩ t →
          ¬ RingSiblingKeyObstruction.Collision i t ∧ ¬ RingSiblingKeyObstruction.ShallowConflict read t := by
  classical
  dsimp only
  let read := RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)
  let fuel := 2*(i.certified.certified.input.molecule.atomCount+2)+2
  let arm (a : Fin 4) : RingActivePairs.Arm i := ⟨(fr.direction a).val,some f⟩
  have material (k : Fin 4) :
      (RingNestedActivePair.retainedLevels? i read fuel [arm k]).isSome = true ↔
        ∀ t, Reaches i (arm k) t → ¬ RingSiblingKeyObstruction.Collision i t ∧
          ¬ RingSiblingKeyObstruction.ShallowConflict read t := by
    refine (arm_covered fr read k).trans ?_
    apply forall_congr'
    intro t
    apply imp_congr_right
    intro path
    exact (RingFrontierProfileShape.ready_iff listed t
      ((RingFrontierProfileShape.reaches_root path).trans (fr.direction k).property.1)).trans
      (RingSiblingKeyObstruction.ordered_shallow_iff i t read)
  simp only [ringPriorityMatrix?,RingActivePairReport.matrix?_complete,ringPriorityEdge_eq]
  constructor
  · intro full a b ne tied noHead k mem
    have deep := ((RingProximalUnit.covered_iff.mp (full a b ne)).resolve_left noHead)
    have both := (tied_frame_score fr read ne tied).mp (by simpa only
      [RingNestedActivePair.Frame.score?,Option.isSome_map] using deep)
    rcases List.mem_cons.mp mem with rfl | tail
    · exact (material _).mp both.1
    · obtain rfl := List.mem_singleton.mp tail
      exact (material _).mp both.2
  · intro clear a b ne
    apply RingProximalUnit.covered_iff.mpr
    by_cases head : Nonempty (RingProximalUnit.Certificate i f (fr.direction a).val (fr.direction b).val read)
    · exact Or.inl head
    · right
      suffices score : (fr.score? read a b).isSome = true by
        simpa only [RingNestedActivePair.Frame.score?,Option.isSome_map] using score
      by_cases tied : representative fr.direction a = representative fr.direction b
      · apply (tied_frame_score fr read ne tied).mpr
        exact ⟨(material a).mpr (clear a b ne tied head a (by simp)),
          (material b).mpr (clear a b ne tied head b (by simp))⟩
      · obtain ⟨s,_,strict⟩ := ringFrameScore_between_classes fr a b tied
        rw [strict read]
        rfl

end

section
open RingReachableReferencePolicy LocalizedChemicalRingRegeneratedLifetime
open LocalizedChemicalRingJointPreparedSourceModelExistence
open LocalizedChemicalRingJointPreparedSourceQueries (SourceQuery)
open LocalizedChemicalRingPhysicalSense (inputGeometry)

/-- With no nested constitutional collisions, replacing each older mark yields
precisely the rows of the public accumulated-reference report, including refusals. -/
theorem ringReport_replacement_iff (i : LocalizedChemicalRing.Input) (profile : LocalizedChemicalRing.Profile)
    (separated : ∀ p u : SourceQuery i.certified i.molecule,
      LocalizedMarkedTerminalReferenceScope.StrictDescendant i.molecule p.val u.val →
      let fr := frames i.certified i.molecule i.agreement i.admissible i.supported i.single
      Function.Injective (structuralColumn i.single fr p) ∨ Function.Injective (structuralColumn i.single fr u))
    (atom : Nat) (value : Option LocalizedTetrahedralRSPseudoDescriptor) :
    (atom,value) ∈ LocalizedChemicalRing.analyze profile i ↔
      ∃ c : i.certified.detectedMultiCenterMolecule.Center, c.val.val = atom ∧
        replaced i.single (frames i.certified i.molecule i.agreement i.admissible i.supported i.single)
          (inputGeometry i.certified) [] (finalQuery i.certified i.molecule i.agreement c) = value := by
  let fr := frames i.certified i.molecule i.agreement i.admissible i.supported i.single
  have model := actualQueryProfile_sourceModel i.certified i.molecule i.agreement i.admissible i.supported i.single
  have eqn := accumulated_eq_sourceModel i.certified i.molecule i.admissible i.single fr _ model
  rw [LocalizedChemicalRing.analyze_eq_prepared, mem_analyze_iff_sourceModel i.certified i.molecule i.agreement i.admissible i.supported i.single model]
  apply exists_congr
  intro c
  rw [← eqn]
  exact and_congr_right fun _ =>
    Eq.congr_left (agree_of_separated_collisions i.single fr i.admissible separated _ _)


/-- An atom-number test on the input graph suffices for exact replacement
readback at every center of the actual public report. Only the exceptional
center may have two distinct neighbors of the same element. -/
theorem ringReport_replacement_of_distinct_neighbors (i : LocalizedChemicalRing.Input)
    (profile : LocalizedChemicalRing.Profile) (exception : Nat)
    (apart : ∀ c : i.certified.detectedMultiCenterMolecule.Center, c.val.val ≠ exception →
      ∀ a b : i.certified.Atom, i.certified.moleculeGraph.Adj c.val a → i.certified.moleculeGraph.Adj c.val b →
        i.certified.moleculeGraph.atomZ a = i.certified.moleculeGraph.atomZ b → a = b)
    (c : i.certified.detectedMultiCenterMolecule.Center) (value : Option LocalizedTetrahedralRSPseudoDescriptor) :
    (c.val.val,value) ∈ LocalizedChemicalRing.analyze profile i ↔
      replaced i.single (frames i.certified i.molecule i.agreement i.admissible i.supported i.single)
        (inputGeometry i.certified) [] (finalQuery i.certified i.molecule i.agreement c) = value := by
  let fr := frames i.certified i.molecule i.agreement i.admissible i.supported i.single
  have model := actualQueryProfile_sourceModel i.certified i.molecule i.agreement i.admissible i.supported i.single
  have eqn := accumulated_eq_sourceModel i.certified i.molecule i.admissible i.single fr _ model
  rw [LocalizedChemicalRing.analyze_eq_prepared, LocalizedChemicalRingJointPreparedReport.mem_analyze_at_center_iff,
    assignCenter_eq_sourceModel i.certified i.molecule i.agreement i.admissible i.supported i.single model, ← eqn]
  exact Eq.congr_left (RingReferenceFirstSphere.agree_of_one_repeated_element_center i.single
    i.agreement i.admissible i.supported exception apart _ _)

end

/-- Only comparisons inside a constitutional tie class can contribute to
lowercase casing in an issued molecular assignment at any retained occurrence. -/
theorem ringAuxiliaryAssignment_lower_within_classes {i : LocalizedChemicalRing.Input}
    {f : RingActivePairs.Site i} {read : RingNestedActivePair.Reader i}
    (o : RingNestedActivePair.Assignment i f read) :
    RingJointObservations.isLower (some o.labels.1) = true ↔
      (LocalizedChemicalRing.ConstitutionalPartition.pairs.countP (fun p =>
        RingRetainedChemicalPreorder.representative o.frame.direction p.1 ==
          RingRetainedChemicalPreorder.representative o.frame.direction p.2 &&
          (o.matrix.get p.1 p.2).1.natAbs == 2)) % 2 = 1 := by
  rw [o.lower_iff_odd]
  suffices h : RingActivePairReport.doubled o.matrix = _ by rw [h]
  apply List.countP_congr
  intro p mem
  by_cases same : RingRetainedChemicalPreorder.representative o.frame.direction p.1 =
      RingRetainedChemicalPreorder.representative o.frame.direction p.2
  · simp [same]
  · obtain ⟨s,sign,constant⟩ := ringFrameScore_between_classes o.frame p.1 p.2 same
    have ne := ne_of_lt ((LocalizedChemicalRing.ConstitutionalPartition.pairs_spec p).mp mem)
    have fixed := Option.some.inj ((o.matrix.found p.1 p.2 ne).symm.trans (constant read))
    rcases sign with rfl | rfl <;> simp [fixed]

/-- Detect a chemically silent exchange in a single tied pair of the unmarked frame. -/
abbrev ringRetainedSilentPair? := RingRetainedSilentPair.find?

/-- Materialize the addressed publication cells once for multiple reads. -/
abbrev ringAuxiliaryTable := RingMolecularSchedule.publicationTable

/-- Each listed failure has a complete set of deeper publications. -/
abbrev ringAuxiliaryFrontier := RingMolecularSchedule.frontier

/-- Exhaust the shared-arm exchange class using a finite global permutation search. -/
abbrev ringExhaustiveExchangeReport? := RingCarbonCoverage.exhaustiveReport?

section
open RingChemicalPriority RingChemicalPriority.Recursive

/-- Classify the exact occurrence on both geometries. A successful inspection
retains its derivation, including the molecular evidence for a nonstereogenic
focus. The outer option records whether the search obtained a certificate. -/
def inspectRingOccurrence? (m : RawMolecule) (g : LocalizedGenericMarkedRecalculation.Geometry)
    (path : List Nat) (fuel : Nat) (hint : List Nat → Option Recursive.Frame)
    (radius : List Nat → Nat) :
    Option {_c : RingAuxiliaryInventory.Result m g path // saturatedWithHalogens m = true} := do
  if domain : saturatedWithHalogens m = true then
    return ⟨← RingAuxiliaryInventory.classify? m g hint radius fuel path,domain⟩
  none

/-- Compare two outward ligands under a specified incident reference atom.
The result retains both signed auxiliary inventories, the unchanged earlier
trees, and either a marked tree correspondence or the first strict sphere. -/
abbrev inspectRingReferenceComparison? := ReferenceDistance.compare?

/-- Recursively derive the auxiliary publications, comparison signs and
geometric verdict on the same retained digraph. Every used publication,
including a proved absence, belongs to one consistent occurrence table. -/
abbrev deriveRingReferenceOccurrence? := ReferenceDerivation.derive?

structure ReferenceCarbonReport (m : RawMolecule) (g : LocalizedGenericMarkedRecalculation.Geometry) where
  domain : saturatedWithHalogens m = true
  rows : List ((i : Nat) × ReferenceCarbonVerdict m g i)
  complete : rows.map Sigma.fst = RingCarbonReport.carbons m

def ReferenceCarbonReport.labels {m g} (r : ReferenceCarbonReport m g) :=
  r.rows.map fun row => (row.1,row.2.reading?.bind Reading.label)

/-- Build a report only when each carbon has a molecular derivation or
a pair of graph-equivalent terminal hydrogens. Each root starts with its
own occurrence table. -/
def deriveRingReferenceCarbons? (m : RawMolecule) (g : LocalizedGenericMarkedRecalculation.Geometry)
    (depth fuel : Nat) : Option (ReferenceCarbonReport m g) := do
  if domain : saturatedWithHalogens m = true then
    let root (i : Nat) : Option (ReferenceCarbonVerdict m g i) := do
      if let some h := RingCarbonReport.hydrogens? m i then return .hydrogens h
      return .derived (← deriveRingReferenceOccurrence? m g depth fuel [i])
    let rows ← (RingCarbonReport.carbons m).mapM (fun i => do return Sigma.mk i (← root i))
    if complete : rows.map Sigma.fst = RingCarbonReport.carbons m then return ⟨domain,rows,complete⟩
  none

/-- A fresh carbon root needs at most one recursion level per atom. -/
def deriveRingReferenceCarbonsAtBound? (m : RawMolecule) (g : LocalizedGenericMarkedRecalculation.Geometry)
    (depth : Nat) := deriveRingReferenceCarbons? m g depth m.atomCount

theorem deriveRingReferenceCarbonsAtBound?_stable (m : RawMolecule)
    (g : LocalizedGenericMarkedRecalculation.Geometry) (depth extra : Nat) :
    deriveRingReferenceCarbonsAtBound? m g depth = deriveRingReferenceCarbons? m g depth (m.atomCount+extra) := by
  have stable (i : Nat) : deriveRingReferenceOccurrence? m g depth m.atomCount [i] =
      deriveRingReferenceOccurrence? m g depth (m.atomCount+extra) [i] :=
    ReferenceDerivation.derive_stable _ _ _ _ _ _ (by simp)
  unfold deriveRingReferenceCarbonsAtBound? deriveRingReferenceCarbons?
  simp only [stable]

theorem ReferenceCarbonReport.atoms {m g} (r : ReferenceCarbonReport m g) :
    r.labels.map Prod.fst = RingCarbonReport.carbons m := by
  simpa only [labels,List.map_map,Function.comp_def] using r.complete

/-- Every assigned public report row has a recursively justified occurrence
table, an actual molecular priority order and a chemical reason for its
casing. A pair of equivalent hydrogens can only produce an absent row. -/
theorem ReferenceCarbonReport.chemical_letter {m g} (report : ReferenceCarbonReport m g) {i letter}
    (listed : (i,some letter) ∈ report.labels) :
    ∃ (c : ReferenceDerivation.Certificate m g [i]) (r : Reading) (a : List Nat) (n : Nat),
      ⟨i,.derived c⟩ ∈ report.rows ∧ c.verdict = some r ∧ ReferenceDerivation.LetterBasis m g c.published [i] a n ∧
      LocalizedGenericMarkedRecalculation.readback? g a = some r.actual ∧
      letter = (if n % 2 = 0 then .chiral r.actual else
        .pseudoasymmetric (pseudoRSOfRS r.actual)) := by
  obtain ⟨⟨j,row⟩,member,eqn⟩ := List.mem_map.mp listed
  obtain rfl : j = i := congrArg Prod.fst eqn
  have label := congrArg Prod.snd eqn
  cases row with
  | hydrogens h => contradiction
  | derived c =>
    change c.verdict.bind Reading.label = some letter at label
    cases hv : c.verdict with
    | none => simp [hv] at label
    | some r =>
      have d := c.derived
      rw [hv] at d
      obtain ⟨a,n,basis,raw,reading⟩ := d.chemical_letter
      have eqn : r.label = some letter := by simpa [hv] using label
      exact ⟨c,r,a,n,member,hv,basis,raw,Option.some.inj (eqn.symm.trans reading)⟩

/-- A public omission identifies either the terminal hydrogen pair or
the exact signed certificate that can be replayed in distance batches. -/
theorem ReferenceCarbonReport.absence {m g} (report : ReferenceCarbonReport m g) {i}
    (listed : (i,none) ∈ report.labels) :
    (∃ h : RingCarbonReport.HydrogenPair m i, ⟨i,.hydrogens h⟩ ∈ report.rows) ∨
    ∃ c : ReferenceDerivation.Certificate m g [i], ⟨i,.derived c⟩ ∈ report.rows ∧ c.verdict = none ∧
      ∀ es : InventoryPriority.Entries, es.Perm c.published →
        ReferenceDerivation.Scheduled m g [i] none (ReferenceDerivation.byDistance es) := by
  obtain ⟨⟨j,row⟩,member,eqn⟩ := List.mem_map.mp listed
  obtain rfl : j = i := congrArg Prod.fst eqn
  have label := congrArg Prod.snd eqn
  cases row with
  | hydrogens h => exact Or.inl ⟨h,member⟩
  | derived c =>
    change c.verdict.bind Reading.label = none at label
    cases hv : c.verdict with
    | none => exact Or.inr ⟨c,member,hv,fun _ perm => hv ▸ c.byDistance_replays perm⟩
    | some r => simp [hv,Reading.label,LocalizedGenericMarkedRecalculation.caseFromMirror?] at label

/-- A molecular two-pair diagnosis retains the complete signed input
inventory even when the eligible marks give different geometric readings. -/
structure RingTwoPairDiagnosis (m : RawMolecule) (g : LocalizedGenericMarkedRecalculation.Geometry) (root : Nat) where
  inputs : RingAuxiliaryInventory.SignedInputs m g
  experiment : Promotion.Experiment m [root] (InventoryPriority.omissions inputs.entries)
  coverage : (Promotion.TwoPairPriority.required experiment).Perm inputs.entries
  unique : ((Promotion.TwoPairPriority.required experiment).map Prod.fst).Nodup
  classified : Promotion.TwoPairPriority.Classified experiment

/-- Discover the four eligible promotions at a fresh carbon root. Every
child is classified at the same addressed occurrence and recursion budget
as in the ordinary whole-carbon report at the molecular bound. -/
def inspectRingTwoPair? (m : RawMolecule) (g : LocalizedGenericMarkedRecalculation.Geometry)
    (root depth : Nat) : Option (RingTwoPairDiagnosis m g root) := do
  if domain : saturatedWithHalogens m = true then
    let ⟨focus,reached⟩ ← (occurrence? m [root]).attach
    if carbon : (m.atoms[focus.atom]?).any (fun a => a.element == .C) = true then
      let children := RingAuxiliaryInventory.classify? m g (fun _ => none) (fun _ => depth) (m.atomCount+1)
      let inputs ← RingAuxiliaryInventory.gatherSigned? children (RingAuxiliaryInventory.promotionPaths m focus)
      let e ← RingAuxiliaryInventory.inventoryExperiment? depth focus domain reached carbon inputs.entries
      if coverage : (Promotion.TwoPairPriority.required e).Perm inputs.entries then
        if unique : ((Promotion.TwoPairPriority.required e).map Prod.fst).Nodup then
          return ⟨inputs,e,coverage,unique,← Promotion.TwoPairPriority.classify? e⟩
  none

def RingTwoPairDiagnosis.votes? {m g root} (d : RingTwoPairDiagnosis m g root) :=
  (d.classified.read? g).map (·.votes)

/-- A checked two-pair diagnosis on a spiro cut has a unique consensus
letter determined by its reference geometry and the written bonds. -/
theorem RingTwoPairDiagnosis.certificate_of_cut {m g root} (d : RingTwoPairDiagnosis m g root)
    {side : Nat → Bool} (cut : Promotion.TwoPairPriority.BondCut m root side)
    (fresh : root ∉ d.experiment.arms.map Promotion.Arm.ligand)
    {a b c f : Nat} (slots : d.classified.partition.order = [a,b,c,f])
    (both : ∀ color : Bool, ∃ k ∈ d.experiment.arms.map Promotion.Arm.ligand, side k = color)
    {reference : RS}
    (coordinates : LocalizedGenericMarkedRecalculation.readback? g [a,b,c,f] = some reference) :
    let hand := if side a == side c then reference else reference.swap
    (d.classified.certificate? g).map (·.reading) = some ⟨hand,hand.swap⟩ := by
  have reached := d.experiment.reached
  have focus : d.experiment.focus = canonicalCenterRoot root := by
    by_cases bound : root < m.atomCount
    · simpa [occurrence?,guard,bound] using reached.symm
    · simp [occurrence?,guard,bound] at reached
  let s : Promotion.TwoPairPriority.PopulationReading d.classified g := ⟨reference,slots ▸ coordinates⟩
  obtain ⟨high,low⟩ := d.classified.partition.split_by_cut cut focus fresh slots both
  exact s.certificate_of_cut cut focus fresh slots high low

theorem RingTwoPairDiagnosis.support {m g root} (d : RingTwoPairDiagnosis m g root) :
    (∀ arm ∈ d.experiment.arms, ∀ x ∈ arm.facts, Promotion.Justified m g x.1 x.2) ∧
    (∀ q ∈ InventoryPriority.omissions d.inputs.entries, ∃ es,
      Promotion.Negative m q es ∧ es ⊆ Promotion.TwoPairPriority.required d.experiment) := by
  constructor
  · intro arm ha x hx
    apply d.inputs.positive _ _ (d.coverage.mem_iff.mp _)
    exact List.mem_append_left _ (List.mem_map_of_mem
      (f := fun x : List Nat × Reading => (x.1,some x.2)) (List.mem_flatMap.mpr ⟨arm,ha,hx⟩))
  · intro q member
    have present : (q,none) ∈ Promotion.TwoPairPriority.required d.experiment :=
      List.mem_append_right _ (List.mem_map_of_mem (f := fun q => (q,none)) member)
    obtain ⟨es,h,sub⟩ := d.inputs.negative q (d.coverage.mem_iff.mp present)
    exact ⟨es,h,fun _ h => d.coverage.mem_iff.mpr (sub h)⟩

/-- A signed two-pair verdict exposes the finite reason for each absent
auxiliary and same-geometry derivations for every reading used by that reason. -/
theorem signedRingPair_omission_evidence {m g p} (s : Promotion.TwoPairPriority.SignedStep m g p)
    {q} (missing : q ∈ s.omitted) :
    ∃ sub, Promotion.Negative m q sub ∧ sub ⊆ Promotion.TwoPairPriority.required s.experiment ∧
      ∀ path reading, (path,some reading) ∈ sub → Promotion.Justified m g path reading := by
  obtain ⟨sub,negative,within⟩ := s.negative q missing
  refine ⟨sub,negative,within,?_⟩
  intro path reading member
  obtain pos | absent := List.mem_append.mp (within member)
  · obtain ⟨x,entry,equal⟩ := List.mem_map.mp pos
    obtain ⟨arm,inside,found⟩ := List.mem_flatMap.mp entry
    cases x with
    | mk addr value =>
      cases equal
      exact s.positive arm inside (addr,value) found
  · obtain ⟨_,_,equal⟩ := List.mem_map.mp absent
    cases equal

/-- Inspect a batch of retained paths using the table of lower-fuel auxiliary
results. Each distinct requested path has one row when fuel is positive. -/
def inspectRingOccurrences? (m : RawMolecule) (g : LocalizedGenericMarkedRecalculation.Geometry)
    (paths : List (List Nat)) (fuel : Nat) (hint : List Nat → Option Recursive.Frame)
    (radius : List Nat → Nat) :
    Option {_rows : OccurrenceTable.Table m g // saturatedWithHalogens m = true} :=
  if domain : saturatedWithHalogens m = true then
    some ⟨OccurrenceTable.evaluate m g hint radius fuel paths,domain⟩
  else none

/-- A requested lookup returns the same proof-carrying verdict as a fresh call
at that path, including certified absence and unresolved search. -/
theorem inspectRingOccurrences?_lookup {m g paths fuel hint radius p} (requested : p ∈ paths) :
    (inspectRingOccurrences? m g paths fuel hint radius).bind (fun batch => OccurrenceTable.read p batch.val) =
      (inspectRingOccurrence? m g p fuel hint radius).map Subtype.val := by
  by_cases domain : saturatedWithHalogens m = true
  · rw [show (inspectRingOccurrences? m g paths fuel hint radius).bind
        (fun batch => OccurrenceTable.read p batch.val) =
        OccurrenceTable.read p (OccurrenceTable.evaluate m g hint radius fuel paths) by
      simp [inspectRingOccurrences?,domain],OccurrenceTable.read_evaluate,if_pos requested]
    cases h : RingAuxiliaryInventory.classify? m g hint radius fuel p <;>
      simp [inspectRingOccurrence?,domain,h]
  · simp [inspectRingOccurrences?,inspectRingOccurrence?,domain]

/-- Use the molecular atom bound for recursive calls. The supplied depth
is the radius of the initial atomic-number comparison. -/
def classifyRingCarbonsAtBound? (m : RawMolecule) (g : LocalizedGenericMarkedRecalculation.Geometry)
    (depth : Nat) :=
  classifyDiscoveredRingCarbons? m g (m.atomCount+2) depth

/-- More recursive fuel changes neither the returned report nor failure at
the molecular bound. This holds for all fresh carbon roots simultaneously. -/
theorem classifyRingCarbonsAtBound?_stable (m : RawMolecule)
    (g : LocalizedGenericMarkedRecalculation.Geometry) (depth extra : Nat) :
    classifyRingCarbonsAtBound? m g depth =
      classifyDiscoveredRingCarbons? m g (m.atomCount+2+extra) depth := by
  apply classifyRingCarbons?_congr_fuel
  intro admitted i
  exact OccurrenceTable.classification_stable m (OccurrenceTable.endpoints_of_saturated admitted) g
    (fun _ => none) (fun _ => depth) [i] extra

/-- Rule 4b ranking of a ligand reached from a parent in the original
digraph. Every candidate carbon occurrence has its own auxiliary derivation.
The selected population contains the senior class at the first occupied
sphere. Its references determine the complete-word interval. -/
structure RankedRingArm (m : RawMolecule) (g : LocalizedGenericMarkedRecalculation.Geometry)
    (path : List Nat) (reverse : Bool) where
  domain : saturatedWithHalogens m = true
  hasParent : 2 ≤ path.length
  node : RawMolecule.CanonicalBranchNode
  reached : occurrence? m path = some node
  facts : Facts
  complete : carbonSites m (m.atomCount+1) node = some (facts.map Prod.fst)
  children : ∀ x ∈ facts, Promotion.Justified m g x.1 x.2
  population : ReferencePopulation m node facts reverse
  selected : referencePopulation? m node facts reverse = some population
  bounds : PairSpheres.Interval
  ranked : rankedArm? m node facts reverse = some (population.references,bounds)

/-- Derive every auxiliary in the supplied molecular arm, select the natural
reference or references on the requested geometry, and rank the complete arm.
The path starts at the original root and ends at the ligand being ranked. -/
def rankRingArm? (m : RawMolecule) (g : LocalizedGenericMarkedRecalculation.Geometry)
    (path : List Nat) (reverse : Bool) (fuel : Nat) (hint : List Nat → Option Recursive.Frame)
    (radius : List Nat → Nat) : Option (RankedRingArm m g path reverse) := do
  if domain : saturatedWithHalogens m = true then
    if parent : 2 ≤ path.length then
      let ⟨node,reached⟩ ← (occurrence? m path).attach
      let ⟨paths,found⟩ ← (carbonSites m (m.atomCount+1) node).attach
      let ⟨fs,coverage,valid⟩ ← Promotion.collect
        (fun q => (RingAuxiliaryInventory.classify? m g hint radius fuel q).bind (·.positive?)) paths
      let ⟨pop,selected⟩ ← (referencePopulation? m node fs reverse).attach
      let ⟨w,hw⟩ ← pop.range?.attach
      return ⟨domain,parent,node,reached,fs,coverage.symm ▸ found,valid,pop,selected,w,by
        simp [rankedArm?,selected,hw]⟩
  none

/-- Both reference selection and the range result are inhabited on the
molecular arm. Every permitted complete reading is enclosed. -/
theorem RankedRingArm.readings {m g p rev} (a : RankedRingArm m g p rev) :
    (∃ w, BestWord m a.node a.facts rev a.population.references w) ∧
    ∀ w, BestWord m a.node a.facts rev a.population.references w → a.bounds.Allows w :=
  rankedArm_sound a.ranked

/-- Compare the Rule 4b words of two checked arms. This projection requires
only their reference populations. The frame-level checker below also verifies
that the earlier rules tie before using the result for ligand priority. -/
theorem RankedRingArm.comparison {m g p q rev o} (l : RankedRingArm m g p rev)
    (r : RankedRingArm m g q rev)
    (decision : rankedDecision? l.population.references r.population.references l.bounds r.bounds = some o) :
    (∃ x y, BestWord m l.node l.facts rev l.population.references x ∧
      BestWord m r.node r.facts rev r.population.references y) ∧
    ∀ x y, BestWord m l.node l.facts rev l.population.references x →
      BestWord m r.node r.facts rev r.population.references y →
      RankResult l.population.references r.population.references x y o :=
  rankedDecision_sound l.ranked r.ranked decision

/-- A comparison on an actual pair in a tetrahedral frame. Both candidate
arms have complete, derived auxiliary inventories. The molecular correspondence
preserves every earlier-rule observation, including duplicate provenance and
stereogenic class, before Rule 4b is applied. -/
structure RingRule4bComparison (m : RawMolecule) (g : LocalizedGenericMarkedRecalculation.Geometry)
    (p : List Nat) (f : Recursive.Frame) (depth : Nat) (rev : Bool) where
  stage : f.stage = .fourB
  incident : frameOK m p depth f = true
  left : RankedRingArm m g (p ++ [f.left]) rev
  right : RankedRingArm m g (p ++ [f.right]) rev
  earlierTied : ∃ a b, inventory m left.node left.facts .fourB false f.rename = some a ∧
    inventory m right.node right.facts .fourB false id = some b ∧ a.Perm b
  sameSpheres : (sphereSites left.facts rev).map List.length = (sphereSites right.facts rev).map List.length
  result : Ordering
  decision : rankedDecision? left.population.references right.population.references
    left.bounds right.bounds = some result

def compareRingRule4b? (m : RawMolecule) (g : LocalizedGenericMarkedRecalculation.Geometry)
    (p : List Nat) (f : Recursive.Frame) (depth : Nat) (rev : Bool) (fuel : Nat)
    (hint : List Nat → Option Recursive.Frame) (radius : List Nat → Nat) :
    Option (RingRule4bComparison m g p f depth rev) := do
  if stage : f.stage = .fourB then
    if frame : frameOK m p depth f = true then
      let l ← rankRingArm? m g (p ++ [f.left]) rev fuel hint radius
      let r ← rankRingArm? m g (p ++ [f.right]) rev fuel hint radius
      let ⟨a,ha⟩ ← (inventory m l.node l.facts .fourB false f.rename).attach
      let ⟨b,hb⟩ ← (inventory m r.node r.facts .fourB false id).attach
      if equal : a.Perm b then
        if shape : (sphereSites l.facts rev).map List.length = (sphereSites r.facts rev).map List.length then
          let ⟨result,hd⟩ ← (rankedDecision? l.population.references r.population.references
            l.bounds r.bounds).attach
          return ⟨stage,frame,l,r,⟨a,b,ha,hb,equal⟩,shape,result,hd⟩
  none

theorem RingRule4bComparison.all_readings {m g p f depth rev}
    (c : RingRule4bComparison m g p f depth rev) :
    (∃ x y, BestWord m c.left.node c.left.facts rev c.left.population.references x ∧
      BestWord m c.right.node c.right.facts rev c.right.population.references y) ∧
    ∀ x y, BestWord m c.left.node c.left.facts rev c.left.population.references x →
      BestWord m c.right.node c.right.facts rev c.right.population.references y →
      RankResult c.left.population.references c.right.population.references x y c.result :=
  RankedRingArm.comparison c.left c.right c.decision

private theorem legalWord_shape {m arm fs rev ref w} (h : LegalWord m arm fs rev ref w) :
    w.map List.length = (sphereSites fs rev).map List.length := by
  obtain ⟨orders,h,rfl⟩ := h
  generalize sphereSites fs rev = sites at *
  induction h with
  | nil => rfl
  | cons h _ ih => exact congrArg₂ List.cons (by simpa using h.1.length_eq.symm) ih

private theorem bestWord_shape {m arm fs rev refs w} (h : BestWord m arm fs rev refs w) :
    w.map List.length = (sphereSites fs rev).map List.length := by
  cases h with
  | single one => exact legalWord_shape one
  | @dual _ _ x y l r =>
    rcases le_total x y with h | h
    · simpa only [max_eq_right h] using legalWord_shape r
    · simpa only [max_eq_left h] using legalWord_shape l

/-- With equally many references, the three-way comparison holds for the
literal complete words after removing sphere boundaries. Earlier-rule
inventory and site coverage keep their boundaries aligned. -/
theorem RingRule4bComparison.complete_words {m g p f depth rev}
    (c : RingRule4bComparison m g p f depth rev)
    (n : c.left.population.references.length = c.right.population.references.length)
    {x y} (l : BestWord m c.left.node c.left.facts rev c.left.population.references x)
    (r : BestWord m c.right.node c.right.facts rev c.right.population.references y) :
    match c.result with
    | .lt => x.flatten < y.flatten
    | .eq => x.flatten = y.flatten
    | .gt => y.flatten < x.flatten := by
  have shape := (bestWord_shape l).trans (c.sameSpheres.trans (bestWord_shape r).symm)
  have h := c.all_readings.2 x y l r
  cases result : c.result with
  | eq =>
    rw [result] at h
    exact congrArg List.flatten h.2
  | lt =>
    rw [result] at h
    rcases h with short | ⟨_,less⟩
    · omega
    · exact Hierarchy.flatten_strict shape less
  | gt =>
    rw [result] at h
    rcases h with short | ⟨_,less⟩
    · omega
    · exact Hierarchy.flatten_strict shape.symm less

private def ringAllowsReference {m g path} (arm : ReferenceArm m g path) (reverse : Bool) (ref : RS) :=
  saturatedWithHalogens m && (molecularReferences? m arm.node arm.facts reverse).any (fun refs => ref ∈ refs)

/-- Read an allowed Rule 4b reference on a reached arm with complete,
recursively derived auxiliary readings. A reference can be selected separately
on each of the two geometries. -/
def ringPairRange? {m g path} (arm : ReferenceArm m g path) (reverse : Bool) (ref : RS) :
    Option PairSpheres.Interval :=
  if ringAllowsReference arm reverse ref then some (pairedRange m arm.node arm.facts reverse ref) else none

/-- Combine the natural-reference order at the first occupied sphere with
the checked like/unlike comparisons at later two-site spheres. -/
def ringRefinedPairRange? {m g path} (arm : ReferenceArm m g path) (reverse : Bool) (ref : RS) :
    Option PairSpheres.Interval :=
  if ringAllowsReference arm reverse ref then some (refinedRange m arm.node arm.facts reverse ref) else none

/-- Every ordering of the arm's occurrences that respects the strict
like/unlike comparisons of its two-site spheres yields a word in the range. -/
theorem ringPairRange_allows {m g path reverse ref bounds orders} (arm : ReferenceArm m g path)
    (accepted : ringPairRange? arm reverse ref = some bounds)
    (ordersValid : List.Forall₂ (fun sites order => sites.Perm order ∧
      (sites.length = 2 → order.Pairwise (fun a b =>
        ¬ LikeBefore m arm.node arm.facts reverse ref b a))) (sphereSites arm.facts reverse) orders) :
    bounds.Allows (orders.map (List.map fun s => (s.2 == ref).toNat)) := by
  unfold ringPairRange? at accepted
  split at accepted
  · cases accepted
    exact pairedRange_allows (ordersValid.imp fun _ _ h => pairOrder_of_comparisons h.1 h.2)
  · contradiction

/-- The strengthened public range contains the complete word when the same
ordering also places like pairs first in the selected nearest class. -/
theorem ringRefinedPairRange_allows {m g path reverse ref bounds orders} (arm : ReferenceArm m g path)
    (accepted : ringRefinedPairRange? arm reverse ref = some bounds)
    (ordersValid : List.Forall₂ (fun sites order => sites.Perm order ∧
      (sites.length = 2 → order.Pairwise (fun a b =>
        ¬ LikeBefore m arm.node arm.facts reverse ref b a))) (sphereSites arm.facts reverse) orders)
    (nearest : PairSpheres.ReferenceOrder ((chiralSpheres arm.facts reverse).map
      (List.map (· == ref))) (orders.map (List.map fun s => s.2 == ref))) :
    bounds.Allows (orders.map (List.map fun s => (s.2 == ref).toNat)) := by
  unfold ringRefinedPairRange? at accepted
  split at accepted
  · cases accepted
    exact refinedRange_allows (ordersValid.imp fun _ _ h => pairOrder_of_comparisons h.1 h.2) nearest
  · contradiction


end

/-- Compare two incident ligands through Rules 1a, 1b and 2. A strict
result identifies the deciding rule and retains its molecular evidence.
Equality carries a complete isomorphism with isotope and duplicate data. -/
abbrev compareRingConstitution? := RingChemicalPriority.IsotopePriority.compareIncident?

/-- Return the complete four-ligand constitutional order together with a
proof of every ordered pair. For the deciding rule and its observed sphere
at runtime, use `compareRingConstitution?` on that pair. -/
abbrev rankRingIsotopes? := RingChemicalPriority.IsotopePriority.rank?

/-- Reading the certified constitutional order yields the actual volume
letter in uppercase, and an ordinary justified occurrence derivation. -/
theorem ringIsotopeAssignment {m path g r}
    (cert : RingChemicalPriority.IsotopePriority.Ranking m path)
    (read : RingChemicalPriority.Recursive.geometric g cert.order cert.order = some r) :
    RingChemicalPriority.Promotion.Justified m g path r ∧
      LocalizedGenericMarkedRecalculation.readback? g cert.order = some r.actual ∧
      r.reflected = r.actual.swap ∧ r.label = some (.chiral r.actual) :=
  ⟨.ordinary (.isotopic cert read),RingChemicalPriority.Recursive.constitutional_casing read⟩

/-- Derive the priorities and descriptor at an addressed occurrence, including
auxiliary assignments by Rule 6. The result checks the molecular domain and
carries the recursive chemical derivation for both geometry readings. -/
def deriveRingOccurrence? (m : RawMolecule) (g : LocalizedGenericMarkedRecalculation.Geometry)
    (path : List Nat) (fuel : Nat) (hint : List Nat → Option RingChemicalPriority.Recursive.Frame)
    (radius : List Nat → Nat) :
    Option {r // RingChemicalPriority.saturatedWithHalogens m = true ∧
      RingChemicalPriority.Promotion.Justified m g path r} := do
  let ⟨c,domain⟩ ← inspectRingOccurrence? m g path fuel hint radius
  let ⟨r,proof⟩ ← c.positive?
  return ⟨r,domain,proof⟩

/-- A completed Rule 6 experiment also records a fully investigated refusal.
Each eligible atom has a trial bound to its own molecular comparison table. -/
abbrev checkRingPromotions? := RingChemicalPriority.Promotion.analyze?

/-- Proof-carrying assignment for the explicitly numbered, fully chlorinated
six-membered ring. Carbon index zero is C-1. The input supplies only coordinates. -/
abbrev classifyHexachlorocyclohexaneCenter? := Examples.HexachlorocyclohexaneFamily.assign?

theorem classifyHexachlorocyclohexaneCenter?_isSome_iff
    (g : LocalizedGenericMarkedRecalculation.Geometry) (i : Fin 6) :
    (classifyHexachlorocyclohexaneCenter? g i).isSome = true ↔
      Examples.HexachlorocyclohexaneFamily.Nondegenerate g :=
  Examples.HexachlorocyclohexaneFamily.assignment_iff g i

/-- Any two family certificates for the same coordinates agree on every
neighbor hand and the focus hand, and hence on both letters and casing. -/
theorem hexachlorocyclohexane_reading_unique {g i}
    (a b : Examples.HexachlorocyclohexaneFamily.Assignment g i) :
    Examples.HexachlorocyclohexaneFamily.reading a.profile a.center =
      Examples.HexachlorocyclohexaneFamily.reading b.profile b.center := by
  have physical (k : Fin 5) : Examples.HexachlorocyclohexaneFamily.hand a.profile k =
      Examples.HexachlorocyclohexaneFamily.hand b.profile k :=
    Option.some.inj ((a.neighborReads k).symm.trans (b.neighborReads k))
  have faithful : ∀ p q : Fin 32,
      (List.finRange 5).map (Examples.HexachlorocyclohexaneFamily.hand p) =
        (List.finRange 5).map (Examples.HexachlorocyclohexaneFamily.hand q) → p = q := by decide +kernel
  exact congrArg₂ Examples.HexachlorocyclohexaneFamily.reading
    (faithful _ _ (List.map_congr_left fun k _ => physical k))
    (Option.some.inj (a.focusRead.symm.trans b.focusRead))

noncomputable section

/-!
  Public engine API.

  This module is a deliberate facade over the research proof kernel.  The kernel contains raw,
  deterministic orders and permutations because those are useful for proofs and executable
  normalization.  The public engine surface below does **not** expose those raw choices as
  stereochemical classifications.  Public results are tied to safe optional APIs and therefore
  certify that a successful descriptor came from resolved priorities rather than from an index
  tie-breaker.
-/

/-- Public descriptor-priority result for one-center descriptor-CIP.

Both fields are safe optional outputs.  There is intentionally no raw deterministic `order` or
`permutation` field here. -/
structure DescriptorPriorityResult {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V) where
  order? : Option (List (Fin 4))
  permutation? : Option (Equiv.Perm (Fin 4))
  safeOrder : order? = m.cipOrderDescriptor?
  safePermutation : permutation? = m.cipPermutationDescriptor?

/-- Public official-priority result for one-center official CIP. -/
structure OfficialPriorityResult {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) where
  order? : Option (List (Fin 4))
  permutation? : Option (Equiv.Perm (Fin 4))
  safeOrder : order? = m.cipOfficialOrder? context
  safePermutation : permutation? = m.cipOfficialPermutation? context

/-- Certified descriptor-CIP `R/S` assignment.

The proof field is the firewall: a successful public assignment is definitionally a theorem that
the safe descriptor-facing API returned `some descriptor`. -/
structure CertifiedRSAssignment {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V) (g : TetrahedralGeometry.Realization) where
  descriptor : RS
  certificate : m.rsCIP? g = some descriptor

/-- Certified official-CIP `R/S` assignment. -/
structure CertifiedOfficialRSAssignment {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (g : TetrahedralGeometry.Realization) where
  descriptor : RS
  certificate : m.rsOfficial? context g = some descriptor

/-- Public descriptor-CIP `R/S` result.

The only descriptor payload is optional and linked by proof to `rsCIP?`; unresolved ties therefore
remain `none` at the public boundary. -/
structure RSResult {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V) (g : TetrahedralGeometry.Realization) where
  descriptor? : Option RS
  safeAssignment : descriptor? = m.rsCIP? g

/-- Public official-CIP `R/S` result. -/
structure OfficialRSResult {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (g : TetrahedralGeometry.Realization) where
  descriptor? : Option RS
  safeAssignment : descriptor? = m.rsOfficial? context g

namespace DescriptorPriorityResult

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : OneCenterMolecule V}

/-- If the public descriptor permutation succeeds, descriptor priorities were resolved. -/
theorem resolved_of_permutation_some (result : DescriptorPriorityResult m)
    {permutation : Equiv.Perm (Fin 4)}
    (h : result.permutation? = some permutation) :
    m.ResolvedCIPDescriptor := by
  have hsomeResult : result.permutation?.isSome = true := by
    simp [h]
  have hsomeSafe : m.cipPermutationDescriptor?.isSome = true := by
    rw [← result.safePermutation]
    exact hsomeResult
  exact
    (m.cipPermutationCycleCut?_isSome_iff_resolvedCIPCycleCut).1
      (by simpa [OneCenterMolecule.cipPermutationDescriptor?] using hsomeSafe)

end DescriptorPriorityResult

namespace OfficialPriorityResult

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : OneCenterMolecule V}
variable {context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext}

/-- If the public official permutation succeeds, official priorities were resolved. -/
theorem resolved_of_permutation_some (result : OfficialPriorityResult m context)
    {permutation : Equiv.Perm (Fin 4)}
    (h : result.permutation? = some permutation) :
    m.ResolvedOfficialCIP context := by
  have hsomeResult : result.permutation?.isSome = true := by
    simp [h]
  have hsomeSafe : (m.cipOfficialPermutation? context).isSome = true := by
    rw [← result.safePermutation]
    exact hsomeResult
  exact (m.cipOfficialPermutation?_isSome_iff_resolved context).1 hsomeSafe

end OfficialPriorityResult

namespace CertifiedRSAssignment

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : OneCenterMolecule V}
variable {g : TetrahedralGeometry.Realization}

/-- A certified public descriptor assignment implies resolved descriptor priorities. -/
theorem resolved (assignment : CertifiedRSAssignment m g) :
    m.ResolvedCIPDescriptor := by
  classical
  by_cases h : m.ResolvedCIPDescriptor
  · exact h
  · have hnone : m.rsCIP? g = none := by
      simp [OneCenterMolecule.rsCIP?, OneCenterMolecule.rsCycleCut?, h]
    rw [assignment.certificate] at hnone
    contradiction

/-- Convert a public assignment into the existing theorem-artifact export format. -/
def toCertificateArtifact (assignment : CertifiedRSAssignment m g)
    (theoremName computedExpr expectedExpr proofTerm : String) : LeanCertificateArtifact :=
  compileRSAssignmentCertificate theoremName computedExpr expectedExpr proofTerm
    (m.rsCIP? g) assignment.descriptor assignment.certificate

end CertifiedRSAssignment

namespace CertifiedOfficialRSAssignment

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : OneCenterMolecule V}
variable {context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext}
variable {g : TetrahedralGeometry.Realization}

/-- A certified public official assignment implies resolved official priorities. -/
theorem resolved (assignment : CertifiedOfficialRSAssignment m context g) :
    m.ResolvedOfficialCIP context := by
  classical
  by_cases h : m.ResolvedOfficialCIP context
  · exact h
  · have hnone : m.rsOfficial? context g = none := by
      simp [OneCenterMolecule.rsOfficial?, h]
    rw [assignment.certificate] at hnone
    contradiction

/-- Convert a public official assignment into the existing theorem-artifact export format. -/
def toCertificateArtifact (assignment : CertifiedOfficialRSAssignment m context g)
    (theoremName computedExpr expectedExpr proofTerm : String) : LeanCertificateArtifact :=
  compileRSAssignmentCertificate theoremName computedExpr expectedExpr proofTerm
    (m.rsOfficial? context g) assignment.descriptor assignment.certificate

end CertifiedOfficialRSAssignment

namespace RSResult

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : OneCenterMolecule V}
variable {g : TetrahedralGeometry.Realization}

/-- Extract a certificate when the public descriptor result succeeded. -/
def certified? (result : RSResult m g) : Option (CertifiedRSAssignment m g) :=
  match h : result.descriptor? with
  | some descriptor =>
      some
        { descriptor := descriptor
          certificate := by
            rw [← result.safeAssignment]
            exact h }
  | none => none

/-- A `some` public descriptor is exactly a safe descriptor-CIP success. -/
theorem safe_some (result : RSResult m g) {descriptor : RS}
    (h : result.descriptor? = some descriptor) :
    m.rsCIP? g = some descriptor := by
  rw [← result.safeAssignment]
  exact h

/-- If the public descriptor result succeeds, descriptor priorities were resolved. -/
theorem resolved_of_some (result : RSResult m g) {descriptor : RS}
    (h : result.descriptor? = some descriptor) :
    m.ResolvedCIPDescriptor :=
  (CertifiedRSAssignment.resolved
    { descriptor := descriptor
      certificate := result.safe_some h })

end RSResult

namespace OfficialRSResult

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : OneCenterMolecule V}
variable {context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext}
variable {g : TetrahedralGeometry.Realization}

/-- Extract a certificate when the public official result succeeded. -/
def certified? (result : OfficialRSResult m context g) :
    Option (CertifiedOfficialRSAssignment m context g) :=
  match h : result.descriptor? with
  | some descriptor =>
      some
        { descriptor := descriptor
          certificate := by
            rw [← result.safeAssignment]
            exact h }
  | none => none

/-- A `some` public official descriptor is exactly a safe official-CIP success. -/
theorem safe_some (result : OfficialRSResult m context g) {descriptor : RS}
    (h : result.descriptor? = some descriptor) :
    m.rsOfficial? context g = some descriptor := by
  rw [← result.safeAssignment]
  exact h

/-- If the public official descriptor result succeeds, official priorities were resolved. -/
theorem resolved_of_some (result : OfficialRSResult m context g) {descriptor : RS}
    (h : result.descriptor? = some descriptor) :
    m.ResolvedOfficialCIP context :=
  (CertifiedOfficialRSAssignment.resolved
    { descriptor := descriptor
      certificate := result.safe_some h })

end OfficialRSResult

/-- Public descriptor-CIP priority engine. -/
def descriptorPriority {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V) : DescriptorPriorityResult m where
  order? := m.cipOrderDescriptor?
  permutation? := m.cipPermutationDescriptor?
  safeOrder := rfl
  safePermutation := rfl

/-- Public official-CIP priority engine. -/
def officialPriority {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    OfficialPriorityResult m context where
  order? := m.cipOfficialOrder? context
  permutation? := m.cipOfficialPermutation? context
  safeOrder := rfl
  safePermutation := rfl

/-- Public descriptor-CIP `R/S` engine. -/
def descriptorRS {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V) (g : TetrahedralGeometry.Realization) : RSResult m g where
  descriptor? := m.rsCIP? g
  safeAssignment := rfl

/-- Public official-CIP `R/S` engine. -/
def officialRS {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (g : TetrahedralGeometry.Realization) :
    OfficialRSResult m context g where
  descriptor? := m.rsOfficial? context g
  safeAssignment := rfl

/-- Public descriptor-CIP `R/S` certificate extraction. -/
def descriptorRSCertificate? {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V) (g : TetrahedralGeometry.Realization) :
    Option (CertifiedRSAssignment m g) :=
  (descriptorRS m g).certified?

/-- Public official-CIP `R/S` certificate extraction. -/
def officialRSCertificate? {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (g : TetrahedralGeometry.Realization) :
    Option (CertifiedOfficialRSAssignment m context g) :=
  (officialRS m context g).certified?

end
end Engine
end TetraStereo

namespace TetraStereo.Engine.CentresRing.Molecular

/-- The public receipt binds each source call by its chronological index, even
when the same operands and integer occur repeatedly at different paths. -/
theorem SourceChecked.comparison_at {input cs} (e : SourceChecked input cs) {i : Nat}
    {o : Observation} (seen : e.observed[i]? = some o) :
    ∃ c, (e.molecular.derivations.flatMap (fun row => row.2.derived.calls))[i]? = some c ∧
      c.observation = o := by
  rw [e.prefixes_eq] at seen
  have bind : expected e.molecular =
      (e.molecular.derivations.flatMap fun row => row.2.derived.calls).map Call.observation := by
    simp [expected,List.map_flatMap]
  rw [bind,List.getElem?_map] at seen
  exact Option.map_eq_some_iff.mp seen

/-- A strict source decision supplies its exact signed magnitude and a
molecular equality for each earlier named rule in the observed prefix. -/
theorem Call.source_decision (c : Call) {r : Rule} (win : c.winner = some r) :
    ∃ before t after, c.tests = before ++ (r,t) :: after ∧
      (∀ x ∈ before, x.2.Tied) ∧ t.value = some c.comparison.value ∧
      c.observation.rules = before.map (fun x => (x.1.sourceName, (0 : Int))) ++
        [(r.sourceName,c.comparison.value)] := by
  obtain ⟨before,t,after,tests,value,ties⟩ := c.earlier_equalities win
  refine ⟨before,t,after,tests,ties,value,?_⟩
  change sourcePrefix c.tests = _
  rw [tests]
  have nz := (c.earlier_ties win).1
  clear tests
  induction before with
  | nil => simp [sourcePrefix,value,nz]
  | cons x rest ih =>
    have zero := x.2.zero_iff.mpr (ties x (by simp))
    have tail := ih (fun y hy => ties y (List.mem_cons_of_mem _ hy))
    rcases x with ⟨rule,test⟩
    simp_all [sourcePrefix]

end TetraStereo.Engine.CentresRing.Molecular

assert_kernel_only TetraStereo.Engine.CentresRing.Molecular.SourceChecked.comparison_at
assert_kernel_only TetraStereo.Engine.CentresRing.Molecular.Call.source_decision

namespace TetraStereo.Engine.CentresRing.MirrorCasing
open OneCenter

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1200000 in
/-- On a structurally admitted ring the same center and layout give lowercase
s in one geometry and lowercase r in its exact reflection. Both evaluations
derive the auxiliary publications and signed comparisons from the input. -/
theorem exists_source_mirror_violation :
    ∃ (m : RawMolecule) (g : SpatialConfiguration) (l : Molecular.Layout),
      (LocalizedChemicalRing.admitRawSpatial? m g).isSome = true ∧
      (LocalizedChemicalRing.admitRawSpatial? m (reflectGeometry g)).isSome = true ∧
      (Molecular.derive m (fun i => g.positions[i]?) l).map (fun d => d.trace.label) = some "s" ∧
      (Molecular.derive m (fun i => (reflectGeometry g).positions[i]?) l).map
        (fun d => d.trace.label) = some "r" := by
  let l := Examples.CentresRingSpiroCasing.renumberedLayouts[3]' (by decide)
  refine ⟨Examples.CentresRingSpiroCasing.renumbered,Examples.CentresRingSpiroCasing.moved,l,?_⟩
  dsimp only [l]
  decide +kernel

end TetraStereo.Engine.CentresRing.MirrorCasing
assert_kernel_only TetraStereo.Engine.CentresRing.MirrorCasing.exists_source_mirror_violation

assert_kernel_only TetraStereo.Engine.classifyHexachlorocyclohexaneCenter?_isSome_iff
assert_kernel_only TetraStereo.Engine.hexachlorocyclohexane_reading_unique

assert_kernel_only TetraStereo.Engine.inspectRingOccurrence?
assert_kernel_only TetraStereo.Engine.inspectRingOccurrences?_lookup
assert_kernel_only TetraStereo.Engine.classifyRingCarbonsAtBound?_stable
assert_kernel_only TetraStereo.Engine.deriveRingOccurrence?
assert_kernel_only TetraStereo.Engine.rankRingIsotopes?
assert_kernel_only TetraStereo.Engine.compareRingConstitution?
assert_kernel_only TetraStereo.Engine.ringIsotopeAssignment
assert_kernel_only TetraStereo.Engine.checkRingPromotions?
assert_kernel_only TetraStereo.Engine.ringPairRange_allows
assert_kernel_only TetraStereo.Engine.ringRefinedPairRange_allows
assert_kernel_only TetraStereo.Engine.rankRingArm?
assert_kernel_only TetraStereo.Engine.RankedRingArm.readings
assert_kernel_only TetraStereo.Engine.RankedRingArm.comparison
assert_kernel_only TetraStereo.Engine.compareRingRule4b?
assert_kernel_only TetraStereo.Engine.RingRule4bComparison.all_readings
assert_kernel_only TetraStereo.Engine.RingRule4bComparison.complete_words

assert_kernel_only TetraStereo.Engine.signedRingPair_omission_evidence
assert_kernel_only TetraStereo.Engine.inspectRingTwoPair?
assert_kernel_only TetraStereo.Engine.RingTwoPairDiagnosis.certificate_of_cut
assert_kernel_only TetraStereo.Engine.RingTwoPairDiagnosis.support

assert_kernel_only TetraStereo.Engine.deriveRingReferenceCarbons?
assert_kernel_only TetraStereo.Engine.ReferenceCarbonReport.atoms

assert_kernel_only TetraStereo.Engine.ReferenceCarbonReport.chemical_letter
assert_kernel_only TetraStereo.Engine.ReferenceCarbonReport.absence
assert_kernel_only TetraStereo.Engine.deriveRingReferenceCarbonsAtBound?_stable

assert_kernel_only TetraStereo.Engine.ringConstitutionalReport
assert_kernel_only TetraStereo.Engine.ringCertifiedCarbonReport?
assert_kernel_only TetraStereo.Engine.ringExhaustiveExchangeReport?

assert_kernel_only TetraStereo.Engine.ringActiveCarbonReport?
assert_kernel_only TetraStereo.Engine.RingActivePairReport.Assignment.exact_letter_casing
assert_kernel_only TetraStereo.Engine.RingActiveCarbonReport.evidence
assert_kernel_only TetraStereo.Engine.ringAuxiliaryPublication
assert_kernel_only TetraStereo.Engine.ringAuxiliaryFrontier
assert_kernel_only TetraStereo.Engine.RingMolecularSchedule.derivation
assert_kernel_only TetraStereo.Engine.RingMolecularSchedule.complete_iff
assert_kernel_only TetraStereo.Engine.RingMolecularSchedule.frontier_gap
assert_kernel_only TetraStereo.Engine.CentresRing.PinnedReferences.molecularRun_exact
assert_kernel_only TetraStereo.Engine.RingUniversalCompatibility.no_universal_assignment
assert_kernel_only TetraStereo.Engine.RingCalibratedCompatibility.no_universal_calibrated_assignment
assert_kernel_only TetraStereo.Engine.RingInsertionCasing.molecular_atMostOne
assert_kernel_only TetraStereo.Engine.RingJointObservations.observations_hit_iff
assert_kernel_only TetraStereo.Engine.RingJointObservations.determined_by_cover
assert_kernel_only TetraStereo.Engine.RingPublicationEquivalence.ranked_schedule_iff
assert_kernel_only TetraStereo.Engine.RingPublicationEquivalence.carried_ranked_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Population.signed_of_transport
assert_kernel_only TetraStereo.Engine.ringScheduledCarbonReport?
assert_kernel_only TetraStereo.Engine.RingScheduledCarbonReport.evidence
assert_kernel_only TetraStereo.Engine.RingScheduledCarbonReport.refusal_evidence
assert_kernel_only TetraStereo.Engine.RingJointObservations.ranked_case_agreement
assert_kernel_only TetraStereo.Engine.RingPublicationEquivalence.divergence_frontier
assert_kernel_only TetraStereo.Engine.RingRetainedConstitution.key_cached
assert_kernel_only TetraStereo.Engine.RingMolecularSchedule.table_readback

assert_kernel_only TetraStereo.Engine.RingRetainedChemicalTrace.compareAt?_source
assert_kernel_only TetraStereo.Engine.RingRetainedSiblingOrder.missing_iff
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.shallow_invariant
assert_kernel_only TetraStereo.Engine.RingRetainedSilentPair.Certificate.no_promotion

assert_kernel_only TetraStereo.Engine.ringRetainedChemicalComparison_source
assert_kernel_only TetraStereo.Engine.ringAuxiliaryPublication_lower_iff
assert_kernel_only TetraStereo.Engine.ringGroupedAuxiliaryAssignment?
assert_kernel_only TetraStereo.Engine.RingClosedPairAssignment.derivation
assert_kernel_only TetraStereo.Engine.RingClosedPairAssignment.atRoot_lower_iff
assert_kernel_only TetraStereo.Engine.RingClosedPairGroup.Certificate.dual_reference
assert_kernel_only TetraStereo.Engine.RingClosedPairAssignment.frozen_source

assert_kernel_only TetraStereo.Engine.ringRetainedChemicalComparison_total
assert_kernel_only TetraStereo.Engine.ringAuxiliaryEdge_between_classes
assert_kernel_only TetraStereo.Engine.ringFrameScore_between_classes
assert_kernel_only TetraStereo.Engine.ringAuxiliaryAssignment_lower_within_classes
assert_kernel_only TetraStereo.Engine.RingOrdinaryPairRefusal.Certificate.no_promotion
assert_kernel_only TetraStereo.Engine.RingTerminalReferenceRoles.three_stabilizer
assert_kernel_only TetraStereo.Engine.RingTerminalReferenceRoles.four_stabilizer
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalPreorder.five_shapes
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.Assignment.lower_iff_odd
assert_kernel_only TetraStereo.Engine.RingTerminalReferenceRoles.ancestor_no_ranking

assert_kernel_only TetraStereo.Engine.ringClosedGroupPublication
assert_kernel_only TetraStereo.Engine.RingClosedGroupTie.derivation
assert_kernel_only TetraStereo.Engine.RingClosedGroupTie.atRoot_lower_iff
assert_kernel_only TetraStereo.Engine.RingClosedGroupRecognition.scheduled_absence_iff
assert_kernel_only TetraStereo.Engine.RingClosedGroupRecognition.tied_score
assert_kernel_only TetraStereo.Engine.RingClosedGroupOverlap.preserve_previous
assert_kernel_only TetraStereo.Engine.ringChemicalPairWord?
assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.chemical_word
assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.chemical_fixed_tie
assert_kernel_only TetraStereo.Engine.RingSeededFIFOTransport.separated_mirror_check
assert_kernel_only TetraStereo.Engine.RingPendantPromotedKey.refined_tie_of_ancestor

assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.chemical_two_seed
assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.unit_requires_reordering
assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.aligned_word
assert_kernel_only TetraStereo.Engine.RingFIFOPopulation.accepted_perm

assert_kernel_only TetraStereo.Engine.RingFIFOAlternatives.chemical_pair_words
assert_kernel_only TetraStereo.Engine.RingFIFOAlternatives.chemical_missing
assert_kernel_only TetraStereo.Engine.RingFIFOAlternatives.chemical_dichotomy
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.MarkedOrbit.Action.cancellation_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.MarkedOrbit.Action.certificate_iff

assert_kernel_only TetraStereo.Engine.diagnoseRingPairWord
assert_kernel_only TetraStereo.Engine.RingReferenceFirstSphere.agree_of_one_repeated_element_center
assert_kernel_only TetraStereo.Engine.ringReport_replacement_of_distinct_neighbors
assert_kernel_only TetraStereo.Engine.ringReport_replacement_iff
assert_kernel_only TetraStereo.Engine.ringPriorityEdge_eq
assert_kernel_only TetraStereo.Engine.ringScheduledPriorityEdge?
assert_kernel_only TetraStereo.Engine.ringPriorityMatrixAtFrontier_iff
assert_kernel_only TetraStereo.Engine.ringFrontierMatrixCovered_iff
assert_kernel_only TetraStereo.Engine.ringFrameMatrixCovered_iff
assert_kernel_only TetraStereo.Engine.RingReachableReferencePolicy.agree_of_separated_collisions
assert_kernel_only TetraStereo.Engine.RingReachableReferencePolicy.nested_selections
assert_kernel_only TetraStereo.Engine.ringPairProfilesCovered_iff
assert_kernel_only TetraStereo.Engine.ringProximalRule5Score?
assert_kernel_only TetraStereo.Engine.RingProximalPair.score_source
assert_kernel_only TetraStereo.Engine.RingProximalPair.seed_transport
assert_kernel_only TetraStereo.Engine.RingPairGateCount.edge_iff
assert_kernel_only TetraStereo.Engine.RingFrozenWordDiagnosis.derived
assert_kernel_only TetraStereo.Engine.RingHomogeneousPairPopulation.opposite_score

assert_kernel_only TetraStereo.Engine.ringSpherePriorityEdge?
assert_kernel_only TetraStereo.Engine.ringSpherePublication
assert_kernel_only TetraStereo.Engine.ringReport_replacement_of_common_neighbors
assert_kernel_only TetraStereo.Engine.RingSpherePriority.Certificate.stage_score
assert_kernel_only TetraStereo.Engine.RingSpherePublication.derivation
assert_kernel_only TetraStereo.Engine.RingSpherePublication.Ranked.casing_by_magnitude
assert_kernel_only TetraStereo.Engine.RingSphereCoverage.frontier
assert_kernel_only TetraStereo.Engine.RingParentGroupWidth.covered_widths
assert_kernel_only TetraStereo.Engine.RingSphereCoverage.silent_molecular
assert_kernel_only TetraStereo.Engine.ringSilentPairFrame_complete
assert_kernel_only TetraStereo.Engine.RingSphereSingleTieRefusal.covered
assert_kernel_only TetraStereo.Engine.RingSphereCoverage.frontier_consensus

assert_kernel_only TetraStereo.Engine.ringGroupedMolecularReport?
assert_kernel_only TetraStereo.Engine.ringGroupedCarbonReport?
assert_kernel_only TetraStereo.Engine.ringGroupedMolecularReportCorrect
assert_kernel_only TetraStereo.Engine.ringGroupedCarbonReportCorrect
assert_kernel_only TetraStereo.Engine.ringGroupedReportExact
assert_kernel_only TetraStereo.Engine.ringGroupedStereoComparison?
assert_kernel_only TetraStereo.Engine.ringGroupedStereoAtFrontier
