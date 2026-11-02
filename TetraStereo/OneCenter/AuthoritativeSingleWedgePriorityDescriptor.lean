import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceAlignment
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through5FixedPoint

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput
namespace SingleWedgeSource

open CertifiedLocalizedCIPInput

/-!
# Source-derived ordinary priority descriptors

The ordinary adapter constructs the final occurrence and its actual returned roots, runs the
production Rules-1a--5 key builder and strict tracked sorter, and replaces spatial-coordinate
lookup with the validated drawing interpretation. Drawing slots are matched to actual root IDs.
No caller supplies a depiction, point list, permutation, priority order, or successful key frame.

The auxiliary dependency view is explicit. Its model correctness is a separate obligation;
spatial-only auxiliary semantics are not asserted to cover drawing-dependent priorities.
Rule-6 tie resolution and source-policy approval are also separate obligations.
-/

def drawingPointForOccurrenceSlot? (drawing : Frame) (slots : List Nat)
    (index : Fin 4) : Option CartesianPoint3 :=
  slots[index.val]?.bind fun sourceSlot => drawing.points[sourceSlot]?

/-- Independent lookup relation in the written source frame. -/
def DrawingPointForOccurrenceSlot (drawing : Frame) (slots : List Nat)
    (index : Fin 4) (point : CartesianPoint3) : Prop :=
  ∃ sourceSlot, slots[index.val]? = some sourceSlot ∧
    drawing.points[sourceSlot]? = some point

theorem drawingPointForOccurrenceSlot?_eq_some_iff (drawing : Frame) (slots : List Nat)
    (index : Fin 4) (point : CartesianPoint3) :
    drawingPointForOccurrenceSlot? drawing slots index = some point ↔
      DrawingPointForOccurrenceSlot drawing slots index point := by
  unfold drawingPointForOccurrenceSlot? DrawingPointForOccurrenceSlot
  cases lookup : slots[index.val]? with
  | none => simp
  | some sourceSlot => simp

private theorem drawingPoint_mapM_sound (drawing : Frame) (slots : List Nat) :
    ∀ order points,
      order.mapM (drawingPointForOccurrenceSlot? drawing slots) = some points →
      List.Forall₂ (DrawingPointForOccurrenceSlot drawing slots) order points
  | [], points, computed => by
      simp at computed
      subst points
      exact .nil
  | index :: order, points, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : drawingPointForOccurrenceSlot? drawing slots index with
      | none => simp [headComputed] at computed
      | some point =>
          cases tailComputed : order.mapM (drawingPointForOccurrenceSlot? drawing slots) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst points
              exact .cons
                ((drawingPointForOccurrenceSlot?_eq_some_iff drawing slots index point).mp
                  headComputed)
                (drawingPoint_mapM_sound drawing slots order tail tailComputed)

structure OrdinaryPriorityEvidence (source : AuthoritativeChemicalInput) (carrierFuel : Nat) where
  drawing : Frame
  slots : List Nat
  keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel
  tracked : TrackedLocalizedLigandOrder
  points : List CartesianPoint3

noncomputable def ordinaryPriorityEvidence? (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (ruleFuel : Nat) : Option (OrdinaryPriorityEvidence source carrierFuel) := do
  let aligned ← occurrenceAlignment? source carrierFuel center
  let keys ← source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
    (source.aromaticCanonicalFinalOccurrence carrierFuel center) view ruleFuel
    (finalOccurrenceRoots source carrierFuel center)
  let tracked ← source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys
  let points ← tracked.highestFirst.mapM
    (drawingPointForOccurrenceSlot? aligned.1 aligned.2)
  some { drawing := aligned.1, slots := aligned.2, keys, tracked, points }

/-- Source geometry, actual root binding, independent key derivations, and strict priorities.
This relation contains no equation asserting successful extraction or successful sorting. -/
def OrdinaryPriorityEvidenceMeaning (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (ruleFuel : Nat) (evidence : OrdinaryPriorityEvidence source carrierFuel) : Prop :=
  SourceOccurrenceAlignment source carrierFuel center evidence.drawing evidence.slots ∧
    source.DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyFrame
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) view ruleFuel
      (finalOccurrenceRoots source carrierFuel center) evidence.keys ∧
    source.DeclarativeSafeAromaticCanonicalOccurrenceRule3Through5TrackedOrder
      evidence.keys evidence.tracked ∧
    List.Forall₂ (DrawingPointForOccurrenceSlot evidence.drawing evidence.slots)
      evidence.tracked.highestFirst evidence.points

theorem ordinaryPriorityEvidence?_sound (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (ruleFuel : Nat) (evidence : OrdinaryPriorityEvidence source carrierFuel)
    (computed : ordinaryPriorityEvidence? source carrierFuel center view ruleFuel =
      some evidence) :
    OrdinaryPriorityEvidenceMeaning source carrierFuel center view ruleFuel evidence := by
  unfold ordinaryPriorityEvidence? at computed
  cases alignedComputed : occurrenceAlignment? source carrierFuel center with
  | none => simp [alignedComputed] at computed
  | some aligned =>
      cases keysComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
          (source.aromaticCanonicalFinalOccurrence carrierFuel center) view ruleFuel
          (finalOccurrenceRoots source carrierFuel center) with
      | none => simp [alignedComputed, keysComputed] at computed
      | some keys =>
          cases trackedComputed :
              source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys with
          | none => simp [alignedComputed, keysComputed, trackedComputed] at computed
          | some tracked =>
              cases pointsComputed : tracked.highestFirst.mapM
                  (drawingPointForOccurrenceSlot? aligned.1 aligned.2) with
              | none => simp [alignedComputed, keysComputed, trackedComputed, pointsComputed]
                  at computed
              | some points =>
                  simp [alignedComputed, keysComputed, trackedComputed, pointsComputed]
                    at computed
                  subst evidence
                  exact ⟨occurrenceAlignment?_sound source carrierFuel center _ _ alignedComputed,
                    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_sound
                      _ view ruleFuel _ keys keysComputed,
                    source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_sound
                      keys tracked trackedComputed,
                    drawingPoint_mapM_sound _ _ _ _ pointsComputed⟩

noncomputable def ordinaryDescriptor? (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (ruleFuel : Nat) : Option AromaticCanonicalAuxiliaryLabel := do
  let evidence ← ordinaryPriorityEvidence? source carrierFuel center view ruleFuel
  let raw ← CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

def OrdinaryDescriptorMeaning (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (ruleFuel : Nat) (descriptor : AromaticCanonicalAuxiliaryLabel) : Prop :=
  ∃ evidence raw,
    OrdinaryPriorityEvidenceMeaning source carrierFuel center view ruleFuel evidence ∧
    CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor evidence.points raw ∧
    descriptor = classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons

theorem ordinaryDescriptor?_sound (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (ruleFuel : Nat) (descriptor : AromaticCanonicalAuxiliaryLabel)
    (computed : ordinaryDescriptor? source carrierFuel center view ruleFuel = some descriptor) :
    OrdinaryDescriptorMeaning source carrierFuel center view ruleFuel descriptor := by
  unfold ordinaryDescriptor? at computed
  cases evidenceComputed : ordinaryPriorityEvidence? source carrierFuel center view ruleFuel with
  | none => simp [evidenceComputed] at computed
  | some evidence =>
      cases rawComputed :
          CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? evidence.points with
      | none => simp [evidenceComputed, rawComputed] at computed
      | some raw =>
          simp [evidenceComputed, rawComputed] at computed
          subst descriptor
          exact ⟨evidence, raw,
            ordinaryPriorityEvidence?_sound source carrierFuel center view ruleFuel _
              evidenceComputed,
            (CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?_eq_some_iff _ _).mp
              rawComputed, rfl⟩

theorem ordinaryDescriptor?_refuses_unmatched_source (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (ruleFuel : Nat) (unmatched : ¬SourceOccurrenceAdmitted source carrierFuel center) :
    ordinaryDescriptor? source carrierFuel center view ruleFuel = none := by
  have refused : occurrenceAlignment? source carrierFuel center = none := by
    cases computed : occurrenceAlignment? source carrierFuel center with
    | none => rfl
    | some aligned =>
        exact False.elim (unmatched
          ((occurrenceAlignment?_exists_iff_admitted source carrierFuel center).mp
            ⟨aligned, computed⟩))
  simp [ordinaryDescriptor?, ordinaryPriorityEvidence?, refused]

/-- Source-only invocation with an internally constructed empty auxiliary state. This is a
concrete evaluator input, not an assertion that the empty state is a CIP fixed point. -/
noncomputable def ordinaryEmptyAuxiliaryDescriptor? (source : AuthoritativeChemicalInput)
    (carrierFuel ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    Option AromaticCanonicalAuxiliaryLabel :=
  ordinaryDescriptor? source carrierFuel center
    (source.aromaticCanonicalDependencyView (fun _ => none)
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)) ruleFuel

theorem ordinaryEmptyAuxiliaryDescriptor?_sound (source : AuthoritativeChemicalInput)
    (carrierFuel ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (descriptor : AromaticCanonicalAuxiliaryLabel)
    (computed : ordinaryEmptyAuxiliaryDescriptor? source carrierFuel ruleFuel center =
      some descriptor) :
    OrdinaryDescriptorMeaning source carrierFuel center
      (source.aromaticCanonicalDependencyView (fun _ => none)
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)) ruleFuel descriptor :=
  ordinaryDescriptor?_sound source carrierFuel center _ ruleFuel descriptor computed

/-! ## Executable first-shell atomic-separated domain

This separate finite source-native route requires all six priority pairs to be strictly decided
by the actual endpoint atomic numbers. Consequently no descriptor-dependent fallthrough is
needed for its priority criterion. Its theorem below states that criterion explicitly; equality
with the production occurrence-key implementation is not assumed or claimed.
-/

def drawingAtomicNumber? (source : AuthoritativeChemicalInput) (drawing : Frame)
    (index : Fin 4) : Option Nat := do
  let atomID ← drawing.endpoints[index.val]?
  let atom ← source.molecule.atoms[atomID]?
  some atom.element.atomicNumber

def drawingAtomicComparison? (source : AuthoritativeChemicalInput) (drawing : Frame)
    (left right : Fin 4) : Option ConstitutionalDescriptorHierarchyComparison := do
  let leftZ ← drawingAtomicNumber? source drawing left
  let rightZ ← drawingAtomicNumber? source drawing right
  some { ordering := compare leftZ rightZ, pseudo := false }

def AtomicStrict (source : AuthoritativeChemicalInput) (drawing : Frame)
    (left right : Fin 4) : Prop :=
  ∃ leftZ rightZ, drawingAtomicNumber? source drawing left = some leftZ ∧
    drawingAtomicNumber? source drawing right = some rightZ ∧
    compare leftZ rightZ = Ordering.gt

def atomicPairStrict (source : AuthoritativeChemicalInput) (drawing : Frame)
    (left right : Fin 4) : Bool :=
  (drawingAtomicComparison? source drawing left right).map
      (fun comparison => comparison.ordering == Ordering.gt) == some true

theorem atomicPairStrict_eq_true_iff (source : AuthoritativeChemicalInput) (drawing : Frame)
    (left right : Fin 4) :
    atomicPairStrict source drawing left right = true ↔ AtomicStrict source drawing left right := by
  unfold atomicPairStrict drawingAtomicComparison? AtomicStrict
  cases leftComputed : drawingAtomicNumber? source drawing left with
  | none => simp
  | some leftZ =>
      cases rightComputed : drawingAtomicNumber? source drawing right with
      | none => simp
      | some rightZ => simp

def atomicOrderCoherent (source : AuthoritativeChemicalInput) (drawing : Frame) :
    List (Fin 4) → Bool
  | [] => true
  | left :: rest => rest.all (atomicPairStrict source drawing left) &&
      atomicOrderCoherent source drawing rest

theorem atomicOrderCoherent_eq_true_iff (source : AuthoritativeChemicalInput) (drawing : Frame) :
    ∀ order, atomicOrderCoherent source drawing order = true ↔
      order.Pairwise (AtomicStrict source drawing)
  | [] => by simp [atomicOrderCoherent]
  | left :: rest => by
      rw [atomicOrderCoherent, Bool.and_eq_true, List.all_eq_true, List.pairwise_cons,
        atomicOrderCoherent_eq_true_iff]
      simp only [atomicPairStrict_eq_true_iff]

structure AtomicSeparatedEvidence where
  drawing : Frame
  tracked : TrackedLocalizedLigandOrder
  points : List CartesianPoint3

def atomicSeparatedEvidence? (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) : Option AtomicSeparatedEvidence := do
  let drawing ← extract? source center
  let tracked ← sortFourLocalizedLigandsTracked (drawingAtomicComparison? source drawing)
  if atomicOrderCoherent source drawing tracked.highestFirst then
    let points ← tracked.highestFirst.mapM fun index => drawing.points[index.val]?
    some { drawing, tracked, points }
  else none

private theorem drawingPointAt_mapM_sound (drawing : Frame) :
    ∀ order points,
      order.mapM (fun index : Fin 4 => drawing.points[index.val]?) = some points →
      List.Forall₂ (fun index : Fin 4 => fun point =>
        drawing.points[index.val]? = some point) order points
  | [], points, computed => by
      simp at computed
      subst points
      exact .nil
  | index :: order, points, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : drawing.points[index.val]? with
      | none => simp [headComputed] at computed
      | some point =>
          cases tailComputed : order.mapM (fun index : Fin 4 => drawing.points[index.val]?) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst points
              exact .cons headComputed (drawingPointAt_mapM_sound drawing order tail tailComputed)

def AtomicSeparatedEvidenceMeaning (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) (evidence : AtomicSeparatedEvidence) : Prop :=
  SourceFrame source center.val evidence.drawing ∧
    evidence.tracked.highestFirst.Perm (List.finRange 4) ∧
    evidence.tracked.highestFirst.Pairwise (AtomicStrict source evidence.drawing) ∧
    List.Forall₂ (fun index : Fin 4 => fun point =>
      evidence.drawing.points[index.val]? = some point)
      evidence.tracked.highestFirst evidence.points

theorem atomicSeparatedEvidence?_sound (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) (evidence : AtomicSeparatedEvidence)
    (computed : atomicSeparatedEvidence? source center = some evidence) :
    AtomicSeparatedEvidenceMeaning source center evidence := by
  unfold atomicSeparatedEvidence? at computed
  cases drawingComputed : extract? source center with
  | none => simp [drawingComputed] at computed
  | some drawing =>
      cases trackedComputed : sortFourLocalizedLigandsTracked
          (drawingAtomicComparison? source drawing) with
      | none => simp [drawingComputed, trackedComputed] at computed
      | some tracked =>
          cases coherent : atomicOrderCoherent source drawing tracked.highestFirst with
          | false => simp [drawingComputed, trackedComputed, coherent] at computed
          | true =>
              cases pointsComputed : tracked.highestFirst.mapM
                  (fun index : Fin 4 => drawing.points[index.val]?) with
              | none => simp [drawingComputed, trackedComputed, coherent, pointsComputed]
                  at computed
              | some points =>
                  simp [drawingComputed, trackedComputed, coherent, pointsComputed] at computed
                  subst evidence
                  exact ⟨(extract?_eq_some_iff source center drawing).mp drawingComputed,
                    sortFourLocalizedLigandsTracked_perm _ tracked trackedComputed,
                    (atomicOrderCoherent_eq_true_iff source drawing _).mp coherent,
                    drawingPointAt_mapM_sound drawing _ _ pointsComputed⟩

def atomicSeparatedDescriptor? (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) : Option RS := do
  let evidence ← atomicSeparatedEvidence? source center
  CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? evidence.points

/-- A fully source-bound Rule-1a judgment with a strict priority criterion for all pairs. -/
def AtomicSeparatedDescriptorMeaning (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) (descriptor : RS) : Prop :=
  ∃ evidence, AtomicSeparatedEvidenceMeaning source center evidence ∧
    CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor evidence.points descriptor

theorem atomicSeparatedDescriptor?_sound (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) (descriptor : RS)
    (computed : atomicSeparatedDescriptor? source center = some descriptor) :
    AtomicSeparatedDescriptorMeaning source center descriptor := by
  unfold atomicSeparatedDescriptor? at computed
  cases evidenceComputed : atomicSeparatedEvidence? source center with
  | none => simp [evidenceComputed] at computed
  | some evidence =>
      simp only [evidenceComputed] at computed
      exact ⟨evidence, atomicSeparatedEvidence?_sound source center evidence evidenceComputed,
        (CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?_eq_some_iff _ _).mp
          computed⟩

end SingleWedgeSource
end AuthoritativeChemicalInput

namespace SingleWedgePriorityDescriptorRegression

open AuthoritativeChemicalInput.SingleWedgeSource

/-- Exact priorities are computed from the semantic CFClBrI atoms, not from supplied ranks. -/
theorem cfclbri_source_priority_order :
    (atomicSeparatedEvidence? SingleWedgeSourceRegression.source
      (SingleWedgeSourceRegression.center _ (by decide))).map
        (fun evidence => evidence.tracked.highestFirst.map Fin.val) = some [3, 2, 1, 0] := by
  decide +kernel

/-- The solid-wedge CFClBrI drawing has written-order oriented volume `-3`; in descending atomic
priority order `[3, 2, 1, 0]` the volume stays negative, so the calibrated descriptor is `R`. -/
theorem cfclbri_source_solid_descriptor :
    atomicSeparatedDescriptor? SingleWedgeSourceRegression.source
      (SingleWedgeSourceRegression.center _ (by decide)) = some RS.R := by decide +kernel

/-- The hashed-wedge variant has written-order oriented volume `+3`; the descending priority order
preserves positivity, so the calibrated descriptor is `S`. -/
theorem cfclbri_source_hashed_descriptor :
    atomicSeparatedDescriptor? (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge)
      (SingleWedgeSourceRegression.center _ (by decide)) = some RS.S := by decide +kernel

theorem cfclbri_source_solid_meaning :
    AtomicSeparatedDescriptorMeaning SingleWedgeSourceRegression.source
      (SingleWedgeSourceRegression.center _ (by decide)) RS.R :=
  atomicSeparatedDescriptor?_sound _ _ _ cfclbri_source_solid_descriptor

theorem cfclbri_source_hashed_meaning :
    AtomicSeparatedDescriptorMeaning (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge)
      (SingleWedgeSourceRegression.center _ (by decide)) RS.S :=
  atomicSeparatedDescriptor?_sound _ _ _ cfclbri_source_hashed_descriptor

/-- Closed source-only outputs require neither SMILES tetrahedral annotations nor spatial data. -/
theorem cfclbri_no_spatial_channel : SingleWedgeSourceRegression.source.spatial? = none := rfl

/-- The closed descriptor and actual returned-root alignment concern the same source and
an inhabited production center. This does not assert equality with the production key sorter. -/
theorem cfclbri_source_solid_descriptor_bound_to_actual_roots (carrierFuel : Nat) :
    ∃ aligned,
      occurrenceAlignment? SingleWedgeSourceRegression.source carrierFuel
        SingleWedgeOccurrenceAlignmentRegression.cfclbriProductionCenter = some aligned ∧
      atomicSeparatedDescriptor? SingleWedgeSourceRegression.source
        (SingleWedgeSourceRegression.center _ (by decide)) = some RS.R ∧
      AtomicSeparatedDescriptorMeaning SingleWedgeSourceRegression.source
        (SingleWedgeSourceRegression.center _ (by decide)) RS.R := by
  rcases SingleWedgeOccurrenceAlignmentRegression.cfclbri_constructed_center_alignment
    carrierFuel with ⟨aligned, computed⟩
  exact ⟨aligned, computed, cfclbri_source_solid_descriptor, cfclbri_source_solid_meaning⟩

def tiedAtomicSource : AuthoritativeChemicalInput :=
  { SingleWedgeSourceRegression.source with
    molecule := { SingleWedgeSourceRegression.molecule with
      atoms := [SingleWedgeSourceRegression.carbon, SingleWedgeSourceRegression.fluorine,
        SingleWedgeSourceRegression.fluorine, SingleWedgeSourceRegression.bromine,
        SingleWedgeSourceRegression.iodine] } }

/-- Equal endpoint atomic numbers require fallthrough and are refused by this strict subdomain. -/
theorem actual_atomic_tie_refused :
    atomicSeparatedDescriptor? tiedAtomicSource ⟨0, by decide⟩ = none := by decide +kernel

theorem actual_relative_drawing_refused :
    atomicSeparatedDescriptor? (SingleWedgeSourceRegression.nonAbsoluteSource (.relative 1))
      ⟨0, by decide⟩ = none := by decide +kernel

end SingleWedgePriorityDescriptorRegression
end TetraStereo.OneCenter
