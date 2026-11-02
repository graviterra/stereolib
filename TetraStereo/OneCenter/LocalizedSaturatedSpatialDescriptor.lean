import TetraStereo.OneCenter.LocalizedSaturatedRule45Pipeline

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

namespace CertifiedLocalizedCIPInput

/-!
# Exact saturated localized `R/S` and `r/s` assignment

The tracked stable sort supplies the comparison history needed for case, but geometry is accepted
only after the resulting order is checked against every earlier/later ligand pair.  This rejects a
decisive cyclic tournament.  The four exact semantic coordinates then determine the raw sense by
the rational affine determinant, and the tracked `±2` count determines uppercase versus lowercase.
-/

/-- Strict pair check for the saturated molecular comparator. -/
def saturatedOrderPairStrictAt? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4) : Bool :=
  match input.compareLocalizedSaturatedThroughRule5At? center left right with
  | none => false
  | some comparison => comparison.ordering == Ordering.gt

/-- Check every earlier/later pair in the proposed descriptor-facing order. -/
def saturatedOrderCoherentListAt? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) : List (Fin 4) → Bool
  | [] => true
  | left :: rest =>
      rest.all (input.saturatedOrderPairStrictAt? center left) &&
        input.saturatedOrderCoherentListAt? center rest

@[simp] theorem saturatedOrderPairStrictAt?_eq_true_iff
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4) :
    input.saturatedOrderPairStrictAt? center left right = true ↔
      ∃ comparison,
        input.compareLocalizedSaturatedThroughRule5At? center left right =
          some comparison ∧ comparison.ordering = Ordering.gt := by
  cases computed : input.compareLocalizedSaturatedThroughRule5At? center left right with
  | none => simp [saturatedOrderPairStrictAt?, computed]
  | some comparison => simp [saturatedOrderPairStrictAt?, computed]

theorem saturatedOrderCoherentListAt?_eq_true_iff
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) : ∀ order,
    input.saturatedOrderCoherentListAt? center order = true ↔
      order.Pairwise fun left right =>
        ∃ comparison,
          input.compareLocalizedSaturatedThroughRule5At? center left right =
            some comparison ∧ comparison.ordering = Ordering.gt
  | [] => by simp [saturatedOrderCoherentListAt?]
  | left :: rest => by
      rw [saturatedOrderCoherentListAt?, Bool.and_eq_true, List.all_eq_true,
        List.pairwise_cons, saturatedOrderCoherentListAt?_eq_true_iff]
      constructor
      · rintro ⟨head, tail⟩
        exact ⟨fun right present =>
          (input.saturatedOrderPairStrictAt?_eq_true_iff
            center left right).mp (head right present), tail⟩
      · rintro ⟨head, tail⟩
        exact ⟨fun right present =>
          (input.saturatedOrderPairStrictAt?_eq_true_iff
            center left right).mpr (head right present), tail⟩

/-- Stable tracked order accepted only when every earlier/later pair is strictly coherent. -/
def safeSaturatedTrackedLigandOrderAt?
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) : Option TrackedLocalizedLigandOrder := do
  let tracked ← input.saturatedTrackedLigandOrderAt? center
  if input.saturatedOrderCoherentListAt? center tracked.highestFirst then
    some tracked
  else none

/-- Independent safe-order relation, including exact sort history, permutation, and an
independent molecule-derived strict comparison for every earlier/later pair. -/
def DeclarativeSafeSaturatedTrackedLigandOrderAt
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (tracked : TrackedLocalizedLigandOrder) : Prop :=
  input.DeclarativeSaturatedTrackedLigandSort center
      (List.finRange 4) [] 0 tracked ∧
    tracked.highestFirst.Perm (List.finRange 4) ∧
    tracked.highestFirst.Pairwise fun left right =>
      ∃ comparison,
        input.DeclarativeLocalizedSaturatedThroughRule5At
          center left right comparison ∧
        comparison.ordering = Ordering.gt

theorem safeSaturatedTrackedLigandOrderAt?_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (tracked : TrackedLocalizedLigandOrder)
    (computed : input.safeSaturatedTrackedLigandOrderAt? center = some tracked) :
    input.DeclarativeSafeSaturatedTrackedLigandOrderAt center tracked := by
  unfold safeSaturatedTrackedLigandOrderAt? at computed
  cases trackedComputed : input.saturatedTrackedLigandOrderAt? center with
  | none => simp [trackedComputed] at computed
  | some observed =>
      cases coherent : input.saturatedOrderCoherentListAt?
          center observed.highestFirst with
      | false => simp [trackedComputed, coherent] at computed
      | true =>
          simp [trackedComputed, coherent] at computed
          subst tracked
          refine ⟨input.saturatedTrackedLigandOrderAt?_sound
              center observed trackedComputed,
            sortFourLocalizedLigandsTracked_perm
              (input.compareLocalizedSaturatedThroughRule5At? center)
              observed trackedComputed, ?_⟩
          exact ((input.saturatedOrderCoherentListAt?_eq_true_iff
            center observed.highestFirst).mp coherent).imp (by
              rintro left right ⟨comparison, compared, higher⟩
              exact ⟨comparison,
                input.compareLocalizedSaturatedThroughRule5At?_sound
                  center left right comparison compared,
                higher⟩)

/-- Safe tracked priority order paired with its exact semantic points. -/
structure SaturatedTrackedSpatialEvidence where
  tracked : TrackedLocalizedLigandOrder
  points : List CartesianPoint3

/-- Look up exact coordinates in the safe saturated priority order. -/
def saturatedTrackedSpatialEvidenceAt?
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) : Option SaturatedTrackedSpatialEvidence := do
  let tracked ← input.safeSaturatedTrackedLigandOrderAt? center
  let points ← tracked.highestFirst.mapM fun index =>
    input.spatialPointAt? (input.canonicalLigandAtom center index)
  some { tracked := tracked, points := points }

private theorem mapM_spatial_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) :
    ∀ order points,
      order.mapM (fun index =>
        input.spatialPointAt? (input.canonicalLigandAtom center index)) = some points →
      input.DeclarativePrioritySpatialPoints center order points
  | [], points, computed => by
      simp at computed
      subst points
      exact List.Forall₂.nil
  | index :: order, points, computed => by
      rw [List.mapM_cons] at computed
      cases pointComputed : input.spatialPointAt?
          (input.canonicalLigandAtom center index) with
      | none => simp [pointComputed] at computed
      | some point =>
          cases tailComputed : order.mapM (fun next =>
              input.spatialPointAt? (input.canonicalLigandAtom center next)) with
          | none => simp [pointComputed, tailComputed] at computed
          | some tail =>
              simp [pointComputed, tailComputed] at computed
              subst points
              exact List.Forall₂.cons
                ((input.spatialPointAt?_eq_some_iff
                  (input.canonicalLigandAtom center index) point).mp pointComputed)
                (mapM_spatial_sound input center order tail tailComputed)

/-- Independent spatial-evidence relation. -/
def DeclarativeSaturatedTrackedSpatialEvidenceAt
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (evidence : SaturatedTrackedSpatialEvidence) : Prop :=
  input.DeclarativeSafeSaturatedTrackedLigandOrderAt center evidence.tracked ∧
    input.DeclarativePrioritySpatialPoints center
      evidence.tracked.highestFirst evidence.points

theorem saturatedTrackedSpatialEvidenceAt?_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (evidence : SaturatedTrackedSpatialEvidence)
    (computed : input.saturatedTrackedSpatialEvidenceAt? center = some evidence) :
    input.DeclarativeSaturatedTrackedSpatialEvidenceAt center evidence := by
  unfold saturatedTrackedSpatialEvidenceAt? at computed
  cases trackedComputed : input.safeSaturatedTrackedLigandOrderAt? center with
  | none => simp [trackedComputed] at computed
  | some tracked =>
      cases pointsComputed : tracked.highestFirst.mapM fun index =>
          input.spatialPointAt? (input.canonicalLigandAtom center index) with
      | none => simp [trackedComputed, pointsComputed] at computed
      | some points =>
          simp [trackedComputed, pointsComputed] at computed
          subst evidence
          exact ⟨input.safeSaturatedTrackedLigandOrderAt?_sound
              center tracked trackedComputed,
            mapM_spatial_sound input center tracked.highestFirst points pointsComputed⟩

/-- Case-bearing saturated localized tetrahedral descriptor. -/
def saturatedTetrahedralRSPseudoDescriptorAt?
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) :
    Option LocalizedTetrahedralRSPseudoDescriptor := do
  let evidence ← input.saturatedTrackedSpatialEvidenceAt? center
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

/-- Independent end-to-end relation for the saturated uppercase-seed subdomain. -/
def DeclarativeSaturatedTetrahedralRSPseudoDescriptorAt
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) : Prop :=
  ∃ evidence raw,
    input.DeclarativeSaturatedTrackedSpatialEvidenceAt center evidence ∧
    RationalTetrahedralDescriptor evidence.points raw ∧
    descriptor = classifyTetrahedralRSPseudo
      raw evidence.tracked.pseudoComparisons

theorem saturatedTetrahedralRSPseudoDescriptorAt?_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor)
    (computed : input.saturatedTetrahedralRSPseudoDescriptorAt? center =
      some descriptor) :
    input.DeclarativeSaturatedTetrahedralRSPseudoDescriptorAt center descriptor := by
  unfold saturatedTetrahedralRSPseudoDescriptorAt? at computed
  cases evidenceComputed : input.saturatedTrackedSpatialEvidenceAt? center with
  | none => simp [evidenceComputed] at computed
  | some evidence =>
      cases rawComputed : descriptorOfPriorityOrderedPoints? evidence.points with
      | none => simp [evidenceComputed, rawComputed] at computed
      | some raw =>
          simp [evidenceComputed, rawComputed] at computed
          subst descriptor
          exact ⟨evidence, raw,
            input.saturatedTrackedSpatialEvidenceAt?_sound
              center evidence evidenceComputed,
            (descriptorOfPriorityOrderedPoints?_eq_some_iff
              evidence.points raw).mp rawComputed,
            rfl⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
