import TetraStereo.OneCenter.LocalizedExtendedDemandDiscovery
import TetraStereo.OneCenter.LocalizedExtendedShortCircuitCachedPipeline

set_option autoImplicit false





























namespace TetraStereo.OneCenter.LocalizedExtendedShortCircuit.Prepared

open CertifiedLocalizedCIPInput

/-! ## The cached child reader -/

/-- Child reader backed by the materialized occurrence carrier of a `Cached.RuntimeCache`. -/
def cachedReadChildren (input : Input) (cache : Cached.RuntimeCache input) :
    input.certified.LocalizedRerootCursor (carrierFuel input) →
      Option (List (input.certified.LocalizedRerootCursor (carrierFuel input))) :=
  fun cursor => input.certified.localizedRerootChildrenFromCarrier? cache.carrier cursor

/-- The materialized reader is extensionally the executable reroot reader. -/
theorem cachedReadChildren_eq (input : Input) (cache : Cached.RuntimeCache input) :
    ∀ cursor, cachedReadChildren input cache cursor =
      input.certified.executableLocalizedRerootChildren? cursor := by
  intro cursor
  unfold cachedReadChildren
  rw [cache.exact]
  exact input.certified.localizedRerootChildrenFromCarrier?_eq_executable cursor

/-! ## The at-budget twin of the direct extended discovery -/

/-- Budget-parameterized twin of `prepareExtendedRule3DemandPlan`.  The occurrence count and
traversal budget are supplied by the caller, so one input preparation pays for them once.  This is
the single substitution point for a replacement extended discovery. -/
def prepareExtendedRule3DemandPlanAt (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (traversalBudget : Nat) (roots : List (input.LocalizedRerootCursor fuel)) :
    Except (input.Rule3DemandDiscoveryFailure fuel) (input.ExtendedRule3DemandPlan roots) := do
  let table ← roots.foldlM (fun known root =>
    input.discoverExtendedRule3DemandRanks traversalBudget [] known root) []
  let some ranks := input.checkExtendedRule3DemandRanks? table | .error .invalidRanks
  if covers : ∀ root ∈ roots, root ∈ ranks.vertices then
    .ok { ranks, covers }
  else .error .missingRoot

/-- At the canonical occurrence-count budget the twin is the direct extended constructor,
definitionally. -/
theorem prepareExtendedRule3DemandPlanAt_eq (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel)) :
    prepareExtendedRule3DemandPlanAt input
        ((input.localizedOccurrenceCarrier fuel).length *
          ((input.localizedOccurrenceCarrier fuel).length + 1) + 1) roots =
      input.prepareExtendedRule3DemandPlan roots := by
  unfold prepareExtendedRule3DemandPlanAt CertifiedLocalizedCIPInput.prepareExtendedRule3DemandPlan
  rfl



def planForBase (input : CertifiedLocalizedCIPInput) {fuel : Nat} (traversalBudget : Nat)
    (base : input.LocalizedOccurrenceFourLigandFrame fuel) :
    Except (input.Rule3DemandDiscoveryFailure fuel)
      (input.ExtendedRule3DemandPlan base.cursors) :=
  prepareExtendedRule3DemandPlanAt input traversalBudget base.cursors

/-! ## The finite preparation table -/


structure FourLigandPlan (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  roots : List (input.LocalizedRerootCursor fuel)
  length_eq : roots.length = 4
  plan : input.ExtendedRule3DemandPlan roots


def FourLigandPlan.ofBase {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (base : input.LocalizedOccurrenceFourLigandFrame fuel)
    (plan : input.ExtendedRule3DemandPlan base.cursors) : FourLigandPlan input fuel :=
  { roots := base.cursors, length_eq := base.length_eq, plan := plan }



structure TargetPreparation (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (readChildren : input.LocalizedRerootCursor fuel →
      Option (List (input.LocalizedRerootCursor fuel))) where
  target : input.LocalizedCIPOccurrence fuel
  center? : Option input.TetrahedralCenter
  center_exact : center? = input.localizedOccurrenceDescriptorCenter? target
  base? : Option (input.LocalizedOccurrenceFourLigandFrame fuel)
  base_exact : ∀ center : input.TetrahedralCenter, center? = some center →
    base? = CertifiedLocalizedCIPInput.WithChildren.localizedNoDoubleFourLigandFrameExec?
      input readChildren target
  plan? : Option (FourLigandPlan input fuel)

  plan_sound : ∀ (base : input.LocalizedOccurrenceFourLigandFrame fuel),
    base? = some base → ∀ row : FourLigandPlan input fuel, plan? = some row →
      ∃ plan : input.ExtendedRule3DemandPlan base.cursors,
        row = FourLigandPlan.ofBase base plan

/-- One row per target, plus the shared runtime cache, built before any view is known. -/
structure Preparation (input : Input) where
  cache : Cached.RuntimeCache input
  entries : List (TargetPreparation input.certified (carrierFuel input)
    (cachedReadChildren input cache))
  complete : ∀ target : Occurrence input, ∃ entry ∈ entries, entry.target = target
  entries_length : entries.length =
    (input.certified.localizedOccurrenceCarrier (carrierFuel input)).length

/-- The base stored for a target, computed from the center decision. -/
def preparedBase? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel →
      Option (List (input.LocalizedRerootCursor fuel)))
    (target : input.LocalizedCIPOccurrence fuel) :
    Option (input.LocalizedOccurrenceFourLigandFrame fuel) :=
  match input.localizedOccurrenceDescriptorCenter? target with
  | none => none
  | some _ =>
      CertifiedLocalizedCIPInput.WithChildren.localizedNoDoubleFourLigandFrameExec?
        input readChildren target


def preparedPlan? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel →
      Option (List (input.LocalizedRerootCursor fuel)))
    (traversalBudget : Nat) (target : input.LocalizedCIPOccurrence fuel) :
    Option (FourLigandPlan input fuel) :=
  match input.localizedOccurrenceDescriptorCenter? target with
  | none => none
  | some _ =>
      match CertifiedLocalizedCIPInput.WithChildren.localizedNoDoubleFourLigandFrameExec?
          input readChildren target with
      | none => none
      | some base =>
          match planForBase input traversalBudget base with
          | .error _ => none
          | .ok plan => some (FourLigandPlan.ofBase base plan)


def prepareTarget (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel →
      Option (List (input.LocalizedRerootCursor fuel)))
    (traversalBudget : Nat) (target : input.LocalizedCIPOccurrence fuel) :
    TargetPreparation input fuel readChildren :=
  { target := target
    center? := input.localizedOccurrenceDescriptorCenter? target
    center_exact := rfl
    base? := preparedBase? input readChildren target
    base_exact := by
      intro center centerComputed
      simp only [preparedBase?, centerComputed]
    plan? := preparedPlan? input readChildren traversalBudget target
    plan_sound := by
      intro base baseComputed row rowComputed
      unfold preparedBase? at baseComputed
      unfold preparedPlan? at rowComputed
      cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
      | none => simp [centerComputed] at baseComputed
      | some center =>
          cases baseFound :
              CertifiedLocalizedCIPInput.WithChildren.localizedNoDoubleFourLigandFrameExec?
                input readChildren target with
          | none => simp [centerComputed, baseFound] at baseComputed
          | some found =>
              have same : found = base :=
                Option.some.inj (by simpa only [centerComputed, baseFound] using baseComputed)
              rw [← same] at *
              cases planFound : planForBase input traversalBudget found with
              | error failure => simp [centerComputed, baseFound, planFound] at rowComputed
              | ok plan =>
                  exact ⟨plan, (Option.some.inj
                    (by simpa only [centerComputed, baseFound, planFound]
                      using rowComputed)).symm⟩ }

/-- The row always carries the requested target. -/
theorem prepareTarget_target (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel →
      Option (List (input.LocalizedRerootCursor fuel)))
    (traversalBudget : Nat) (target : input.LocalizedCIPOccurrence fuel) :
    (prepareTarget input readChildren traversalBudget target).target = target := rfl

/-- Build every row from the already materialized carrier.  The traversal budget is a parameter, so
it is evaluated once by `prepare` rather than once per row. -/
def prepareEntries (input : Input) (cache : Cached.RuntimeCache input)
    (traversalBudget : Nat) :
    List (TargetPreparation input.certified (carrierFuel input)
      (cachedReadChildren input cache)) :=
  cache.carrier.map fun target =>
    prepareTarget input.certified (cachedReadChildren input cache) traversalBudget target



@[noinline] def prepare (input : Input) : Preparation input :=
  let cache := Cached.buildRuntimeCache input
  let occurrenceCount := cache.carrier.length
  let traversalBudget := occurrenceCount * (occurrenceCount + 1) + 1
  let entries := prepareEntries input cache traversalBudget
  { cache := cache
    entries := entries
    complete := by
      intro target
      have present : target ∈ cache.carrier := by
        rw [cache.exact]
        exact input.certified.localizedOccurrenceCarrier_complete (carrierFuel input) target
      exact ⟨prepareTarget input.certified (cachedReadChildren input cache) traversalBudget target,
        List.mem_map.mpr ⟨target, present, rfl⟩,
        prepareTarget_target input.certified (cachedReadChildren input cache) traversalBudget target⟩
    entries_length := by
      simp only [entries, prepareEntries, List.length_map, cache.exact] }

/-! ## Lookup and row projections -/

namespace Preparation

variable {input : Input}

/-- Find the row of a target. -/
def lookup? (prep : Preparation input) (target : Occurrence input) :
    Option (TargetPreparation input.certified (carrierFuel input)
      (cachedReadChildren input prep.cache)) :=
  prep.entries.find? fun entry => decide (entry.target = target)

/-- The table has a row for every carrier occurrence. -/
theorem lookup?_isSome (prep : Preparation input) (target : Occurrence input) :
    (prep.lookup? target).isSome = true := by
  obtain ⟨entry, member, same⟩ := prep.complete target
  unfold lookup?
  rw [List.find?_isSome]
  exact ⟨entry, member, by simp [same]⟩

/-- Lookup returns a row carrying the requested target. -/
theorem lookup?_eq_some (prep : Preparation input) (target : Occurrence input) :
    ∃ entry, prep.lookup? target = some entry ∧ entry.target = target := by
  have someTrue := prep.lookup?_isSome target
  cases found : prep.lookup? target with
  | none => simp [found] at someTrue
  | some entry =>
      refine ⟨entry, rfl, ?_⟩
      simp only [lookup?] at found
      have decided := List.find?_some found
      exact of_decide_eq_true (decided : decide (entry.target = target) = true)

/-- Stored descriptor center. -/
def center? (prep : Preparation input) (target : Occurrence input) :
    Option input.certified.TetrahedralCenter :=
  match prep.lookup? target with
  | some entry => entry.center?
  | none => none

/-- Stored four-ligand base. -/
def base? (prep : Preparation input) (target : Occurrence input) :
    Option (input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input)) :=
  match prep.lookup? target with
  | some entry => entry.base?
  | none => none


def plan? (prep : Preparation input) (target : Occurrence input) :
    Option (FourLigandPlan input.certified (carrierFuel input)) :=
  match prep.lookup? target with
  | some entry => entry.plan?
  | none => none

/-- The stored center is the production center computation. -/
theorem center?_eq (prep : Preparation input) (target : Occurrence input) :
    prep.center? target = input.certified.localizedOccurrenceDescriptorCenter? target := by
  obtain ⟨entry, found, same⟩ := prep.lookup?_eq_some target
  simp [center?, found, entry.center_exact, same]

/-- Under a stored center, the stored base is the production four-ligand base computation. -/
theorem base?_eq (prep : Preparation input) (target : Occurrence input)
    (center : input.certified.TetrahedralCenter)
    (centerEq : prep.center? target = some center) :
    prep.base? target =
      CertifiedLocalizedCIPInput.WithChildren.localizedNoDoubleFourLigandFrameExec?
        input.certified (cachedReadChildren input prep.cache) target := by
  obtain ⟨entry, found, same⟩ := prep.lookup?_eq_some target
  have entryCenter : entry.center? = some center := by
    simpa [center?, found] using centerEq
  have stored := entry.base_exact center entryCenter
  simpa [base?, found, same] using stored


theorem plan?_sound (prep : Preparation input) (target : Occurrence input)
    (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (baseEq : prep.base? target = some base)
    (row : FourLigandPlan input.certified (carrierFuel input))
    (rowEq : prep.plan? target = some row) :
    ∃ plan : input.certified.ExtendedRule3DemandPlan base.cursors,
      row = FourLigandPlan.ofBase base plan := by
  obtain ⟨entry, found, same⟩ := prep.lookup?_eq_some target
  have entryBase : entry.base? = some base := by
    simpa [base?, found] using baseEq
  have entryRow : entry.plan? = some row := by
    simpa [plan?, found] using rowEq
  exact entry.plan_sound base entryBase row entryRow

end Preparation

/-! ## The per-view evaluator (no discovery, no carrier enumeration) -/



def rule3FrameFrom? (input : Input) (prep : Preparation input)
    (target : Occurrence input) (view : input.certified.LocalizedDependencyView target)
    (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input)) :
    Option input.certified.LocalizedRule3CanonicalKeyFrame :=
  let productionFuel := localizedDescriptorBearingRule3EvaluationFuel (carrierFuel input)
  match prep.plan? target with
  | none =>
      CertifiedLocalizedCIPInput.WithChildren.buildLocalizedExtendedShortCircuitRule3FrameExec?
        input.certified (cachedReadChildren input prep.cache) target view productionFuel base.cursors
  | some row =>
      if row.plan.bound ≤ productionFuel then
        CertifiedLocalizedCIPInput.WithChildren.buildLocalizedExtendedShortCircuitRule3FrameExec?
          input.certified (cachedReadChildren input prep.cache) target view row.plan.bound row.roots
      else
        CertifiedLocalizedCIPInput.WithChildren.buildLocalizedExtendedShortCircuitRule3FrameExec?
          input.certified (cachedReadChildren input prep.cache) target view productionFuel base.cursors



def keyFrameFrom? (input : Input) (prep : Preparation input)
    (ready? : Option (input.certified.LocalizedExtendedRule3NoCallbackCertificate
      (carrierFuel input)))
    (target : Occurrence input) (view : input.certified.LocalizedDependencyView target)
    (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input)) :
    Option (input.certified.LocalizedOccurrenceRule3Through5KeyFrame (carrierFuel input)) :=
  match ready? with
  | some _ =>
      CertifiedLocalizedCIPInput.ExtendedBounded.keyFrame? input.certified
        (cachedReadChildren input prep.cache) target view base
  | none => do
      let rule45Fuel := localizedOccurrenceRerootEvaluationFuel (carrierFuel input)
      let rule3Frame ← rule3FrameFrom? input prep target view base
      if rule3Length : rule3Frame.keys.length = 4 then
        let rule45Keys ← base.cursors.mapM
          (CertifiedLocalizedCIPInput.WithChildren.buildLocalizedRerootCompoundRule45KeyExec?
            input.certified (cachedReadChildren input prep.cache) target view rule45Fuel)
        if rule45Length : rule45Keys.length = 4 then
          some { rule3Frame, rule3Length, rule45Keys, rule45Length }
        else none
      else none

/-- Spatial evidence assembled from the prepared center and base. -/
def spatialEvidenceFrom? (input : Input) (prep : Preparation input)
    (ready? : Option (input.certified.LocalizedExtendedRule3NoCallbackCertificate
      (carrierFuel input)))
    (target : Occurrence input) (view : input.certified.LocalizedDependencyView target)
    (center : input.certified.TetrahedralCenter)
    (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input)) :
    Option (input.certified.LocalizedOccurrenceRule3Through5SpatialEvidence
      (carrierFuel input)) := do
  let keys ← keyFrameFrom? input prep ready? target view base
  let tracked ← input.certified.localizedNoDoubleTrackedOrderExec? keys
  let points ← tracked.highestFirst.mapM fun index =>
    input.certified.localizedRerootCursorSpatialPoint? (base.cursorAt index)
  some { center, base, keys, tracked, points }

/-- Descriptor from prepared evidence. -/
def descriptorFrom? (input : Input) (prep : Preparation input)
    (ready? : Option (input.certified.LocalizedExtendedRule3NoCallbackCertificate
      (carrierFuel input)))
    (target : Occurrence input) (view : input.certified.LocalizedDependencyView target)
    (center : input.certified.TetrahedralCenter)
    (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input)) :
    Option LocalizedAuxiliaryLabel := do
  let evidence ← spatialEvidenceFrom? input prep ready? target view center base
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

/-- The two production branches: callback-free linear Rule3, or the automatic extended path. -/
def selectedDescriptor? (input : Input) (prep : Preparation input)
    (ready? : Option (input.certified.LocalizedExtendedRule3NoCallbackCertificate
      (carrierFuel input)))
    (target : Occurrence input) (view : input.certified.LocalizedDependencyView target)
    (center : input.certified.TetrahedralCenter)
    (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input)) :
    Option LocalizedAuxiliaryLabel :=
  match ready? with
  | some _ => descriptorFrom? input prep ready? target view center base
  | none => descriptorFrom? input prep none target view center base

/-- Certified terminal-tie refusal runs before any descriptor or demand work, exactly as in
`ExtendedTerminalTie.descriptor?`; only the center and base are table lookups. -/
def descriptorWithTerminalTie? (input : Input) (prep : Preparation input)
    (ready? : Option (input.certified.LocalizedExtendedRule3NoCallbackCertificate
      (carrierFuel input)))
    (target : Occurrence input) (view : input.certified.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel :=
  match prep.center? target with
  | none => none
  | some center =>
      match prep.base? target with
      | none => none
      | some base =>
          match ExtendedTerminalTie.refusalCertificate? input.certified
              (cachedReadChildren input prep.cache) target view base with
          | some _ => none
          | none => selectedDescriptor? input prep ready? target view center base

/-! ## Equality with the extended production descriptor -/




theorem rule3FrameFrom?_eq_production (input : Input) (prep : Preparation input)
    (target : Occurrence input) (view : input.certified.LocalizedDependencyView target)
    (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (baseEq : prep.base? target = some base) :
    rule3FrameFrom? input prep target view base =
      CertifiedLocalizedCIPInput.WithChildren.buildLocalizedExtendedShortCircuitRule3FrameExec?
        input.certified (cachedReadChildren input prep.cache) target view
        (localizedDescriptorBearingRule3EvaluationFuel (carrierFuel input)) base.cursors := by
  unfold rule3FrameFrom?
  cases planFound : prep.plan? target with
  | none => rfl
  | some row =>
      obtain ⟨plan, rowEq⟩ := Preparation.plan?_sound prep target base baseEq row planFound
      subst row
      simp only [FourLigandPlan.ofBase] at *
      by_cases enough : plan.bound ≤
          localizedDescriptorBearingRule3EvaluationFuel (carrierFuel input)
      · simp only [if_pos enough]
        calc
          CertifiedLocalizedCIPInput.WithChildren.buildLocalizedExtendedShortCircuitRule3FrameExec?
              input.certified (cachedReadChildren input prep.cache) target view plan.bound
              base.cursors
            = input.certified.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
                plan.bound base.cursors :=
              (CertifiedLocalizedCIPInput.WithChildren.extendedShortCircuitRule3_mutual_eq_original
                input.certified (cachedReadChildren input prep.cache)
                (cachedReadChildren_eq input prep.cache) target view plan.bound).2 base.cursors
          _ = input.certified.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
                (localizedDescriptorBearingRule3EvaluationFuel (carrierFuel input))
                base.cursors :=
              plan.ranks.frame_stable target view base.cursors plan.covers
                plan.bound
                (localizedDescriptorBearingRule3EvaluationFuel (carrierFuel input))
                (Nat.le_refl _) enough
          _ = CertifiedLocalizedCIPInput.WithChildren.buildLocalizedExtendedShortCircuitRule3FrameExec?
                input.certified (cachedReadChildren input prep.cache) target view
                (localizedDescriptorBearingRule3EvaluationFuel (carrierFuel input))
                base.cursors :=
              ((CertifiedLocalizedCIPInput.WithChildren.extendedShortCircuitRule3_mutual_eq_original
                input.certified (cachedReadChildren input prep.cache)
                (cachedReadChildren_eq input prep.cache) target view
                (localizedDescriptorBearingRule3EvaluationFuel (carrierFuel input))).2
                base.cursors).symm
      · simp only [if_neg enough]

/-- Ready branch: the prepared key frame is the existing linear `ExtendedBounded.keyFrame?`. -/
theorem keyFrameFrom?_eq_extendedBounded (input : Input) (prep : Preparation input)
    (ready : input.certified.LocalizedExtendedRule3NoCallbackCertificate (carrierFuel input))
    (target : Occurrence input) (view : input.certified.LocalizedDependencyView target)
    (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input)) :
    keyFrameFrom? input prep (some ready) target view base =
      CertifiedLocalizedCIPInput.ExtendedBounded.keyFrame? input.certified
        (cachedReadChildren input prep.cache) target view base := by
  unfold keyFrameFrom?
  rfl

/-- No-readiness branch: the prepared key frame is the `WithChildren` automatic producer. -/
theorem keyFrameFrom?_eq_withChildren (input : Input) (prep : Preparation input)
    (target : Occurrence input) (view : input.certified.LocalizedDependencyView target)
    (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (baseEq : prep.base? target = some base) :
    keyFrameFrom? input prep none target view base =
      CertifiedLocalizedCIPInput.WithChildren.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
        input.certified (cachedReadChildren input prep.cache) target view base := by
  unfold keyFrameFrom?
    CertifiedLocalizedCIPInput.WithChildren.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
  rw [rule3FrameFrom?_eq_production input prep target view base baseEq]

/-- Ready branch spatial evidence. -/
theorem spatialEvidenceFrom?_eq_extendedBounded (input : Input) (prep : Preparation input)
    (ready : input.certified.LocalizedExtendedRule3NoCallbackCertificate (carrierFuel input))
    (target : Occurrence input) (view : input.certified.LocalizedDependencyView target)
    (center : input.certified.TetrahedralCenter)
    (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (centerEq : prep.center? target = some center)
    (baseEq : prep.base? target = some base) :
    spatialEvidenceFrom? input prep (some ready) target view center base =
      CertifiedLocalizedCIPInput.ExtendedBounded.spatialEvidence? input.certified
        (cachedReadChildren input prep.cache) target view := by
  unfold spatialEvidenceFrom? CertifiedLocalizedCIPInput.ExtendedBounded.spatialEvidence?
  have productionCenter :
      input.certified.localizedOccurrenceDescriptorCenter? target = some center :=
    (Preparation.center?_eq prep target).symm.trans centerEq
  have productionBase :
      CertifiedLocalizedCIPInput.WithChildren.localizedNoDoubleFourLigandFrameExec?
        input.certified (cachedReadChildren input prep.cache) target = some base :=
    (Preparation.base?_eq prep target center centerEq).symm.trans baseEq
  rw [productionCenter, productionBase]
  rw [keyFrameFrom?_eq_extendedBounded input prep ready target view base]
  rfl

/-- No-readiness branch spatial evidence. -/
theorem spatialEvidenceFrom?_eq_withChildren (input : Input) (prep : Preparation input)
    (target : Occurrence input) (view : input.certified.LocalizedDependencyView target)
    (center : input.certified.TetrahedralCenter)
    (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (centerEq : prep.center? target = some center)
    (baseEq : prep.base? target = some base) :
    spatialEvidenceFrom? input prep none target view center base =
      CertifiedLocalizedCIPInput.WithChildren.localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
        input.certified (cachedReadChildren input prep.cache) target view := by
  unfold spatialEvidenceFrom?
    CertifiedLocalizedCIPInput.WithChildren.localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
  have productionCenter :
      input.certified.localizedOccurrenceDescriptorCenter? target = some center :=
    (Preparation.center?_eq prep target).symm.trans centerEq
  have productionBase :
      CertifiedLocalizedCIPInput.WithChildren.localizedNoDoubleFourLigandFrameExec?
        input.certified (cachedReadChildren input prep.cache) target = some base :=
    (Preparation.base?_eq prep target center centerEq).symm.trans baseEq
  rw [productionCenter, productionBase]
  rw [keyFrameFrom?_eq_withChildren input prep target view base baseEq]
  rfl

/-- Ready branch descriptor. -/
theorem descriptorFrom?_eq_extendedBounded (input : Input) (prep : Preparation input)
    (ready : input.certified.LocalizedExtendedRule3NoCallbackCertificate (carrierFuel input))
    (target : Occurrence input) (view : input.certified.LocalizedDependencyView target)
    (center : input.certified.TetrahedralCenter)
    (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (centerEq : prep.center? target = some center)
    (baseEq : prep.base? target = some base) :
    descriptorFrom? input prep (some ready) target view center base =
      CertifiedLocalizedCIPInput.ExtendedBounded.descriptor? input.certified
        (cachedReadChildren input prep.cache) target view := by
  unfold descriptorFrom? CertifiedLocalizedCIPInput.ExtendedBounded.descriptor?
  rw [spatialEvidenceFrom?_eq_extendedBounded input prep ready target view center base centerEq baseEq]

/-- No-readiness branch descriptor. -/
theorem descriptorFrom?_eq_withChildren (input : Input) (prep : Preparation input)
    (target : Occurrence input) (view : input.certified.LocalizedDependencyView target)
    (center : input.certified.TetrahedralCenter)
    (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (centerEq : prep.center? target = some center)
    (baseEq : prep.base? target = some base) :
    descriptorFrom? input prep none target view center base =
      CertifiedLocalizedCIPInput.WithChildren.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
        input.certified (cachedReadChildren input prep.cache) target view := by
  unfold descriptorFrom?
    CertifiedLocalizedCIPInput.WithChildren.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
  rw [spatialEvidenceFrom?_eq_withChildren input prep target view center base centerEq baseEq]

/-- The selected descriptor equals the executable extended production descriptor. -/
theorem selectedDescriptor?_eq_production (input : Input) (prep : Preparation input)
    (ready? : Option (input.certified.LocalizedExtendedRule3NoCallbackCertificate
      (carrierFuel input)))
    (target : Occurrence input) (view : input.certified.LocalizedDependencyView target)
    (center : input.certified.TetrahedralCenter)
    (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (centerEq : prep.center? target = some center)
    (baseEq : prep.base? target = some base) :
    selectedDescriptor? input prep ready? target view center base =
      input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
        target view := by
  cases ready? with
  | none =>
      simp only [selectedDescriptor?]
      exact (descriptorFrom?_eq_withChildren input prep target view center base centerEq baseEq).trans
        (CertifiedLocalizedCIPInput.WithChildren.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_original
          input.certified (cachedReadChildren input prep.cache)
          (cachedReadChildren_eq input prep.cache) target view)
  | some ready =>
      simp only [selectedDescriptor?]
      exact (descriptorFrom?_eq_extendedBounded input prep ready target view center base
          centerEq baseEq).trans
        (CertifiedLocalizedCIPInput.ExtendedBounded.descriptor?_eq_production input.certified
          (cachedReadChildren input prep.cache) (cachedReadChildren_eq input prep.cache)
          ready target view)

/-- The prepared early-tie evaluator is the existing tie evaluator at the cached reader. -/
theorem descriptorWithTerminalTie?_eq_extendedTerminalTie (input : Input) (prep : Preparation input)
    (ready? : Option (input.certified.LocalizedExtendedRule3NoCallbackCertificate
      (carrierFuel input)))
    (target : Occurrence input) (view : input.certified.LocalizedDependencyView target) :
    descriptorWithTerminalTie? input prep ready? target view =
      ExtendedTerminalTie.descriptor? input.certified
        (cachedReadChildren input prep.cache) target view := by
  unfold descriptorWithTerminalTie? ExtendedTerminalTie.descriptor?
  rw [Preparation.center?_eq prep target]
  cases centerComputed : input.certified.localizedOccurrenceDescriptorCenter? target with
  | none => rfl
  | some center =>
      have centerEq : prep.center? target = some center :=
        (Preparation.center?_eq prep target).trans centerComputed
      have baseEqAll : prep.base? target =
          CertifiedLocalizedCIPInput.WithChildren.localizedNoDoubleFourLigandFrameExec?
            input.certified (cachedReadChildren input prep.cache) target :=
        Preparation.base?_eq prep target center centerEq
      cases baseComputed :
          CertifiedLocalizedCIPInput.WithChildren.localizedNoDoubleFourLigandFrameExec?
            input.certified (cachedReadChildren input prep.cache) target with
      | none =>
          rw [baseEqAll, baseComputed]
      | some base =>
          have baseEq : prep.base? target = some base := baseEqAll.trans baseComputed
          have unchanged :
              selectedDescriptor? input prep ready? target view center base =
                CertifiedLocalizedCIPInput.WithChildren.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
                  input.certified (cachedReadChildren input prep.cache) target view :=
            (selectedDescriptor?_eq_production input prep ready? target view center base
                centerEq baseEq).trans
              (CertifiedLocalizedCIPInput.WithChildren.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_original
                input.certified (cachedReadChildren input prep.cache)
                (cachedReadChildren_eq input prep.cache) target view).symm
          rw [baseEqAll, baseComputed]
          dsimp only
          cases refusalComputed :
              ExtendedTerminalTie.refusalCertificate? input.certified
                (cachedReadChildren input prep.cache) target view base
          · rw [unchanged]
          · rfl

/-- Full optional equality for every target and every dependency view: the prepared evaluator never
changes an outcome, including every refusal branch. -/
theorem descriptorWithTerminalTie?_eq_production (input : Input) (prep : Preparation input)
    (ready? : Option (input.certified.LocalizedExtendedRule3NoCallbackCertificate
      (carrierFuel input)))
    (target : Occurrence input) (view : input.certified.LocalizedDependencyView target) :
    descriptorWithTerminalTie? input prep ready? target view =
      input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
        target view := by
  exact (descriptorWithTerminalTie?_eq_extendedTerminalTie input prep ready? target view).trans
    ((ExtendedTerminalTie.descriptor?_eq_original input.certified
        (cachedReadChildren input prep.cache) target view).trans
      (CertifiedLocalizedCIPInput.WithChildren.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_original
        input.certified (cachedReadChildren input prep.cache)
        (cachedReadChildren_eq input prep.cache) target view))



theorem prepared_universal_semantics (input : Input) :
    let prep := prepare input
    ∀ (target : Occurrence input) (view : input.certified.LocalizedDependencyView target),
      descriptorWithTerminalTie? input prep prep.cache.ready? target view =
        input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
          target view := by
  dsimp only
  intro target view
  exact descriptorWithTerminalTie?_eq_production input (prepare input)
    (prepare input).cache.ready? target view





theorem Preparation.checked_plan_coverage {input : Input} (prep : Preparation input)
    (target : Occurrence input)
    (base : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (row : FourLigandPlan input.certified (carrierFuel input))
    (baseEq : prep.base? target = some base)
    (rowEq : prep.plan? target = some row) :
    ∃ plan : input.certified.ExtendedRule3DemandPlan base.cursors,
      row = FourLigandPlan.ofBase base plan ∧
      (∀ cursor ∈ plan.ranks.vertices, 0 < plan.ranks.height cursor) ∧
      (∀ cursor ∈ plan.ranks.vertices,
        ∀ child ∈ input.certified.executableLocalizedRerootChildren cursor,
          child ∈ plan.ranks.vertices ∧
            plan.ranks.height child + 1 ≤ plan.ranks.height cursor) ∧
      (∀ cursor ∈ plan.ranks.vertices,
        ∀ request ∈ input.certified.rule3ExtendedNodeCallbackRequests cursor.occurrence,
          (∀ reference ∈ request, reference ∈ plan.ranks.vertices) ∧
            rule3CursorListHeight plan.ranks.height request + 2 ≤ plan.ranks.height cursor) ∧
      (∀ root ∈ base.cursors, root ∈ plan.ranks.vertices) := by
  obtain ⟨plan, same⟩ := Preparation.plan?_sound prep target base baseEq row rowEq
  exact ⟨plan, same, plan.ranks.positive, plan.ranks.children, plan.ranks.callbacks, plan.covers⟩

/-! ## Evaluator integration -/

/-- Restricted evaluator backed by one preparation pass. -/
def evaluatorUsingPreparation (input : Input) (prep : Preparation input) :
    input.certified.LocalizedRestrictedEvaluator (carrierFuel input) :=
  descriptorWithTerminalTie? input prep prep.cache.ready?

/-- The prepared evaluator is the production extended evaluator, for every state. -/
theorem evaluatorUsingPreparation_eq (input : Input) (prep : Preparation input) :
    evaluatorUsingPreparation input prep = evaluator input (carrierFuel input) := by
  funext target view
  exact descriptorWithTerminalTie?_eq_production input prep prep.cache.ready? target view

end TetraStereo.OneCenter.LocalizedExtendedShortCircuit.Prepared
