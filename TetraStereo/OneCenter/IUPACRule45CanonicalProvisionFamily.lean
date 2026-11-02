import TetraStereo.OneCenter.IUPACRule45CanonicalPartitionCompleteness
import TetraStereo.OneCenter.IUPACNormativeManifest
import TetraStereo.OneCenter.IUPACProvisionSemantics
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Canonical Rules 4b/5 provision family

The complete Rules-4b--5 comparator is one lexicographic mathematical object.  This module
retains its four stage outcomes as a typed, source-independent trace, proves that evaluating the
trace is exactly the production comparator, and transports the trace through the builder-free
canonical partition theorem.  The three manifest provisions for Rule 4b pairing, Rule 4b
like/unlike comparison, and Rule 5 are then activated projections of that single trace judgment.

This is the molecular execution layer, not a replacement for the audited primitive Blue Book
operation graphs.  Rebinding these three rows in the global corpus requires a separate theorem
showing that each activated composite-stage projection instantiates its existing primitive
reference relation.
-/

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

namespace AuthoritativeChemicalInput

private theorem orderingThen_four_assoc (a b c d : Ordering) :
    a.then (b.then (c.then d)) = (a.then (b.then c)).then d := by
  cases a <;> cases b <;> cases c <;> rfl

/-- The four semantically distinct decisions made by the compound Rules-4b--5 comparator. -/
structure Rule45CanonicalComparisonTrace where
  leftRule4bReferences : List RS
  rightRule4bReferences : List RS
  rule4bReferenceCount : Ordering
  rule4bLikeUnlike : Ordering
  rule4c : Ordering
  rule5CommonR : Ordering
  rule5CommonS : Ordering
  deriving DecidableEq, Repr

namespace Rule45CanonicalComparisonTrace

/-- Lexicographic meaning of the trace: the first decisive official stage wins. -/
def outcome (trace : Rule45CanonicalComparisonTrace) : Ordering :=
  compareLex (fun _ _ => trace.rule4bReferenceCount)
    (compareLex (fun _ _ => trace.rule4bLikeUnlike)
      (compareLex (fun _ _ => trace.rule4c) (fun _ _ => trace.rule5CommonR))) () ()

/-- Full Rule-5 result.  The common-S reading is retained because disagreement with common R is
the pseudoasymmetric/enantiomorphic signal; projecting only common R would lose P-92.6 data. -/
def rule5Result (trace : Rule45CanonicalComparisonTrace) : ConstitutionalRule5Comparison :=
  match trace.rule5CommonR with
  | .lt => { ordering := .lt, pseudo := trace.rule5CommonS != .lt }
  | .gt => { ordering := .gt, pseudo := trace.rule5CommonS != .gt }
  | .eq => { ordering := .eq, pseudo := false }

end Rule45CanonicalComparisonTrace

/-- Retain every official stage of the actual compound Rules-4b--5 key comparison. -/
def rule45CanonicalComparisonTrace
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key) :
    Rule45CanonicalComparisonTrace where
  leftRule4bReferences := left.prior.references
  rightRule4bReferences := right.prior.references
  rule4bReferenceCount :=
    compare left.prior.referenceCountPriority right.prior.referenceCountPriority
  rule4bLikeUnlike := source.compareAromaticCanonicalRerootCompoundRule4bReadings
    left.prior.readings right.prior.readings
  rule4c := source.compareAromaticCanonicalRerootCompoundRule4cReadings
    left.prior.readings right.prior.readings
  rule5CommonR := source.compareAromaticCanonicalRerootCompoundRule5Readings .R
    left.rule5Readings right.rule5Readings
  rule5CommonS := source.compareAromaticCanonicalRerootCompoundRule5Readings .S
    left.rule5Readings right.rule5Readings

/-- Independent fieldwise meaning of a canonical Rules-4b--5 trace.  Unlike the production
constructor, this relation does not mention `rule45CanonicalComparisonTrace`. -/
def Rule45CanonicalComparisonTraceJudgment
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key)
    (trace : Rule45CanonicalComparisonTrace) : Prop :=
  trace.leftRule4bReferences = left.prior.references ∧
    trace.rightRule4bReferences = right.prior.references ∧
    trace.rule4bReferenceCount =
      compare left.prior.referenceCountPriority right.prior.referenceCountPriority ∧
    trace.rule4bLikeUnlike =
      source.compareAromaticCanonicalRerootCompoundRule4bReadings
        left.prior.readings right.prior.readings ∧
    trace.rule4c = source.compareAromaticCanonicalRerootCompoundRule4cReadings
      left.prior.readings right.prior.readings ∧
    trace.rule5CommonR = source.compareAromaticCanonicalRerootCompoundRule5Readings .R
      left.rule5Readings right.rule5Readings ∧
    trace.rule5CommonS = source.compareAromaticCanonicalRerootCompoundRule5Readings .S
      left.rule5Readings right.rule5Readings

theorem rule45CanonicalComparisonTrace_eq_iff_judgment
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key)
    (trace : Rule45CanonicalComparisonTrace) :
    source.rule45CanonicalComparisonTrace left right = trace ↔
      source.Rule45CanonicalComparisonTraceJudgment left right trace := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨leftReferences, rightReferences, count, pair, rule4c, rule5R, rule5S⟩
    cases trace
    simp_all [rule45CanonicalComparisonTrace]

/-- The trace is not auxiliary logging: its lexicographic meaning is definitionally the complete
production comparison through Rule 5. -/
theorem rule45CanonicalComparisonTrace_outcome
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key) :
    (source.rule45CanonicalComparisonTrace left right).outcome =
      source.compareAromaticCanonicalRerootCompoundRule45Keys left right := by
  simpa [Rule45CanonicalComparisonTrace.outcome, rule45CanonicalComparisonTrace,
    compareAromaticCanonicalRerootCompoundRule45Keys,
    compareAromaticCanonicalRerootCompoundRule4bcKeys, compareLex, Ordering.byKey] using
    orderingThen_four_assoc
      (compare left.prior.referenceCountPriority right.prior.referenceCountPriority)
      (source.compareAromaticCanonicalRerootCompoundRule4bReadings
        left.prior.readings right.prior.readings)
      (source.compareAromaticCanonicalRerootCompoundRule4cReadings
        left.prior.readings right.prior.readings)
      (source.compareAromaticCanonicalRerootCompoundRule5Readings .R
        left.rule5Readings right.rule5Readings)

/-- When the earlier Rule-3 key ties, the retained Rules-4b--5 trace is exactly the comparator
used by the complete Rules-1a--5 canonical partition. -/
theorem rule45CanonicalComparisonTrace_outcome_eq_rule3Through5_of_rule3Tie
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalOccurrenceRule3Through5Key)
    (rule3Tie : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      left.rule3 right.rule3 = Ordering.eq) :
    (source.rule45CanonicalComparisonTrace left.rule45 right.rule45).outcome =
      source.compareAromaticCanonicalOccurrenceRule3Through5Keys left right := by
  rw [source.rule45CanonicalComparisonTrace_outcome]
  simp [compareAromaticCanonicalOccurrenceRule3Through5Keys, compareLex, Ordering.byKey,
    rule3Tie]

end AuthoritativeChemicalInput

namespace IUPACNormativeProvision

open AuthoritativeChemicalInput

/-- Exactly the three manifest rows represented by the canonical Rules-4b/5 execution trace. -/
inductive Rule45CanonicalProvisionFamily where
  | rule4bPairingMethodology
  | rule4bLikeUnlike
  | rule5Enantiomorph
  deriving DecidableEq, Repr, Fintype

namespace Rule45CanonicalProvisionFamily

def all : List Rule45CanonicalProvisionFamily :=
  [ .rule4bLikeUnlike, .rule4bPairingMethodology, .rule5Enantiomorph ]

def provision : Rule45CanonicalProvisionFamily → IUPACNormativeProvision
  | .rule4bPairingMethodology => .p92Rule4bPairingMethodology
  | .rule4bLikeUnlike => .p92Rule4bLikeUnlike
  | .rule5Enantiomorph => .p92Rule5Enantiomorph

/-- Result type retained by each provision.  Rule 5 carries the full ordering-plus-pseudo signal. -/
def Result : Rule45CanonicalProvisionFamily → Type
  | .rule4bPairingMethodology => Ordering
  | .rule4bLikeUnlike => Ordering
  | .rule5Enantiomorph => ConstitutionalRule5Comparison

/-- Each provision reads exactly one typed projection of the common canonical trace. -/
def project : (family : Rule45CanonicalProvisionFamily) →
    Rule45CanonicalComparisonTrace → family.Result
  | .rule4bPairingMethodology, trace => trace.rule4bReferenceCount
  | .rule4bLikeUnlike, trace => trace.rule4bLikeUnlike
  | .rule5Enantiomorph, trace => trace.rule5Result

def projectedOrdering : Rule45CanonicalProvisionFamily →
    Rule45CanonicalComparisonTrace → Ordering
  | .rule4bPairingMethodology, trace => trace.rule4bReferenceCount
  | .rule4bLikeUnlike, trace => trace.rule4bLikeUnlike
  | .rule5Enantiomorph, trace => trace.rule5Result.ordering

/-- Internal reach condition after Rule 3 has tied.  The outer Rule-3 tie and distinct-position
conditions are carried by the trace judgment itself. -/
def Active : Rule45CanonicalProvisionFamily →
    Rule45CanonicalComparisonTrace → Prop
  | .rule4bPairingMethodology, trace =>
      trace.leftRule4bReferences ≠ [] ∧ trace.rightRule4bReferences ≠ []
  | .rule4bLikeUnlike, trace =>
      trace.leftRule4bReferences ≠ [] ∧ trace.rightRule4bReferences ≠ [] ∧
        trace.rule4bReferenceCount = Ordering.eq
  | .rule5Enantiomorph, trace =>
      trace.rule4bReferenceCount = Ordering.eq ∧
        trace.rule4bLikeUnlike = Ordering.eq ∧ trace.rule4c = Ordering.eq

/-- Whenever an activated Rule-4b/5 stage is decisive, its projection is the result of the whole
through-Rule-5 comparator. -/
theorem outcome_eq_project_of_active_of_decisive
    (family : Rule45CanonicalProvisionFamily)
    (trace : Rule45CanonicalComparisonTrace)
    (active : family.Active trace)
    (decisive : family.projectedOrdering trace ≠ Ordering.eq) :
    trace.outcome = family.projectedOrdering trace := by
  cases family with
  | rule4bPairingMethodology =>
      cases count : trace.rule4bReferenceCount <;>
        simp_all [projectedOrdering, Rule45CanonicalComparisonTrace.outcome, compareLex]
  | rule4bLikeUnlike =>
      cases pair : trace.rule4bLikeUnlike <;>
        simp_all [Active, projectedOrdering, Rule45CanonicalComparisonTrace.outcome, compareLex]
  | rule5Enantiomorph =>
      rcases active with ⟨countTie, pairTie, rule4cTie⟩
      cases commonR : trace.rule5CommonR <;>
        simp_all [projectedOrdering, Rule45CanonicalComparisonTrace.outcome,
          Rule45CanonicalComparisonTrace.rule5Result, compareLex]

@[simp] theorem mem_all (family : Rule45CanonicalProvisionFamily) : family ∈ all := by
  cases family <;> simp [all]

theorem provision_injective : Function.Injective provision := by
  intro left right equal
  cases left <;> cases right <;> simp_all [provision]

@[simp] theorem provisions_exact :
    all.map provision =
      [ .p92Rule4bLikeUnlike, .p92Rule4bPairingMethodology, .p92Rule5Enantiomorph ] :=
  rfl

def provisionSlice : List IUPACNormativeProvision := all.map provision

@[simp] theorem provisionSlice_count : provisionSlice.length = 3 := by
  rfl

theorem provisionSlice_nodup : provisionSlice.Nodup := by
  decide

theorem mem_provisionSlice_iff (target : IUPACNormativeProvision) :
    target ∈ provisionSlice ↔
      ∃ family : Rule45CanonicalProvisionFamily, family.provision = target := by
  change target ∈ all.map provision ↔
    ∃ family : Rule45CanonicalProvisionFamily, provision family = target
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨family, _familyMember, equal⟩
    exact ⟨family, equal⟩
  · rintro ⟨family, rfl⟩
    exact List.mem_map.mpr ⟨family, mem_all family, rfl⟩

end Rule45CanonicalProvisionFamily

/-- Source-independent carrier for one pairwise comparison in the canonical partition. -/
structure Rule45CanonicalTraceObservation where
  carrierFuel : Nat
  ruleFuel : Nat
  centerAtom : Nat
  left : Fin 4
  right : Fin 4
  trace : Rule45CanonicalComparisonTrace
  deriving DecidableEq, Repr

/-- Production trace judgment, using the fixed root-frame and initial-partition builders. -/
def Rule45CanonicalTraceProductionJudged
    (source : AuthoritativeChemicalInput)
    (observation : Rule45CanonicalTraceObservation) : Prop :=
  let semantics := source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
    observation.carrierFuel observation.ruleFuel
  ∃ center : source.AromaticCanonicalTetrahedralCenter,
    let target := source.aromaticCanonicalFinalOccurrence observation.carrierFuel center
    let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
    let view := source.aromaticCanonicalDependencyView state target
    ∃ roots partition,
      center.1.val = observation.centerAtom ∧
        observation.left ≠ observation.right ∧
        source.aromaticCanonicalOccurrenceLigandFrame? target = some roots ∧
        source.buildAromaticCanonicalRule3Through5InitialPartition?
            target view observation.ruleFuel roots = some partition ∧
        source.compareAromaticCanonicalUncancelledRule3SpatialKeys
            (partition.frame.keyAt observation.left).rule3
            (partition.frame.keyAt observation.right).rule3 = Ordering.eq ∧
        source.rule45CanonicalComparisonTrace
            (partition.frame.keyAt observation.left).rule45
            (partition.frame.keyAt observation.right).rule45 = observation.trace

/-- Independent trace judgment using the builder-free canonical partition normal form. -/
def Rule45CanonicalTraceCanonicalCompleteJudged
    (source : AuthoritativeChemicalInput)
    (observation : Rule45CanonicalTraceObservation) : Prop :=
  let semantics := source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
    observation.carrierFuel observation.ruleFuel
  ∃ center : source.AromaticCanonicalTetrahedralCenter,
    let target := source.aromaticCanonicalFinalOccurrence observation.carrierFuel center
    let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
    let view := source.aromaticCanonicalDependencyView state target
    ∃ roots partition,
      center.1.val = observation.centerAtom ∧
        observation.left ≠ observation.right ∧
        source.aromaticCanonicalOccurrenceLigandFrame? target = some roots ∧
        source.CanonicalAromaticCanonicalRule3Through5InitialPartition
            target view observation.ruleFuel roots partition ∧
        source.compareAromaticCanonicalUncancelledRule3SpatialKeys
            (partition.frame.keyAt observation.left).rule3
            (partition.frame.keyAt observation.right).rule3 = Ordering.eq ∧
        source.Rule45CanonicalComparisonTraceJudgment
            (partition.frame.keyAt observation.left).rule45
            (partition.frame.keyAt observation.right).rule45 observation.trace

/-- One canonical-partition theorem transports the whole four-stage trace, rather than proving
the Rule-4b and Rule-5 manifest rows separately. -/
theorem rule45CanonicalTraceProduction_iff_canonicalComplete
    (source : AuthoritativeChemicalInput)
    (observation : Rule45CanonicalTraceObservation) :
    Rule45CanonicalTraceProductionJudged source observation ↔
      Rule45CanonicalTraceCanonicalCompleteJudged source observation := by
  unfold Rule45CanonicalTraceProductionJudged
    Rule45CanonicalTraceCanonicalCompleteJudged
  dsimp only
  constructor
  · rintro ⟨center, roots, partition, centerExact, distinct, rootsComputed,
      partitionComputed, rule3Tie, traceComputed⟩
    exact ⟨center, roots, partition, centerExact, distinct, rootsComputed,
      (source.buildAromaticCanonicalRule3Through5InitialPartition?_eq_some_iff_canonical
        _ _ observation.ruleFuel roots partition).mp partitionComputed,
      rule3Tie,
      (source.rule45CanonicalComparisonTrace_eq_iff_judgment _ _ observation.trace).mp
        traceComputed⟩
  · rintro ⟨center, roots, partition, centerExact, distinct, rootsComputed,
      partitionCanonical, rule3Tie, traceJudged⟩
    exact ⟨center, roots, partition, centerExact, distinct, rootsComputed,
      (source.buildAromaticCanonicalRule3Through5InitialPartition?_eq_some_iff_canonical
        _ _ observation.ruleFuel roots partition).mpr partitionCanonical,
      rule3Tie,
      (source.rule45CanonicalComparisonTrace_eq_iff_judgment _ _ observation.trace).mpr
        traceJudged⟩

/-- A manifest-family observation is a typed projection of one complete canonical trace. -/
structure Rule45CanonicalFamilyObservation
    (family : Rule45CanonicalProvisionFamily) where
  carrierFuel : Nat
  ruleFuel : Nat
  centerAtom : Nat
  left : Fin 4
  right : Fin 4
  outcome : family.Result

def Rule45CanonicalFamilyProductionJudged
    (family : Rule45CanonicalProvisionFamily)
    (source : AuthoritativeChemicalInput)
    (observation : Rule45CanonicalFamilyObservation family) : Prop :=
  ∃ trace,
    Rule45CanonicalTraceProductionJudged source
      { carrierFuel := observation.carrierFuel
        ruleFuel := observation.ruleFuel
        centerAtom := observation.centerAtom
        left := observation.left
        right := observation.right
        trace := trace } ∧ family.Active trace ∧
      family.project trace = observation.outcome

def Rule45CanonicalFamilyCanonicalCompleteJudged
    (family : Rule45CanonicalProvisionFamily)
    (source : AuthoritativeChemicalInput)
    (observation : Rule45CanonicalFamilyObservation family) : Prop :=
  ∃ trace,
    Rule45CanonicalTraceCanonicalCompleteJudged source
      { carrierFuel := observation.carrierFuel
        ruleFuel := observation.ruleFuel
        centerAtom := observation.centerAtom
        left := observation.left
        right := observation.right
        trace := trace } ∧ family.Active trace ∧
      family.project trace = observation.outcome

/-- The single trace transport theorem carries every activated Rules-4b/5 execution projection. -/
theorem rule45CanonicalFamilyProduction_iff_canonicalComplete
    (family : Rule45CanonicalProvisionFamily)
    (source : AuthoritativeChemicalInput)
    (observation : Rule45CanonicalFamilyObservation family) :
    Rule45CanonicalFamilyProductionJudged family source observation ↔
      Rule45CanonicalFamilyCanonicalCompleteJudged family source observation := by
  constructor <;> rintro ⟨trace, judged, active, projected⟩
  · exact ⟨trace,
      (rule45CanonicalTraceProduction_iff_canonicalComplete source _).mp judged,
      active, projected⟩
  · exact ⟨trace,
      (rule45CanonicalTraceProduction_iff_canonicalComplete source _).mpr judged,
      active, projected⟩

/-- The independent corpus relation for one Rules-4b/5 family member.  Applicability is exactly
the existence of a builder-free canonical-complete observation on the supplied molecular source;
the public observation type itself remains source-independent. -/
def Rule45CanonicalProvisionFamily.completeReference
    (family : Rule45CanonicalProvisionFamily) : ProvisionReference where
  Observation := Rule45CanonicalFamilyObservation family
  Applicable := fun source =>
    ∃ observation, Rule45CanonicalFamilyCanonicalCompleteJudged family source observation
  Judges := Rule45CanonicalFamilyCanonicalCompleteJudged family

/-- One molecular refinement theorem for the entire heterogeneous Rules-4b/5 family.  It is the
exact `ProvisionCorrect` relation: canonical executable production equals applicability plus the
independent builder-free complete judgment, with all row variation carried only by `family`. -/
theorem rule45CanonicalFamilyProduction_iff_completeReference
    (family : Rule45CanonicalProvisionFamily)
    (source : AuthoritativeChemicalInput)
    (observation : family.completeReference.Observation) :
    Rule45CanonicalFamilyProductionJudged family source observation ↔
      family.completeReference.Applicable source ∧
        family.completeReference.Judges source observation := by
  constructor
  · intro produced
    have complete :=
      (rule45CanonicalFamilyProduction_iff_canonicalComplete family source observation).mp produced
    exact ⟨⟨observation, complete⟩, complete⟩
  · rintro ⟨_applicable, complete⟩
    exact (rule45CanonicalFamilyProduction_iff_canonicalComplete
      family source observation).mpr complete

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeChemicalInput.rule45CanonicalComparisonTrace_outcome
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.rule45CanonicalTraceProduction_iff_canonicalComplete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.rule45CanonicalFamilyProduction_iff_canonicalComplete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.rule45CanonicalFamilyProduction_iff_completeReference
