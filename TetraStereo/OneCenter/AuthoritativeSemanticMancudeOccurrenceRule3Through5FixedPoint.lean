import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeRule3Through6Analysis
import TetraStereo.OneCenter.LocalizedPseudoasymmetricClassification

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput

/-!
# Concrete source-canonical auxiliary fixed point through Rule 5

This is the source-native evaluator required by the molecule Rule-3--6 analyzer.  It recognizes a
real tetrahedral occurrence node, constructs its four-ligand reroot frame, compiles the already
certified source Rules-1a--5 keys, performs the proof-relevant Rule-5 tracked sort, and reads exact
rational coordinates.  Its optional outcome relation covers both success and refusal exactly.
-/

/-! ## Occurrence-center and four-root perception -/

/-- A real occurrence node denotes this perceived source tetrahedral center. -/
def RealAromaticCanonicalTetrahedralOccurrenceNode
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (center : source.AromaticCanonicalTetrahedralCenter) : Prop :=
  node.provenance = OfficialCIPNodeProvenance.realAtom ∧
    node.current? = some center.1

/-- Recover a perceived center only from a real occurrence node. -/
noncomputable def aromaticCanonicalOccurrenceTetrahedralCenter?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    Option source.AromaticCanonicalTetrahedralCenter := by
  classical
  exact if real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom then
    match target.1.node.current? with
    | none => none
    | some atom =>
        if perceived : atom ∈ source.aromaticCanonicalTetrahedralCenterSet then
          some ⟨atom, perceived⟩
        else none
  else none

theorem aromaticCanonicalOccurrenceTetrahedralCenter?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (computed : source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some center) :
    source.RealAromaticCanonicalTetrahedralOccurrenceNode target.1.node center := by
  classical
  unfold aromaticCanonicalOccurrenceTetrahedralCenter? at computed
  by_cases real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  · rw [dif_pos real] at computed
    cases current : target.1.node.current? with
    | none =>
        rw [current] at computed
        cases computed
    | some atom =>
        rw [current] at computed
        dsimp only at computed
        by_cases perceived : atom ∈ source.aromaticCanonicalTetrahedralCenterSet
        · rw [dif_pos perceived] at computed
          have centerEqual :
              (⟨atom, perceived⟩ : source.AromaticCanonicalTetrahedralCenter) = center :=
            Option.some.inj computed
          subst center
          exact ⟨real, current⟩
        · rw [dif_neg perceived] at computed
          cases computed
  · rw [dif_neg real] at computed
    cases computed

/-- Four ordered reroot cursors around one occurrence coordinate. -/
structure AromaticCanonicalOccurrenceFourLigandFrame
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) where
  roots : List (source.AromaticCanonicalRerootCursor carrierFuel)
  rootsLength : roots.length = 4

def AromaticCanonicalOccurrenceFourLigandFrame.cursorAt
    {source : AuthoritativeChemicalInput} {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (index : Fin 4) : source.AromaticCanonicalRerootCursor carrierFuel :=
  frame.roots.get (Fin.cast frame.rootsLength.symm index)

noncomputable def aromaticCanonicalOccurrenceFourLigandFrame?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    Option (source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel) := do
  let roots ← source.aromaticCanonicalOccurrenceLigandFrame? target
  if rootsLength : roots.length = 4 then some { roots, rootsLength } else none

def DeclarativeAromaticCanonicalOccurrenceFourLigandFrame
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel) : Prop :=
  source.DeclarativeAromaticCanonicalRerootChildren
      { occurrence := target, previous? := none } frame.roots ∧
    frame.roots.length = 4

theorem aromaticCanonicalOccurrenceFourLigandFrame?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some frame) :
    source.DeclarativeAromaticCanonicalOccurrenceFourLigandFrame target frame := by
  unfold aromaticCanonicalOccurrenceFourLigandFrame? at computed
  cases rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame? target with
  | none => simp [rootsComputed] at computed
  | some roots =>
      by_cases rootsLength : roots.length = 4
      · simp [rootsComputed, rootsLength] at computed
        subst frame
        exact ⟨source.aromaticCanonicalOccurrenceLigandFrame?_sound
          target roots rootsComputed, rootsLength⟩
      · simp [rootsComputed, rootsLength] at computed

/-! ## Proof-relevant source Rules-1a--5 ordering -/

/-- Convert the source Rule-5 record into the generic tracked-sort record without changing its
order or pseudoasymmetric flag. -/
def aromaticCanonicalRule3Through5DescriptorComparison
    (comparison : ConstitutionalRule5Comparison) :
    ConstitutionalDescriptorHierarchyComparison :=
  { ordering := comparison.ordering
    decisiveRule? := none
    pseudo := comparison.pseudo }

noncomputable def compareAromaticCanonicalOccurrenceRule3Through5At?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4) : Option ConstitutionalDescriptorHierarchyComparison :=
  some (aromaticCanonicalRule3Through5DescriptorComparison
    (source.compareAromaticCanonicalOccurrenceRule3Through5At frame left right))

noncomputable def aromaticCanonicalOccurrenceRule3Through5TrackedOrder?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) :
    Option TrackedLocalizedLigandOrder :=
  sortFourLocalizedLigandsTracked
    (source.compareAromaticCanonicalOccurrenceRule3Through5At? frame)

noncomputable def aromaticCanonicalOccurrenceRule3Through5OrderPairStrict
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4) : Bool :=
  (source.compareAromaticCanonicalOccurrenceRule3Through5At frame left right).ordering ==
    Ordering.gt

noncomputable def aromaticCanonicalOccurrenceRule3Through5OrderCoherent
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) :
    List (Fin 4) → Bool
  | [] => true
  | left :: rest =>
      rest.all (source.aromaticCanonicalOccurrenceRule3Through5OrderPairStrict frame left) &&
        source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent frame rest

theorem aromaticCanonicalOccurrenceRule3Through5OrderCoherent_eq_true_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) :
    ∀ order,
      source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent frame order = true ↔
        order.Pairwise fun left right =>
          (source.compareAromaticCanonicalOccurrenceRule3Through5At
            frame left right).ordering = Ordering.gt
  | [] => by simp [aromaticCanonicalOccurrenceRule3Through5OrderCoherent]
  | left :: rest => by
      rw [aromaticCanonicalOccurrenceRule3Through5OrderCoherent, Bool.and_eq_true,
        List.all_eq_true, List.pairwise_cons,
        aromaticCanonicalOccurrenceRule3Through5OrderCoherent_eq_true_iff]
      simp [aromaticCanonicalOccurrenceRule3Through5OrderPairStrict]

noncomputable def safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) :
    Option TrackedLocalizedLigandOrder := do
  let tracked ← source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? frame
  if source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent
      frame tracked.highestFirst then some tracked else none

def DeclarativeSafeAromaticCanonicalOccurrenceRule3Through5TrackedOrder
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder) : Prop :=
  DeclarativeTrackedLocalizedLigandSort
      (source.compareAromaticCanonicalOccurrenceRule3Through5At? frame)
      (List.finRange 4) [] 0 tracked ∧
    tracked.highestFirst.Perm (List.finRange 4) ∧
    tracked.highestFirst.Pairwise fun left right =>
      (source.compareAromaticCanonicalOccurrenceRule3Through5At
        frame left right).ordering = Ordering.gt

theorem safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder)
    (computed : source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? frame =
      some tracked) :
    source.DeclarativeSafeAromaticCanonicalOccurrenceRule3Through5TrackedOrder
      frame tracked := by
  unfold safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? at computed
  cases trackedComputed :
      source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? frame with
  | none => simp [trackedComputed] at computed
  | some observed =>
      cases coherent : source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent
          frame observed.highestFirst with
      | false => simp [trackedComputed, coherent] at computed
      | true =>
          simp [trackedComputed, coherent] at computed
          subst tracked
          exact ⟨
            sortFourLocalizedLigandsTracked_sound
              (source.compareAromaticCanonicalOccurrenceRule3Through5At? frame)
              observed trackedComputed,
            sortFourLocalizedLigandsTracked_perm
              (source.compareAromaticCanonicalOccurrenceRule3Through5At? frame)
              observed trackedComputed,
            (source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent_eq_true_iff
              frame observed.highestFirst).mp coherent⟩

/-- The safe tracked sorter is extensional in the complete Rules-3--5 comparison.  Therefore an
automorphism preserving every pair comparison preserves both ligand order and the exact number
of pseudo comparisons without replaying the insertion-sort derivation. -/
theorem safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_eq_of_compare
    (source : AuthoritativeChemicalInput) {carrierFuel : ℕ}
    (original mapped : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (compareNatural : ∀ left right,
      source.compareAromaticCanonicalOccurrenceRule3Through5At mapped left right =
        source.compareAromaticCanonicalOccurrenceRule3Through5At original left right) :
    source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? mapped =
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? original := by
  have compareAtEq :
      source.compareAromaticCanonicalOccurrenceRule3Through5At? mapped =
        source.compareAromaticCanonicalOccurrenceRule3Through5At? original := by
    funext left right
    simp [compareAromaticCanonicalOccurrenceRule3Through5At?, compareNatural left right]
  have trackedEq :
      source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? mapped =
        source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? original := by
    unfold aromaticCanonicalOccurrenceRule3Through5TrackedOrder?
    rw [compareAtEq]
  have coherentEq : ∀ order,
      source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent mapped order =
        source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent original order := by
    intro order
    induction order with
    | nil => rfl
    | cons left rest inductionHypothesis =>
        unfold aromaticCanonicalOccurrenceRule3Through5OrderCoherent
        have predicateEq :
            source.aromaticCanonicalOccurrenceRule3Through5OrderPairStrict mapped left =
              source.aromaticCanonicalOccurrenceRule3Through5OrderPairStrict original left := by
          funext right
          simp [aromaticCanonicalOccurrenceRule3Through5OrderPairStrict,
            compareNatural left right]
        rw [predicateEq, inductionHypothesis]
  unfold safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
  rw [trackedEq]
  cases source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? original with
  | none => rfl
  | some tracked =>
      simp
      rw [coherentEq tracked.highestFirst]

/-! ## Exact source occurrence descriptor -/

structure AromaticCanonicalOccurrenceRule3Through5SpatialEvidence
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) where
  center : source.AromaticCanonicalTetrahedralCenter
  base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel
  keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel
  tracked : TrackedLocalizedLigandOrder
  points : List CartesianPoint3

noncomputable def aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat) :
    Option (source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel) := do
  let center ← source.aromaticCanonicalOccurrenceTetrahedralCenter? target
  let base ← source.aromaticCanonicalOccurrenceFourLigandFrame? target
  let keys ← source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
    target view ruleFuel base.roots
  let tracked ← source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys
  let points ← tracked.highestFirst.mapM fun index =>
    source.aromaticCanonicalRerootSpatialPoint? (base.cursorAt index)
  some { center, base, keys, tracked, points }

private theorem mapM_aromaticCanonicalRule3Through5SpatialPoint_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel) :
    ∀ order points,
      order.mapM (fun index => source.aromaticCanonicalRerootSpatialPoint?
        (base.cursorAt index)) = some points →
      List.Forall₂
        (fun index point => source.DeclarativeAromaticCanonicalRerootSpatialPoint
          (base.cursorAt index) point)
        order points
  | [], points, computed => by
      simp at computed
      subst points
      exact .nil
  | index :: order, points, computed => by
      rw [List.mapM_cons] at computed
      cases pointComputed : source.aromaticCanonicalRerootSpatialPoint?
          (base.cursorAt index) with
      | none => simp [pointComputed] at computed
      | some point =>
          cases tailComputed : order.mapM (fun next =>
              source.aromaticCanonicalRerootSpatialPoint?
                (base.cursorAt next)) with
          | none => simp [pointComputed, tailComputed] at computed
          | some tail =>
              simp [pointComputed, tailComputed] at computed
              subst points
              exact .cons
                ((source.aromaticCanonicalRerootSpatialPoint?_eq_some_iff
                  (base.cursorAt index) point).mp pointComputed)
                (mapM_aromaticCanonicalRule3Through5SpatialPoint_sound
                  source base order tail tailComputed)

def DeclarativeAromaticCanonicalOccurrenceRule3Through5SpatialEvidence
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat)
    (evidence : source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence
      carrierFuel) : Prop :=
  source.RealAromaticCanonicalTetrahedralOccurrenceNode target.1.node evidence.center ∧
    source.DeclarativeAromaticCanonicalOccurrenceFourLigandFrame target evidence.base ∧
    source.DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyFrame
      target view ruleFuel evidence.base.roots evidence.keys ∧
    source.DeclarativeSafeAromaticCanonicalOccurrenceRule3Through5TrackedOrder
      evidence.keys evidence.tracked ∧
    List.Forall₂
      (fun index point => source.DeclarativeAromaticCanonicalRerootSpatialPoint
        (evidence.base.cursorAt index) point)
      evidence.tracked.highestFirst evidence.points

theorem aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat)
    (evidence : source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence
      carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
      target view ruleFuel = some evidence) :
    source.DeclarativeAromaticCanonicalOccurrenceRule3Through5SpatialEvidence
      target view ruleFuel evidence := by
  unfold aromaticCanonicalOccurrenceRule3Through5SpatialEvidence? at computed
  cases centerComputed : source.aromaticCanonicalOccurrenceTetrahedralCenter? target with
  | none => simp [centerComputed] at computed
  | some center =>
      cases baseComputed : source.aromaticCanonicalOccurrenceFourLigandFrame? target with
      | none => simp [centerComputed, baseComputed] at computed
      | some base =>
          cases keysComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
              target view ruleFuel base.roots with
          | none => simp [centerComputed, baseComputed, keysComputed] at computed
          | some keys =>
              cases trackedComputed :
                  source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys with
              | none =>
                  simp [centerComputed, baseComputed, keysComputed, trackedComputed] at computed
              | some tracked =>
                  cases pointsComputed : tracked.highestFirst.mapM (fun index =>
                      source.aromaticCanonicalRerootSpatialPoint?
                        (base.cursorAt index)) with
                  | none =>
                      simp [centerComputed, baseComputed, keysComputed, trackedComputed,
                        pointsComputed] at computed
                  | some points =>
                      simp [centerComputed, baseComputed, keysComputed, trackedComputed,
                        pointsComputed] at computed
                      subst evidence
                      exact ⟨
                        source.aromaticCanonicalOccurrenceTetrahedralCenter?_sound
                          target center centerComputed,
                        source.aromaticCanonicalOccurrenceFourLigandFrame?_sound
                          target base baseComputed,
                        source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_sound
                          target view ruleFuel base.roots keys keysComputed,
                        source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_sound
                          keys tracked trackedComputed,
                        mapM_aromaticCanonicalRule3Through5SpatialPoint_sound
                          source base tracked.highestFirst points pointsComputed⟩

noncomputable def aromaticCanonicalOccurrenceRule3Through5Descriptor?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat) : Option AromaticCanonicalAuxiliaryLabel := do
  let evidence ← source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
    target view ruleFuel
  let raw ← CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

def CanonicalAromaticCanonicalOccurrenceRule3Through5Descriptor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat) (descriptor : AromaticCanonicalAuxiliaryLabel) : Prop :=
  ∃ evidence raw,
    source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
        target view ruleFuel = some evidence ∧
    CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor evidence.points raw ∧
    descriptor = classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons

theorem aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat) (descriptor : AromaticCanonicalAuxiliaryLabel) :
    source.aromaticCanonicalOccurrenceRule3Through5Descriptor?
        target view ruleFuel = some descriptor ↔
      source.CanonicalAromaticCanonicalOccurrenceRule3Through5Descriptor
        target view ruleFuel descriptor := by
  constructor
  · intro computed
    unfold aromaticCanonicalOccurrenceRule3Through5Descriptor? at computed
    cases evidenceComputed :
        source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
          target view ruleFuel with
    | none => simp [evidenceComputed] at computed
    | some evidence =>
        cases rawComputed :
            CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? evidence.points with
        | none => simp [evidenceComputed, rawComputed] at computed
        | some raw =>
            simp [evidenceComputed, rawComputed] at computed
            subst descriptor
            exact ⟨evidence, raw, evidenceComputed,
              (CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?_eq_some_iff
                evidence.points raw).mp rawComputed, rfl⟩
  · rintro ⟨evidence, raw, evidenceComputed, handedness, rfl⟩
    unfold aromaticCanonicalOccurrenceRule3Through5Descriptor?
    rw [evidenceComputed]
    change (do
      let observed ←
        CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? evidence.points
      some (classifyTetrahedralRSPseudo observed evidence.tracked.pseudoComparisons)) =
      some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)
    rw [(CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?_eq_some_iff
      evidence.points raw).mpr handedness]
    rfl

theorem aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_none_iff_no_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat) :
    source.aromaticCanonicalOccurrenceRule3Through5Descriptor?
        target view ruleFuel = none ↔
      ¬ ∃ descriptor,
        source.CanonicalAromaticCanonicalOccurrenceRule3Through5Descriptor
          target view ruleFuel descriptor := by
  constructor
  · intro refused ⟨descriptor, canonical⟩
    have accepted :=
      (source.aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
        target view ruleFuel descriptor).mpr canonical
    rw [refused] at accepted
    contradiction
  · intro absent
    cases computed : source.aromaticCanonicalOccurrenceRule3Through5Descriptor?
        target view ruleFuel with
    | none => rfl
    | some descriptor =>
        exact (absent ⟨descriptor,
          (source.aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
            target view ruleFuel descriptor).mp computed⟩).elim

/-! ## Concrete complete-outcome semantics and fixed point -/

def DeclarativeAromaticCanonicalOccurrenceRule3Through5Outcome
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (ruleFuel : Nat) (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (outcome : Option AromaticCanonicalAuxiliaryLabel) : Prop :=
  match outcome with
  | none =>
      ¬ ∃ descriptor,
        source.CanonicalAromaticCanonicalOccurrenceRule3Through5Descriptor target
          (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor
  | some descriptor =>
      source.CanonicalAromaticCanonicalOccurrenceRule3Through5Descriptor target
        (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor

theorem declarativeAromaticCanonicalOccurrenceRule3Through5Outcome_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (ruleFuel : Nat) (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (outcome : Option AromaticCanonicalAuxiliaryLabel) :
    source.DeclarativeAromaticCanonicalOccurrenceRule3Through5Outcome
        ruleFuel state target outcome ↔
      source.aromaticCanonicalOccurrenceRule3Through5Descriptor? target
        (source.aromaticCanonicalDependencyView state target) ruleFuel = outcome := by
  cases outcome with
  | none =>
      exact (source.aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_none_iff_no_canonical
        target (source.aromaticCanonicalDependencyView state target) ruleFuel).symm
  | some descriptor =>
      exact (source.aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
        target (source.aromaticCanonicalDependencyView state target)
        ruleFuel descriptor).symm

noncomputable def aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalRuleSemantics carrierFuel where
  DeclarativeDerivation :=
    source.DeclarativeAromaticCanonicalOccurrenceRule3Through5Outcome ruleFuel
  executableRule := fun target view =>
    source.aromaticCanonicalOccurrenceRule3Through5Descriptor? target view ruleFuel
  derivation_executable_iff := by
    intro state target outcome
    exact source.declarativeAromaticCanonicalOccurrenceRule3Through5Outcome_iff
      ruleFuel state target outcome

theorem existsUnique_aromaticCanonicalOccurrenceRule3Through5Model
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    ∃! state,
      (source.aromaticCanonicalOccurrenceSystem
        (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
          carrierFuel ruleFuel)).CIPModel state :=
  source.existsUnique_aromaticCanonicalCIPModel
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel)

/-- Every label in any concrete model is exactly one canonical source occurrence result. -/
theorem aromaticCanonicalOccurrenceRule3Through5Model_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel ruleFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel)).CIPModel state)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (descriptor : AromaticCanonicalAuxiliaryLabel) :
    state target = some descriptor ↔
      source.CanonicalAromaticCanonicalOccurrenceRule3Through5Descriptor target
        (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor := by
  have fixed :=
    (source.aromaticCanonicalOccurrenceSystem
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel)).cipModel_iff_executableStateStep_fixed
      (source.aromaticCanonicalDerivationStepCorrespondence
        (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
          carrierFuel ruleFuel)) state |>.mp model
  have atTarget := congrFun fixed target
  rw [← atTarget]
  exact source.aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
    target (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor

/-- A completed occurrence evidence record with nondegenerate exact geometry forces the unique
scheduled model to contain its classified auxiliary label. -/
theorem aromaticCanonicalOccurrenceRule3Through5Model_eq_some_of_spatialEvidence
    (source : AuthoritativeChemicalInput) {carrierFuel ruleFuel : ℕ}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel)).CIPModel state)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (evidence : source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel)
    (raw : RS)
    (evidenceComputed : source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
      target (source.aromaticCanonicalDependencyView state target) ruleFuel = some evidence)
    (geometry : CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor evidence.points raw) :
    state target = some (classifyTetrahedralRSPseudo raw
      evidence.tracked.pseudoComparisons) := by
  apply (source.aromaticCanonicalOccurrenceRule3Through5Model_eq_some_iff_canonical
    state model target
      (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)).mpr
  exact ⟨evidence, raw, evidenceComputed, geometry, rfl⟩

/-- In every valid fixed-point model, a non-tetrahedral occurrence is forced to the semantic
`none` outcome by the evaluator's first gate. -/
theorem aromaticCanonicalOccurrenceRule3Through5Model_eq_none_of_no_center
    (source : AuthoritativeChemicalInput) {carrierFuel ruleFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel)).CIPModel state)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (centerAbsent :
      source.aromaticCanonicalOccurrenceTetrahedralCenter? target = none) :
    state target = none := by
  have fixed :=
    (source.aromaticCanonicalOccurrenceSystem
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel)).cipModel_iff_executableStateStep_fixed
      (source.aromaticCanonicalDerivationStepCorrespondence
        (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
          carrierFuel ruleFuel)) state |>.mp model
  have atTarget := congrFun fixed target
  rw [← atTarget]
  simp [DeclarativeCIP.OccurrenceSystem.executableStateStep,
    aromaticCanonicalOccurrenceSystem,
    aromaticCanonicalExecutableStep,
    aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics,
    aromaticCanonicalOccurrenceRule3Through5Descriptor?,
    aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?, centerAbsent]

/-- Parameter-free evaluator choice for the molecule Rule-3--6 descriptor at a requested depth. -/
noncomputable def aromaticCanonicalConcreteRule3Through6Descriptor?
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) : Option RS :=
  source.aromaticCanonicalScheduledRule3Through6Descriptor?
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel) ruleFuel center

/-- Full meaning of a concrete final descriptor, including the causal auxiliary model whose
labels are consumed by Rules 4 and 5. -/
def AromaticCanonicalConcreteRule3Through6DescriptorJudgment
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (descriptor : RS) : Prop :=
  let semantics := source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
    carrierFuel ruleFuel
  source.AromaticCanonicalScheduledRule3Through6DescriptorJudgment
      semantics ruleFuel center descriptor ∧
    (source.aromaticCanonicalOccurrenceSystem semantics).CIPModel
      (source.aromaticCanonicalScheduledAuxiliaryState semantics)

theorem aromaticCanonicalConcreteRule3Through6Descriptor?_sound
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (descriptor : RS)
    (computed : source.aromaticCanonicalConcreteRule3Through6Descriptor?
      carrierFuel ruleFuel center = some descriptor) :
    source.AromaticCanonicalConcreteRule3Through6DescriptorJudgment
      carrierFuel ruleFuel center descriptor := by
  let semantics := source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
    carrierFuel ruleFuel
  exact ⟨
    source.aromaticCanonicalScheduledRule3Through6Descriptor?_sound
      semantics ruleFuel center descriptor computed,
    source.aromaticCanonicalScheduledAuxiliaryState_cipModel semantics⟩

/-- Whole-molecule analysis with the concrete source evaluator; no semantic callback remains. -/
noncomputable def analyzeAromaticCanonicalConcreteRule3Through6
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    List source.AromaticCanonicalScheduledRule3Through6Assignment :=
  source.analyzeAromaticCanonicalScheduledRule3Through6
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel) ruleFuel

/-- Every assignment emitted by the concrete whole-molecule analyzer satisfies the full judgment
and is backed by the unique causal auxiliary fixed point. -/
theorem analyzeAromaticCanonicalConcreteRule3Through6_member_sound
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalScheduledRule3Through6Assignment)
    (present : assignment ∈ source.analyzeAromaticCanonicalConcreteRule3Through6
      carrierFuel ruleFuel) :
    source.AromaticCanonicalConcreteRule3Through6DescriptorJudgment
      carrierFuel ruleFuel assignment.center assignment.descriptor := by
  apply source.aromaticCanonicalConcreteRule3Through6Descriptor?_sound
  exact (source.mem_analyzeAromaticCanonicalScheduledRule3Through6_iff
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel) ruleFuel assignment).mp present

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
