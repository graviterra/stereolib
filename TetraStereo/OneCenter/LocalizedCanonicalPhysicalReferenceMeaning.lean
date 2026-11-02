import TetraStereo.OneCenter.LocalizedCanonicalAuxiliaryRS
import TetraStereo.OneCenter.LocalizedActualPhysicalReferenceObservationClosure
import TetraStereo.OneCenter.LocalizedPhysicalStageExtensionClosure
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open Rule4bSparseSource



























namespace ActualSlotPhysicalSetup

variable {input : LocalizedUniversalReference.Input}

/-! ## A. Pointwise canonical physical meaning of a marked position -/






theorem position_referenceState_iff_canonicalPhysicalDescriptor
    (setup : ActualSlotPhysicalSetup input) (p : Position setup.tree)
    (marked : setup.PositionMarked p) (rs : RS) :
    LocalizedUniversalReference.referenceState input (positionSource p).occurrence =
        some (.chiral rs) ↔
      (setup.positionContext p marked).CanonicalPhysicalDescriptor
        (setup.positionBranch p marked) rs :=
  (setup.positionContext p marked).referenceState_iff_canonicalPhysicalDescriptor
    (setup.positionBranch p marked) rs




theorem position_label_iff_canonicalPhysicalDescriptor
    (setup : ActualSlotPhysicalSetup input) (p : Position setup.tree)
    (marked : setup.PositionMarked p) (rs : RS) :
    (positionNode p).label = some (.chiral rs) ↔
      (setup.positionContext p marked).CanonicalPhysicalDescriptor
        (setup.positionBranch p marked) rs := by
  rw [setup.tree_positionNode_label_eq_state p]
  exact setup.position_referenceState_iff_canonicalPhysicalDescriptor p marked rs

/-- The canonical descriptor at a marked position is exactly the executed `RS.ofHandedness` of
that position's own normalized physical sense.  This ties the graph-only descriptor to the actual
auxiliary meaning rather than to a copied letter. -/
theorem position_canonicalPhysicalDescriptor_iff_ofHandedness
    (setup : ActualSlotPhysicalSetup input) (p : Position setup.tree)
    (marked : setup.PositionMarked p) (rs : RS) :
    (setup.positionContext p marked).CanonicalPhysicalDescriptor
        (setup.positionBranch p marked) rs ↔
      rs = RS.ofHandedness (setup.positionSense p marked) := by
  have stateIff :=
    (setup.positionContext p marked).referenceState_eq_chiral_iff_ofHandedness
      (setup.positionBranch p marked) rs
  have descriptorIff :=
    (setup.positionContext p marked).referenceState_iff_canonicalPhysicalDescriptor
      (setup.positionBranch p marked) rs
  exact descriptorIff.symm.trans stateIff

/-- The canonical descriptor produced by the actual sense exists at every marked position. -/
theorem position_canonicalPhysicalDescriptor_ofHandedness
    (setup : ActualSlotPhysicalSetup input) (p : Position setup.tree)
    (marked : setup.PositionMarked p) :
    (setup.positionContext p marked).CanonicalPhysicalDescriptor
      (setup.positionBranch p marked)
        (RS.ofHandedness (setup.positionSense p marked)) :=
  (setup.position_canonicalPhysicalDescriptor_iff_ofHandedness p marked _).mpr rfl

/-- **Derived actual existence.**  Every marked position actually carries a chiral label and the
same letter is its canonical physical descriptor. -/
theorem exists_position_canonicalPhysicalDescriptor
    (setup : ActualSlotPhysicalSetup input) (p : Position setup.tree)
    (marked : setup.PositionMarked p) :
    ∃ rs : RS,
      (positionNode p).label = some (.chiral rs) ∧
        (setup.positionContext p marked).CanonicalPhysicalDescriptor
          (setup.positionBranch p marked) rs := by
  obtain ⟨rs, stateEq, descriptor⟩ :=
    (setup.positionContext p marked).exists_referenceState_canonicalPhysicalDescriptor
      (setup.positionBranch p marked)
  refine ⟨rs, ?_, descriptor⟩
  rw [setup.tree_positionNode_label_eq_state p]
  exact stateEq



theorem position_canonicalPhysicalDescriptor_unique
    (setup : ActualSlotPhysicalSetup input) (p : Position setup.tree)
    (marked : setup.PositionMarked p) {first second : RS}
    (left : (setup.positionContext p marked).CanonicalPhysicalDescriptor
      (setup.positionBranch p marked) first)
    (right : (setup.positionContext p marked).CanonicalPhysicalDescriptor
      (setup.positionBranch p marked) second) : first = second :=
  (setup.positionContext p marked).canonicalPhysicalDescriptor_unique
    (setup.positionBranch p marked) left right

/-! ## B. Unmarked positions: actual absence, not an assumed state -/





theorem position_referenceState_eq_none_of_not_marked
    (setup : ActualSlotPhysicalSetup input) (p : Position setup.tree)
    (notMarked : ¬ setup.PositionMarked p) :
    LocalizedUniversalReference.referenceState input (positionSource p).occurrence = none := by
  have reachable := actualChildReachable_positionSource (input := input.certified)
    (carrierFuel := LocalizedUniversalReference.carrierFuel input)
    (read := ActualReaderPhysicalBranchInverse.dependencyReader input setup.c)
    setup.tree_realizes p
  rcases reachable_cursor_reader_none_or_chiral setup reachable with noneEq | ⟨rs, chiralEq⟩
  · rwa [reachable_cursor_reader_eq_state setup reachable] at noneEq
  · exfalso
    have stateEq : LocalizedUniversalReference.referenceState input
        (positionSource p).occurrence = some (.chiral rs) := by
      rw [← reachable_cursor_reader_eq_state setup reachable]
      exact chiralEq
    exact setup.position_not_chiral_of_not_marked p notMarked rs
      (by
        rw [setup.tree_positionNode_label_eq_state p]
        exact stateEq)

/-- At an unmarked position the actual tree label is `none`, derived from the actual reader
state rather than assumed. -/
theorem position_label_eq_none_of_not_marked
    (setup : ActualSlotPhysicalSetup input) (p : Position setup.tree)
    (notMarked : ¬ setup.PositionMarked p) :
    (positionNode p).label = none := by
  rw [setup.tree_positionNode_label_eq_state p,
    setup.position_referenceState_eq_none_of_not_marked p notMarked]

/-- At an unmarked position the upper-case descriptor readback of the actual label is `none`. -/
theorem position_chiralDescriptorOfLabel_eq_none_of_not_marked
    (setup : ActualSlotPhysicalSetup input) (p : Position setup.tree)
    (notMarked : ¬ setup.PositionMarked p) :
    chiralDescriptorOfLabel ((positionNode p).label) = none := by
  rw [setup.position_label_eq_none_of_not_marked p notMarked]
  rfl

/-! ## C. Rule-4b relative observation against an actual selected reference -/

/-- Constructor-level fact about the booleans arising in the sparse Rule-4b observation. -/
private theorem rule4bPairClass_if_like_iff (flag : Bool) :
    (if flag then BlueBookP92.Rule4bPairClass.like else .unlike) = .like ↔ flag = true := by
  cases flag <;> decide

/-- Constructor-level fact about the booleans arising in the sparse Rule-4b observation. -/
private theorem rule4bPairClass_if_unlike_iff (flag : Bool) :
    (if flag then .like else BlueBookP92.Rule4bPairClass.unlike) = .unlike ↔ flag = false := by
  cases flag <;> decide

/-- The actual sparse Rule-4b observation at a marked position, written against the canonical
descriptor `rp` of that same position.  The only input is the canonical descriptor; the letter is
read back from the actual label, not supplied. -/
theorem position_sourceObserve_pair?_eq_of_canonicalDescriptor
    (setup : ActualSlotPhysicalSetup input) (p : Position setup.tree)
    (marked : setup.PositionMarked p) {rp : RS}
    (descriptor : (setup.positionContext p marked).CanonicalPhysicalDescriptor
      (setup.positionBranch p marked) rp) (reference : RS) :
    (sourceObserveRule4bLabel reference ((positionNode p).label)).pair? =
      some (if rp == reference then .like else .unlike) := by
  have labelEq : (positionNode p).label = some (.chiral rp) :=
    (setup.position_label_iff_canonicalPhysicalDescriptor p marked rp).mpr descriptor
  rw [labelEq]
  rfl

/-- **Deliverable 3, `like`.**  At any marked position, the actual Rule-4b observation against a
reference letter is `like` exactly when the canonical physical descriptor of that position is that
same reference letter. -/
theorem position_sourceObserve_pair?_eq_some_like_iff
    (setup : ActualSlotPhysicalSetup input) (p : Position setup.tree)
    (marked : setup.PositionMarked p) (reference : RS) :
    (sourceObserveRule4bLabel reference ((positionNode p).label)).pair? = some .like ↔
      (setup.positionContext p marked).CanonicalPhysicalDescriptor
        (setup.positionBranch p marked) reference := by
  obtain ⟨rp, _labelEq, rpDescriptor⟩ :=
    setup.exists_position_canonicalPhysicalDescriptor p marked
  have formula := setup.position_sourceObserve_pair?_eq_of_canonicalDescriptor p marked
    rpDescriptor reference
  constructor
  · intro pairLike
    have ifLike : (if rp == reference then BlueBookP92.Rule4bPairClass.like else .unlike) =
        .like := by
      have someEq : some (if rp == reference then BlueBookP92.Rule4bPairClass.like
          else .unlike) = some BlueBookP92.Rule4bPairClass.like := by
        rw [← formula]
        exact pairLike
      exact Option.some.inj someEq
    have beq : (rp == reference) = true := (rule4bPairClass_if_like_iff _).mp ifLike
    have rpEqReference : rp = reference := beq_iff_eq.mp beq
    rw [← rpEqReference]
    exact rpDescriptor
  · intro canonical
    have rpEqReference : rp = reference :=
      setup.position_canonicalPhysicalDescriptor_unique p marked rpDescriptor canonical
    have beq : (rp == reference) = true := beq_iff_eq.mpr rpEqReference
    rw [formula, (rule4bPairClass_if_like_iff _).mpr beq]

/-- **Deliverable 3, `unlike`.**  At any marked position, the actual Rule-4b observation against a
reference letter is `unlike` exactly when the canonical physical descriptor of that position is
not that same reference letter. -/
theorem position_sourceObserve_pair?_eq_some_unlike_iff
    (setup : ActualSlotPhysicalSetup input) (p : Position setup.tree)
    (marked : setup.PositionMarked p) (reference : RS) :
    (sourceObserveRule4bLabel reference ((positionNode p).label)).pair? = some .unlike ↔
      ¬ (setup.positionContext p marked).CanonicalPhysicalDescriptor
        (setup.positionBranch p marked) reference := by
  obtain ⟨rp, _labelEq, rpDescriptor⟩ :=
    setup.exists_position_canonicalPhysicalDescriptor p marked
  have formula := setup.position_sourceObserve_pair?_eq_of_canonicalDescriptor p marked
    rpDescriptor reference
  constructor
  · intro pairUnlike canonical
    have rpEqReference : rp = reference :=
      setup.position_canonicalPhysicalDescriptor_unique p marked rpDescriptor canonical
    have ifUnlike : (if rp == reference then BlueBookP92.Rule4bPairClass.like else .unlike) =
        .unlike := by
      have someEq : some (if rp == reference then BlueBookP92.Rule4bPairClass.like
          else .unlike) = some BlueBookP92.Rule4bPairClass.unlike := by
        rw [← formula]
        exact pairUnlike
      exact Option.some.inj someEq
    have beqFalse : (rp == reference) = false := (rule4bPairClass_if_unlike_iff _).mp ifUnlike
    have beqTrue : (rp == reference) = true := beq_iff_eq.mpr rpEqReference
    rw [beqTrue] at beqFalse
    cases beqFalse
  · intro notCanonical
    have rpNeReference : rp ≠ reference := by
      intro rpEqReference
      exact notCanonical (rpEqReference ▸ rpDescriptor)
    have beq : (rp == reference) = false := by
      cases hval : (rp == reference) with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp hval) rpNeReference
    rw [formula, (rule4bPairClass_if_unlike_iff _).mpr beq]

/-! ## D. The unique nearest actual position and the actual selected reference -/

/-- The physical context of the actual unique nearest position. -/
def nearestContext (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance) :
    DomainPhysicalContext input :=
  setup.positionContext (setup.nearestPosition unique) (setup.nearestPosition_marked unique)

/-- The rigid branch of the actual unique nearest position. -/
def nearestBranch (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance) :
    DomainPhysicalRigidBranch (setup.nearestContext unique) :=
  setup.positionBranch (setup.nearestPosition unique) (setup.nearestPosition_marked unique)

/-- The normalized physical sense of the actual unique nearest position. -/
def nearestSense (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance) : ℝ :=
  setup.positionSense (setup.nearestPosition unique) (setup.nearestPosition_marked unique)

/-- The nearest sense is `±1`. -/
theorem nearestSense_eq_one_or_neg_one (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance) :
    setup.nearestSense unique = 1 ∨ setup.nearestSense unique = -1 :=
  setup.positionSense_eq_one_or_neg_one (setup.nearestPosition unique)
    (setup.nearestPosition_marked unique)

/-- The canonical descriptor context at the nearest position keeps the original outer root. -/
theorem nearestContext_target_root (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance) :
    (setup.nearestContext unique).target.1.root = setup.root.1 := by
  simpa [nearestContext, root] using
    setup.position_source_root_eq (setup.nearestPosition unique)

/-- **Deliverable 2, selected facts.**  On a physically unique-nearest branch, the actual nearest
position is the selected centre; the actual selected descriptor, the actual prior reference
singleton, the actual single prior reading with its `reference?`, the executed
`RS.ofHandedness` of the nearest sense, and the canonical descriptor at that same nearest physical
context all coincide.  Nothing here assumes a desired letter or a successful build; deeper marked
centres are unrestricted. -/
theorem nearest_selected_singleton (setup : ActualSlotPhysicalSetup input)
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
              descriptor = RS.ofHandedness (setup.nearestSense unique) ∧
                (setup.nearestContext unique).CanonicalPhysicalDescriptor
                  (setup.nearestBranch unique) descriptor ∧
                  positionAtom setup.singleBonded setup.acyclic
                    (setup.nearestPosition unique) = center := by
  obtain ⟨descriptor, markedEq, ranked, refs, readingData, descriptorEq⟩ :=
    TetraStereo.OneCenter.physical_selected_reference_of_unique setup unique
  have stateEq := setup.position_referenceState_eq_chiral (setup.nearestPosition unique)
    (setup.nearestPosition_marked unique)
  have canonical : (setup.nearestContext unique).CanonicalPhysicalDescriptor
      (setup.nearestBranch unique) descriptor := by
    have stateDescriptor : LocalizedUniversalReference.referenceState input
        (setup.nearestContext unique).target = some (.chiral descriptor) := by
      rw [descriptorEq]
      exact stateEq
    exact ((setup.nearestContext unique).referenceState_iff_canonicalPhysicalDescriptor
      (setup.nearestBranch unique) descriptor).mp stateDescriptor
  exact ⟨descriptor, markedEq, ranked, refs, readingData,
    by simpa [nearestSense] using descriptorEq, canonical,
    setup.nearestPosition_atom unique⟩

/-- **Deliverable 2, actual reference-list characterization.**  The actual prior reference list on
a unique-nearest branch is the singleton `[rs]` exactly when the canonical physical descriptor at
that same nearest physical context is `rs`.  The actual singleton reading, the selected centre and
the nearest position are retained by `nearest_selected_singleton`. -/
theorem nearest_references_iff_canonicalPhysicalDescriptor
    (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance) (rs : RS) :
    setup.key.prior.references = [rs] ↔
      (setup.nearestContext unique).CanonicalPhysicalDescriptor
        (setup.nearestBranch unique) rs := by
  obtain ⟨descriptor, _markedEq, _ranked, refs, _readingData, descriptorEq⟩ :=
    TetraStereo.OneCenter.physical_selected_reference_of_unique setup unique
  have selectedEq : setup.key.prior.references = [descriptor] := refs
  constructor
  · intro refsRs
    have listEq : [descriptor] = [rs] := selectedEq.symm.trans refsRs
    have rsEqDescriptor : rs = descriptor := by
      have hhead : some descriptor = some rs := by
        simpa using congrArg List.head? listEq
      exact (Option.some.inj hhead).symm
    have rsEq : rs = RS.ofHandedness (setup.positionSense (setup.nearestPosition unique)
        (setup.nearestPosition_marked unique)) := by
      rw [rsEqDescriptor, descriptorEq]
    exact (setup.position_canonicalPhysicalDescriptor_iff_ofHandedness
      (setup.nearestPosition unique) (setup.nearestPosition_marked unique) rs).mpr rsEq
  · intro canonical
    have rsEq : rs = RS.ofHandedness (setup.positionSense (setup.nearestPosition unique)
        (setup.nearestPosition_marked unique)) :=
      (setup.position_canonicalPhysicalDescriptor_iff_ofHandedness
        (setup.nearestPosition unique) (setup.nearestPosition_marked unique) rs).mp canonical
    rw [rsEq, ← descriptorEq]
    exact selectedEq

/-- **Deliverable 3 joined to the actual selection.**  For the actually selected descriptor `rb`
of a unique-nearest branch and *any* marked position `p` (deeper marked centres included), the
actual Rule-4b observation against `rb` is the physical pair class of the two independently
justified absolute auxiliary senses, and it is `like`/`unlike` exactly when the canonical
descriptor at `p` is/is not `rb`. -/
theorem nearest_selected_sourceObserve_pairClass
    (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance)
    (p : Position setup.tree) (marked : setup.PositionMarked p) {rb : RS}
    (selected : branchMarkedDescriptor input setup.c setup.frame setup.frameComputed setup.slot
      setup.singleBonded setup.acyclic setup.oAtom setup.oObserved center = some rb) :
    ∃ rp : RS,
      (setup.positionContext p marked).CanonicalPhysicalDescriptor
          (setup.positionBranch p marked) rp ∧
        rp = RS.ofHandedness (setup.positionSense p marked) ∧
          (sourceObserveRule4bLabel rb ((positionNode p).label)).pair? =
            some (physicalPairClass (setup.nearestSense unique)
              (setup.positionSense p marked)) ∧
            ((sourceObserveRule4bLabel rb ((positionNode p).label)).pair? = some .like ↔
              (setup.positionContext p marked).CanonicalPhysicalDescriptor
                (setup.positionBranch p marked) rb) ∧
              ((sourceObserveRule4bLabel rb ((positionNode p).label)).pair? = some .unlike ↔
                ¬ (setup.positionContext p marked).CanonicalPhysicalDescriptor
                  (setup.positionBranch p marked) rb) ∧
                rb = RS.ofHandedness (setup.nearestSense unique) := by
  obtain ⟨rp, _labelEq, rpDescriptor⟩ :=
    setup.exists_position_canonicalPhysicalDescriptor p marked
  have rbEq : rb = RS.ofHandedness (setup.nearestSense unique) := by
    have nearest := setup.branchMarkedDescriptor_nearestPosition unique
    have same : some rb = some (RS.ofHandedness (setup.positionSense
        (setup.nearestPosition unique) (setup.nearestPosition_marked unique))) :=
      selected.symm.trans nearest
    simpa [nearestSense] using Option.some.inj same
  have rpEq : rp = RS.ofHandedness (setup.positionSense p marked) :=
    (setup.position_canonicalPhysicalDescriptor_iff_ofHandedness p marked rp).mp rpDescriptor
  have pairEq : (sourceObserveRule4bLabel rb ((positionNode p).label)).pair? =
      some (physicalPairClass (setup.nearestSense unique)
        (setup.positionSense p marked)) := by
    rw [rbEq, setup.position_label_eq_ofHandedness p marked]
    rw [sourceObserveRule4bLabel_ofHandedness_pairClass
      (reference := setup.nearestSense unique) (observed := setup.positionSense p marked)
      (setup.nearestSense_eq_one_or_neg_one unique)
      (setup.positionSense_eq_one_or_neg_one p marked)]
    rfl
  exact ⟨rp, rpDescriptor, rpEq, pairEq,
    setup.position_sourceObserve_pair?_eq_some_like_iff p marked rb,
    setup.position_sourceObserve_pair?_eq_some_unlike_iff p marked rb, rbEq⟩

/-! ## E. The empty physical branch -/

/-- On a physically empty branch the actual prior references are `[]`, the single actual prior
reading reads `none`, and every position is unmarked with pair observation `none`. -/
theorem emptyBranch_referenceMeaning (setup : ActualSlotPhysicalSetup input)
    (empty : setup.NoPhysicalMarkedBranch) :
    localizedRule4bReferencesFromRankedLabels setup.key.prior.rule4aKey.rankedLabels = [] ∧
      setup.key.prior.references = [] ∧
        (∃ reading : input.certified.LocalizedRerootRule4bcReading,
          setup.key.prior.readings = [reading] ∧ reading.reference? = none) ∧
          (∀ p : Position setup.tree, ¬ setup.PositionMarked p) ∧
            (∀ (p : Position setup.tree) (reference : RS),
              (sourceObserveRule4bLabel reference ((positionNode p).label)).pair? = none) := by
  obtain ⟨rankedEmpty, refsEmpty, reading, readingsEq, refNone⟩ :=
    TetraStereo.OneCenter.physical_empty_selected_references setup empty
  refine ⟨rankedEmpty, refsEmpty, ⟨reading, readingsEq, refNone⟩, ?_, ?_⟩
  · intro p marked
    exact empty _ (setup.position_atom_mem_cutBranch p) marked
  · intro p reference
    exact setup.position_sourceObserve_pair?_eq_none p
      (fun marked => empty _ (setup.position_atom_mem_cutBranch p) marked) reference

/-! ## F. The joined meaning package -/

















structure CanonicalPhysicalReferenceMeaning (setup : ActualSlotPhysicalSetup input)
    (branchDomain : PhysicalBranchDomain input setup.root setup.oAtom) : Prop where

  closure : setup.PhysicalReferenceObservationClosure branchDomain
  /-- Actual label iff canonical physical descriptor at the same marked position. -/
  label_iff : ∀ (p : Position setup.tree) (marked : setup.PositionMarked p) (rs : RS),
    (positionNode p).label = some (.chiral rs) ↔
      (setup.positionContext p marked).CanonicalPhysicalDescriptor
        (setup.positionBranch p marked) rs
  /-- Actual generated reader state iff canonical physical descriptor at the same marked
  position. -/
  state_iff : ∀ (p : Position setup.tree) (marked : setup.PositionMarked p) (rs : RS),
    LocalizedUniversalReference.referenceState input (positionSource p).occurrence =
        some (.chiral rs) ↔
      (setup.positionContext p marked).CanonicalPhysicalDescriptor
        (setup.positionBranch p marked) rs
  /-- Every marked position actually carries a canonical physical descriptor. -/
  existsDescriptor : ∀ (p : Position setup.tree) (marked : setup.PositionMarked p),
    ∃ rs : RS,
      (positionNode p).label = some (.chiral rs) ∧
        (setup.positionContext p marked).CanonicalPhysicalDescriptor
          (setup.positionBranch p marked) rs
  /-- The canonical descriptor at a marked position is unique. -/
  descriptor_unique : ∀ (p : Position setup.tree) (marked : setup.PositionMarked p)
      {first second : RS},
    (setup.positionContext p marked).CanonicalPhysicalDescriptor
        (setup.positionBranch p marked) first →
      (setup.positionContext p marked).CanonicalPhysicalDescriptor
        (setup.positionBranch p marked) second → first = second
  /-- Unmarked positions retain the actual `none`/absence/pair-none facts. -/
  unmarked : ∀ (p : Position setup.tree), ¬ setup.PositionMarked p →
    LocalizedUniversalReference.referenceState input (positionSource p).occurrence = none ∧
      (positionNode p).label = none ∧
        chiralDescriptorOfLabel ((positionNode p).label) = none ∧
          (∀ reference : RS,
            (sourceObserveRule4bLabel reference ((positionNode p).label)).pair? = none)
  /-- Actual Rule-4b `like` iff the canonical descriptor at the marked position is the reference. -/
  like_iff : ∀ (p : Position setup.tree) (marked : setup.PositionMarked p) (reference : RS),
    (sourceObserveRule4bLabel reference ((positionNode p).label)).pair? = some .like ↔
      (setup.positionContext p marked).CanonicalPhysicalDescriptor
        (setup.positionBranch p marked) reference
  /-- Actual Rule-4b `unlike` iff the canonical descriptor at the marked position is not the
  reference. -/
  unlike_iff : ∀ (p : Position setup.tree) (marked : setup.PositionMarked p) (reference : RS),
    (sourceObserveRule4bLabel reference ((positionNode p).label)).pair? = some .unlike ↔
      ¬ (setup.positionContext p marked).CanonicalPhysicalDescriptor
        (setup.positionBranch p marked) reference
  /-- Empty branch: actual prior references are `[]` and the single actual reading is `none`. -/
  empty_references : setup.NoPhysicalMarkedBranch →
    setup.key.prior.references = [] ∧
      ∃ reading : input.certified.LocalizedRerootRule4bcReading,
        setup.key.prior.readings = [reading] ∧ reading.reference? = none
  /-- The physical branch is empty or has a unique nearest marked centre. -/
  branch_cases : setup.NoPhysicalMarkedBranch ∨
    ∃ (center : input.certified.Atom) (distance : Nat),
      PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance
  /-- Unique nearest: actual references are `[rs]` iff the nearest canonical descriptor is `rs`. -/
  nearest_references_iff : ∀ {center : input.certified.Atom} {distance : Nat}
      (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance)
      (rs : RS),
    setup.key.prior.references = [rs] ↔
      (setup.nearestContext unique).CanonicalPhysicalDescriptor (setup.nearestBranch unique) rs
  /-- Unique nearest: actual selected descriptor, actual reference/reading singletons and the
  canonical descriptor at the nearest position all coincide, and the selected centre is the
  nearest actual position. -/
  nearest_selected : ∀ {center : input.certified.Atom} {distance : Nat}
      (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance),
    ∃ descriptor : RS,
      branchMarkedDescriptor input setup.c setup.frame setup.frameComputed setup.slot
          setup.singleBonded setup.acyclic setup.oAtom setup.oObserved center = some descriptor ∧
        setup.key.prior.references = [descriptor] ∧
          (∃ reading : input.certified.LocalizedRerootRule4bcReading,
            setup.key.prior.readings = [reading] ∧ reading.reference? = some descriptor) ∧
            descriptor = RS.ofHandedness (setup.nearestSense unique) ∧
              (setup.nearestContext unique).CanonicalPhysicalDescriptor
                (setup.nearestBranch unique) descriptor ∧
                positionAtom setup.singleBonded setup.acyclic
                  (setup.nearestPosition unique) = center
  /-- Unique nearest, pointwise: the actual selected reference reads Rule-4b against any marked
  position according to canonical agreement, with the physical pair class of the independent
  absolute auxiliary senses.  Deeper marked centres are unrestricted. -/
  nearest_pointwise : ∀ {center : input.certified.Atom} {distance : Nat}
      (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance),
    ∃ rb : RS,
      branchMarkedDescriptor input setup.c setup.frame setup.frameComputed setup.slot
          setup.singleBonded setup.acyclic setup.oAtom setup.oObserved center = some rb ∧
        setup.key.prior.references = [rb] ∧
          (setup.nearestContext unique).CanonicalPhysicalDescriptor (setup.nearestBranch unique) rb ∧
            ∀ (p : Position setup.tree) (marked : setup.PositionMarked p),
              ∃ rp : RS,
                (setup.positionContext p marked).CanonicalPhysicalDescriptor
                    (setup.positionBranch p marked) rp ∧
                  rp = RS.ofHandedness (setup.positionSense p marked) ∧
                    (sourceObserveRule4bLabel rb ((positionNode p).label)).pair? =
                      some (physicalPairClass (setup.nearestSense unique)
                        (setup.positionSense p marked)) ∧
                      ((sourceObserveRule4bLabel rb ((positionNode p).label)).pair? =
                          some .like ↔
                        (setup.positionContext p marked).CanonicalPhysicalDescriptor
                          (setup.positionBranch p marked) rb) ∧
                        ((sourceObserveRule4bLabel rb ((positionNode p).label)).pair? =
                            some .unlike ↔
                          ¬ (setup.positionContext p marked).CanonicalPhysicalDescriptor
                            (setup.positionBranch p marked) rb)



theorem canonicalPhysicalReferenceMeaning_core (setup : ActualSlotPhysicalSetup input)
    (branchDomain : PhysicalBranchDomain input setup.root setup.oAtom)
    (closure : setup.PhysicalReferenceObservationClosure branchDomain) :
    setup.CanonicalPhysicalReferenceMeaning branchDomain where
  closure := closure
  label_iff := fun p marked rs =>
    setup.position_label_iff_canonicalPhysicalDescriptor p marked rs
  state_iff := fun p marked rs =>
    setup.position_referenceState_iff_canonicalPhysicalDescriptor p marked rs
  existsDescriptor := fun p marked =>
    setup.exists_position_canonicalPhysicalDescriptor p marked
  descriptor_unique := fun p marked _first _second left right =>
    setup.position_canonicalPhysicalDescriptor_unique p marked left right
  unmarked := fun p notMarked =>
    ⟨setup.position_referenceState_eq_none_of_not_marked p notMarked,
      setup.position_label_eq_none_of_not_marked p notMarked,
      setup.position_chiralDescriptorOfLabel_eq_none_of_not_marked p notMarked,
      fun reference => setup.position_sourceObserve_pair?_eq_none p notMarked reference⟩
  like_iff := fun p marked reference =>
    setup.position_sourceObserve_pair?_eq_some_like_iff p marked reference
  unlike_iff := fun p marked reference =>
    setup.position_sourceObserve_pair?_eq_some_unlike_iff p marked reference
  empty_references := fun empty => by
    obtain ⟨_ranked, refs, readingData, _unmarked, _pairs⟩ :=
      setup.emptyBranch_referenceMeaning empty
    exact ⟨refs, readingData⟩
  branch_cases := (physicalBranchDomain_iff_empty_or_unique setup).mp branchDomain
  nearest_references_iff := fun unique rs =>
    setup.nearest_references_iff_canonicalPhysicalDescriptor unique rs
  nearest_selected := fun unique => by
    obtain ⟨descriptor, markedEq, _ranked, refs, readingData, senseEq, canonical, atomEq⟩ :=
      setup.nearest_selected_singleton unique
    exact ⟨descriptor, markedEq, refs, readingData, senseEq, canonical, atomEq⟩
  nearest_pointwise := fun unique => by
    obtain ⟨rb, markedEq, _ranked, refs, _readingData, _senseEq, canonical, _atomEq⟩ :=
      setup.nearest_selected_singleton unique
    refine ⟨rb, markedEq, refs, canonical, ?_⟩
    intro p marked
    obtain ⟨rp, rpDescriptor, rpEq, pairEq, likeIff, unlikeIff, _rbEq⟩ :=
      setup.nearest_selected_sourceObserve_pairClass unique p marked markedEq
    exact ⟨rp, rpDescriptor, rpEq, pairEq, likeIff, unlikeIff⟩



theorem canonicalPhysicalReferenceMeaning (setup : ActualSlotPhysicalSetup input)
    (branchDomain : PhysicalBranchDomain input setup.root setup.oAtom) :
    setup.CanonicalPhysicalReferenceMeaning branchDomain :=
  setup.canonicalPhysicalReferenceMeaning_core branchDomain
    (setup.physicalReferenceObservation_closure branchDomain)

end ActualSlotPhysicalSetup

/-! ## G. Original-input facade -/

/-- **Deliverable 4.**  From the actual certified graph, the detected root `c`, the original
configuration and original general-rigid physical domain, an actually adjacent branch atom and a
physical branch domain, derive an actual slot setup indexed by those exact original inputs and the
joined canonical physical selected-reference meaning at that setup.  No frame success, supplied
order, desired letter or assumed reader value is an input; general-rigid or terminal-twin
alternatives, arbitrary depth, the empty and unique-nearest branch cases and the constant-charge
and no-double-bond side conditions are all explicit. -/
theorem canonicalPhysicalReferenceMeaning_of_physical
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (oAtom : input.certified.Atom)
    (adjacent : input.certified.moleculeGraph.Adj c.1 oAtom)
    (branchDomain : PhysicalBranchDomain input c oAtom) :
    ∃ setup : ActualSlotPhysicalSetupOf input c cfg physicalDomain oAtom,
      ActualSlotPhysicalSetup.CanonicalPhysicalReferenceMeaning setup.toSetup branchDomain := by
  obtain ⟨setup, closure⟩ := physicalReferenceObservation_closure_of_physical input c
    singleBonded acyclic hcharge noDouble cfg physicalDomain oAtom adjacent branchDomain
  exact ⟨setup, ActualSlotPhysicalSetup.canonicalPhysicalReferenceMeaning_core
    setup.toSetup branchDomain closure⟩

/-! ## H. Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_referenceState_iff_canonicalPhysicalDescriptor
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_label_iff_canonicalPhysicalDescriptor
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_canonicalPhysicalDescriptor_iff_ofHandedness
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_canonicalPhysicalDescriptor_ofHandedness
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.exists_position_canonicalPhysicalDescriptor
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_canonicalPhysicalDescriptor_unique
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_referenceState_eq_none_of_not_marked
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_label_eq_none_of_not_marked
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_chiralDescriptorOfLabel_eq_none_of_not_marked
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_sourceObserve_pair?_eq_of_canonicalDescriptor
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_sourceObserve_pair?_eq_some_like_iff
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_sourceObserve_pair?_eq_some_unlike_iff
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestContext
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestBranch
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestSense
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestSense_eq_one_or_neg_one
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestContext_target_root
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearest_selected_singleton
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearest_references_iff_canonicalPhysicalDescriptor
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearest_selected_sourceObserve_pairClass
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.emptyBranch_referenceMeaning
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.CanonicalPhysicalReferenceMeaning
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.canonicalPhysicalReferenceMeaning_core
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.canonicalPhysicalReferenceMeaning
assert_kernel_only TetraStereo.OneCenter.canonicalPhysicalReferenceMeaning_of_physical

end TetraStereo.OneCenter
