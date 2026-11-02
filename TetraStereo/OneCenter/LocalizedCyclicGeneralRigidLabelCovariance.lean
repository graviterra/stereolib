import TetraStereo.OneCenter.LocalizedCyclicGeneralRigidGeneratedLabels
import TetraStereo.OneCenter.LocalizedRetainedGeneratedCovariance
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-!
# Physical covariance of actual rigid auxiliary labels under one molecular automorphism

One molecular automorphism `e` maps a carrier occurrence `t`, with its outer root, address and
full history, to `u = transportOccurrence e t`. This module derives the actual generated labels
at both occurrences and relates them through the physical configuration. It never assumes
whole-state equality, a selected reference, or a reader correspondence.

## Constitutional covariance

`declarative_observable_transport` is new and needs no acyclicity. For a root-aligned cursor, a
declarative constitutional derivation at the cursor and one at its transported cursor have equal
Rule-1a/1b/2 tables. The fuels are independent. The proof is by fuel induction:

* Root keys: `e` preserves `Z`, mass, provenance and depth (`rootKey_observable_transport`).
* Children: the transported executable children are a permutation of the image's children
  (`executableLocalizedRerootChildren_transport_perm`). Each child is again root-aligned.
* Tied siblings may sort differently, but their observable sequences agree
  (`constitutional_observables_eq_of_perm`).

Reader independence turns this into `ruleMajorBuild_compare_transport`: any successful builds,
at any stages, readers and fuels, compare equally at the source and image cursor pairs.

## Frame transport

The actual frames are related by the actual executable-list slot permutation `slotPerm`
(`actualFrameSlotTransport`). Source strictness gives image strictness. The image's contextual
priority permutation is `slotPerm * τ`, by the uniqueness of `priorityOrder`. The detected ligand
permutations satisfy `α' ∘ slotPerm = framePerm ∘ α`.

## Physical label law

Assume calibrated coordinates at both detected centers and the `BranchTransport` sign law at the
source center:
`configurationSign cfg d * permHandedness (ligandPermAt e d) =
  physicalMirrorFactor mirror * configurationSign cfg (e • d)`.
Then the actual image label is the actual source label (proper) or its uppercase reflection
(mirror). These physical hypotheses are explicit; the automorphism alone does not supply
coordinates or a mirror factor. `referenceState_transport_of_branchTransport` reads the sign law
from an accepted `DetectedBranchTransport` at a reached center.

At a real nonroot target in a Rule-1a tied root arm, `referenceState_transport_of_tiedRootArm`
derives the source strictness itself (`LocalizedCyclicGeneralRigidPriority`), so only the
physical calibration and sign hypotheses remain.
-/

namespace TetraStereo.OneCenter
namespace LocalizedCyclicGeneralRigidLabelCovariance

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedRuleMajorReference
open LocalizedCyclicGeneralRigidPriority
open LocalizedCyclicGeneralRigidGeneratedLabels

/-! ## Root observations -/

section Roots

variable (input : CertifiedLocalizedCIPInput) (e : input.moleculeGraph.Aut)

/-- The atom label of an official node is invariant under a molecular automorphism. -/
theorem officialNodeAtomLabel_transport (node : OfficialCIPNode input.Atom) :
    input.moleculeGraph.officialNodeAtomLabel (mapOfficialNode (e : Equiv.Perm input.Atom) node) =
      input.moleculeGraph.officialNodeAtomLabel node := by
  obtain ⟨current?, history, provenance⟩ := node
  cases current? with
  | none => simp [MoleculeGraph.officialNodeAtomLabel, mapOfficialNode]
  | some atom =>
      cases provenance <;>
        simp [MoleculeGraph.officialNodeAtomLabel, mapOfficialNode, MoleculeGraph.rawCIPAtomLabel,
          input.atomZ_transport e atom, input.atomMass_transport e atom]

/-- The Rule-1b root distance of an official node is invariant under a molecular automorphism. -/
theorem rule1bRootDistance_transport (node : OfficialCIPNode input.Atom) :
    (mapOfficialNode (e : Equiv.Perm input.Atom) node).rule1bRootDistance =
      node.rule1bRootDistance := by
  obtain ⟨current?, history, provenance⟩ := node
  cases provenance <;>
    simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.depth, mapOfficialNode]

/-- Root keys of a node and of its automorphic image have equal constitutional tables. -/
theorem rootKey_observable_transport (node : OfficialCIPNode input.Atom) (complete : Bool) :
    constitutionalObservable (input.moleculeGraph.officialRuleMajorRootKey
        (mapOfficialNode (e : Equiv.Perm input.Atom) node) complete) =
      constitutionalObservable (input.moleculeGraph.officialRuleMajorRootKey node complete) := by
  simp only [constitutionalObservable, MoleculeGraph.officialRuleMajorRootKey,
    officialNodeAtomLabel_transport input e node, rule1bRootDistance_transport input e node]

end Roots

/-! ## Constitutional derivations under one molecular automorphism -/

section Derivations

/-- Assembly with roots of equal tables and children of equal table sequences. -/
theorem assemble_observable_eq {V : Type*} (root root' : OfficialRuleMajorKey V)
    (children children' : List (OfficialRuleMajorKey V))
    (rootEq : constitutionalObservable root = constitutionalObservable root')
    (childEq : children.map constitutionalObservable = children'.map constitutionalObservable) :
    constitutionalObservable (OfficialRuleMajorKey.assemble root children) =
      constitutionalObservable (OfficialRuleMajorKey.assemble root' children') := by
  rw [assembled_constitutional_observable_eq root children children' childEq]
  have h1a := congrArg LocalizedConstitutionalObservable.rule1a rootEq
  have h1b := congrArg LocalizedConstitutionalObservable.rule1b rootEq
  have h2 := congrArg LocalizedConstitutionalObservable.rule2 rootEq
  simp only [constitutionalObservable] at h1a h1b h2
  simp only [constitutionalObservable, OfficialRuleMajorKey.assemble, h1a, h1b, h2]

private theorem map_eq_of_forall₂_pair {α β γ : Type*} (f : β → γ)
    {R S : α → β → Prop} {xs : List α} {ys zs : List β}
    (hR : List.Forall₂ R xs ys) (hS : List.Forall₂ S xs zs)
    (pointwise : ∀ x ∈ xs, ∀ y z, R x y → S x z → f y = f z) : ys.map f = zs.map f := by
  induction hR generalizing zs with
  | nil =>
      cases hS
      rfl
  | @cons x y xs ys hxy _ ih =>
      cases hS with
      | cons hxz hzs =>
          simp only [List.map_cons]
          rw [pointwise x List.mem_cons_self _ _ hxy hxz,
            ih hzs (fun x' hx' => pointwise x' (List.mem_cons_of_mem _ hx'))]

variable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}

private theorem declarativeChildren_eq_executable
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {children : List (input.LocalizedRerootCursor carrierFuel)}
    (frame : input.DeclarativeLocalizedRerootChildren cursor children) :
    children = input.executableLocalizedRerootChildren cursor :=
  Option.some.inj
    (((input.localizedRerootChildren?_eq_some_iff cursor children).mpr frame).symm.trans
      (input.localizedRerootChildren?_eq_some_executable cursor))

private theorem declarativeList_forall₂ (fuel : Nat) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys : List (OfficialRuleMajorKey input.Atom)),
      input.DeclarativeLocalizedRerootRuleMajorKeyList fuel cursors keys →
      List.Forall₂ (input.DeclarativeLocalizedRerootRuleMajorKey fuel) cursors keys
  | [], _, derived => by
      cases derived
      exact .nil
  | _ :: cursors, _, derived => by
      cases derived with
      | cons head tail => exact .cons head (declarativeList_forall₂ fuel cursors _ tail)

variable (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)

private theorem terminal_observable_transport
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (aligned : input.cursorPreviousRootAligned cursor)
    {children : List (input.LocalizedRerootCursor carrierFuel)}
    (frame : input.DeclarativeLocalizedRerootChildren cursor children) (empty : children = [])
    {fuel' : Nat} {key' : OfficialRuleMajorKey input.Atom}
    (image : input.DeclarativeLocalizedRerootRuleMajorKey fuel'
      (input.transportCursor singleBonded e cursor) key') :
    constitutionalObservable
        (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true) =
      constitutionalObservable key' := by
  have sourceExec := declarativeChildren_eq_executable input frame
  have perm := input.executableLocalizedRerootChildren_transport_perm singleBonded e aligned
  rw [← sourceExec, empty, List.map_nil] at perm
  have imageEmpty := List.nil_perm.mp perm
  generalize hImage : input.transportCursor singleBonded e cursor = imageCursor
    at image imageEmpty
  cases image with
  | terminal frame' _ =>
      subst hImage
      exact (rootKey_observable_transport input e cursor.occurrence.1.node true).symm
  | branch frame' nonempty' _ _ _ =>
      exact absurd ((declarativeChildren_eq_executable input frame').trans imageEmpty) nonempty'

/-- **Cyclic constitutional covariance.** At a root-aligned cursor, a declarative
constitutional derivation and a declarative derivation at the transported cursor have equal
Rule-1a/1b/2 tables, for arbitrary fuels. No acyclicity is used. -/
theorem declarative_observable_transport :
    ∀ (fuel fuel' : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key key' : OfficialRuleMajorKey input.Atom),
      input.cursorPreviousRootAligned cursor →
      input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key →
      input.DeclarativeLocalizedRerootRuleMajorKey fuel'
        (input.transportCursor singleBonded e cursor) key' →
      constitutionalObservable key = constitutionalObservable key' := by
  intro fuel
  induction fuel with
  | zero =>
      intro fuel' cursor key key' aligned source image
      cases source with
      | terminal frame empty =>
          exact terminal_observable_transport input singleBonded e aligned frame empty image
  | succ fuel ih =>
      intro fuel' cursor key key' aligned source image
      cases source with
      | terminal frame empty =>
          exact terminal_observable_transport input singleBonded e aligned frame empty image
      | branch frame nonempty childDerivations ranking descending =>
          have sourceExec := declarativeChildren_eq_executable input frame
          have perm := input.executableLocalizedRerootChildren_transport_perm singleBonded e
            aligned
          rw [← sourceExec] at perm
          have childAligned : ∀ child ∈ _, input.cursorPreviousRootAligned child :=
            fun child present => input.executableLocalizedRerootChildren_cursorAligned cursor
              child (sourceExec ▸ present)
          generalize hImage : input.transportCursor singleBonded e cursor = imageCursor
            at image perm
          cases image with
          | terminal frame' empty' =>
              have imageExec := declarativeChildren_eq_executable input frame'
              rw [← imageExec, empty'] at perm
              exact absurd (List.map_eq_nil_iff.mp (List.perm_nil.mp perm)) nonempty
          | branch frame' _ childDerivations' ranking' descending' =>
              subst hImage
              have imageExec := declarativeChildren_eq_executable input frame'
              rw [← imageExec] at perm
              have sourceForall := declarativeList_forall₂ input fuel _ _ childDerivations
              have imageForall := declarativeList_forall₂ input _ _ _ childDerivations'
              obtain ⟨middle, middleForall, middlePerm⟩ :=
                List.perm_comp_forall₂ perm imageForall
              have middleForall' := List.forall₂_map_left_iff.mp middleForall
              have middleEq := map_eq_of_forall₂_pair constitutionalObservable sourceForall
                middleForall' (fun child present key key' derived derived' =>
                  ih _ child key key' (childAligned child present) derived derived')
              have childPerm := (List.Perm.of_eq middleEq).trans
                (middlePerm.map constitutionalObservable)
              have sortedPerm := (ranking.map constitutionalObservable).trans
                (childPerm.trans (ranking'.map constitutionalObservable).symm)
              exact assemble_observable_eq _ _ _ _
                (rootKey_observable_transport input e cursor.occurrence.1.node false).symm
                (constitutional_observables_eq_of_perm _ _ sortedPerm descending descending')

omit singleBonded e in
/-- A successful rule-major build is a declarative constitutional derivation at its fuel. -/
theorem ruleMajorBuild_declarative {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {cursor : input.LocalizedRerootCursor carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (built : input.buildRuleMajorCumulativeWithRead? stage read fuel cursor = some key) :
    input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key.constitutional := by
  obtain ⟨tree, source, trace⟩ :=
    exists_ruleMajorTrace_of_buildWithRead input stage read fuel cursor key built
  have derived :=
    RetainedConstitutionalReaderIndependence.ruleMajorSortTrace_constitutional_declarative
      fuel trace
  rw [source] at derived
  exact derived

/-- Builds at a root-aligned cursor and at its transported cursor have equal constitutional
tables, for arbitrary stages, readers and fuels. -/
theorem ruleMajorBuild_observable_transport
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (aligned : input.cursorPreviousRootAligned cursor)
    {stage stage' : LocalizedCumulativeRule45Stage}
    {read read' : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel fuel' : Nat} {key key' : input.LocalizedRerootCumulativeRule45Key}
    (built : input.buildRuleMajorCumulativeWithRead? stage read fuel cursor = some key)
    (built' : input.buildRuleMajorCumulativeWithRead? stage' read' fuel'
      (input.transportCursor singleBonded e cursor) = some key') :
    constitutionalObservable key.constitutional = constitutionalObservable key'.constitutional :=
  declarative_observable_transport input singleBonded e fuel fuel' cursor _ _ aligned
    (ruleMajorBuild_declarative input built) (ruleMajorBuild_declarative input built')

/-- Constitutional comparisons of root-aligned cursor pairs are invariant under transport. -/
theorem ruleMajorBuild_compare_transport
    {left right : input.LocalizedRerootCursor carrierFuel}
    (alignedL : input.cursorPreviousRootAligned left)
    (alignedR : input.cursorPreviousRootAligned right)
    {stageL stageR stageL' stageR' : LocalizedCumulativeRule45Stage}
    {readL readR readL' readR' :
      input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuelL fuelR fuelL' fuelR' : Nat}
    {keyL keyR keyL' keyR' : input.LocalizedRerootCumulativeRule45Key}
    (builtL : input.buildRuleMajorCumulativeWithRead? stageL readL fuelL left = some keyL)
    (builtR : input.buildRuleMajorCumulativeWithRead? stageR readR fuelR right = some keyR)
    (builtL' : input.buildRuleMajorCumulativeWithRead? stageL' readL' fuelL'
      (input.transportCursor singleBonded e left) = some keyL')
    (builtR' : input.buildRuleMajorCumulativeWithRead? stageR' readR' fuelR'
      (input.transportCursor singleBonded e right) = some keyR') :
    OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional =
      OfficialRuleMajorKey.compare keyL'.constitutional keyR'.constitutional :=
  ruleMajor_compare_congr _ _ _ _
    (ruleMajorBuild_observable_transport input singleBonded e alignedL builtL builtL')
    (ruleMajorBuild_observable_transport input singleBonded e alignedR builtR builtR')

/-- Constitutional separation transports along the automorphism. -/
theorem constitutionallySeparated_transport
    {left right : input.LocalizedRerootCursor carrierFuel}
    (alignedL : input.cursorPreviousRootAligned left)
    (alignedR : input.cursorPreviousRootAligned right)
    (validL : input.LocalizedRerootCursorValid left)
    (validR : input.LocalizedRerootCursorValid right)
    (separated : ConstitutionallySeparated left right) :
    ConstitutionallySeparated (input.transportCursor singleBonded e left)
      (input.transportCursor singleBonded e right) := by
  intro stageL stageR readL readR fuelL fuelR keyL keyR builtL builtR
  obtain ⟨sourceL, sourceBuiltL⟩ := input.exists_buildRuleMajorCumulativeWithRead_at_twice
    .rule4a (fun _ => none) left validL
  obtain ⟨sourceR, sourceBuiltR⟩ := input.exists_buildRuleMajorCumulativeWithRead_at_twice
    .rule4a (fun _ => none) right validR
  rw [← ruleMajorBuild_compare_transport input singleBonded e alignedL alignedR sourceBuiltL
    sourceBuiltR builtL builtR]
  exact separated _ _ _ _ _ _ _ _ sourceBuiltL sourceBuiltR

/-- The constitutional above relation transports along the automorphism. -/
theorem constitutionallyAbove_transport
    {left right : input.LocalizedRerootCursor carrierFuel}
    (alignedL : input.cursorPreviousRootAligned left)
    (alignedR : input.cursorPreviousRootAligned right)
    (validL : input.LocalizedRerootCursorValid left)
    (validR : input.LocalizedRerootCursorValid right)
    (above : ConstitutionallyAbove left right) :
    ConstitutionallyAbove (input.transportCursor singleBonded e left)
      (input.transportCursor singleBonded e right) := by
  intro stageL stageR readL readR fuelL fuelR keyL keyR builtL builtR
  obtain ⟨sourceL, sourceBuiltL⟩ := input.exists_buildRuleMajorCumulativeWithRead_at_twice
    .rule4a (fun _ => none) left validL
  obtain ⟨sourceR, sourceBuiltR⟩ := input.exists_buildRuleMajorCumulativeWithRead_at_twice
    .rule4a (fun _ => none) right validR
  rw [← ruleMajorBuild_compare_transport input singleBonded e alignedL alignedR sourceBuiltL
    sourceBuiltR builtL builtR]
  exact above _ _ _ _ _ _ _ _ sourceBuiltL sourceBuiltR

end Derivations

/-! ## The transported occurrence -/

/-- The image occurrence of a real occurrence is real. -/
theorem transportOccurrence_real (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut) (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    (input.certified.transportOccurrence singleBonded e target).1.node.provenance =
      OfficialCIPNodeProvenance.realAtom :=
  (input.certified.transportOccurrence_provenance singleBonded e target).trans real

/-- The transported detected unit is the unit of the transported occurrence. -/
theorem transportOccurrence_unit (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut) (target : Occurrence input)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1) :
    input.certified.molecularFrameUnit
        (input.certified.transportOccurrence singleBonded e target).1 =
      (input.certified.transportDetectedOccurrence e unit).1 := by
  rw [input.certified.molecularFrameUnit_transport singleBonded e target, targetUnit]
  rfl

/-! ## Actual frames at a transported occurrence -/

section Frames

variable {input : Input} (singleBonded : input.certified.moleculeGraph.SimpleBonded)
  (e : input.certified.moleculeGraph.Aut)
  {target : Occurrence input} {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
  (frames : ContextFrameCompilation input target unit targetUnit)
  {imageUnit : DetectedOccurrence input.certified.moleculeGraph}
  {imageTargetUnit : input.certified.molecularFrameUnit
    (input.certified.transportOccurrence singleBonded e target).1 = imageUnit.1}
  (imageFrames : ContextFrameCompilation input
    (input.certified.transportOccurrence singleBonded e target) imageUnit imageTargetUnit)

/-- The actual slot transport at the compiled frame's detected center. -/
noncomputable def slotTransport :
    input.certified.ActualFrameSlotTransport singleBonded e target frames.center :=
  input.certified.actualFrameSlotTransport singleBonded e
    (CertifiedLocalizedCIPInput.globalCarrierFuel_adequate input) target frames.center
    ((input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target
      frames.center).mp frames.centerComputed)

theorem slotTransport_sourceFrame :
    (slotTransport singleBonded e frames).sourceFrame = frames.frame :=
  Option.some.inj ((slotTransport singleBonded e frames).sourceComputed.symm.trans
    (frame_computed frames))

theorem slotTransport_imageFrame :
    (slotTransport singleBonded e frames).imageFrame = imageFrames.frame :=
  Option.some.inj ((slotTransport singleBonded e frames).imageComputed.symm.trans
    (frame_computed imageFrames))

/-- The image frame slot `slotPerm i` holds the transported source cursor at slot `i`. -/
theorem image_cursorAt (i : Fin 4) :
    imageFrames.frame.cursorAt ((slotTransport singleBonded e frames).slotPerm i) =
      input.certified.transportCursor singleBonded e (frames.frame.cursorAt i) := by
  have transported := (slotTransport singleBonded e frames).cursorAt_eq i
  rw [slotTransport_sourceFrame singleBonded e frames,
    slotTransport_imageFrame singleBonded e frames imageFrames] at transported
  exact transported

omit singleBonded e in
theorem frames_cursor_aligned (i : Fin 4) :
    input.certified.cursorPreviousRootAligned (frames.frame.cursorAt i) :=
  input.certified.executableLocalizedRerootChildren_cursorAligned _ _ (frames.childAt i)

omit singleBonded e in
theorem frames_cursor_valid (i : Fin 4) :
    input.certified.LocalizedRerootCursorValid (frames.frame.cursorAt i) :=
  input.certified.frameCursor_valid target frames.frame (frame_computed frames) i

/-- Source strictness gives image strictness. -/
theorem image_strict (strict : FrameConstitutionalStrict frames.frame) :
    FrameConstitutionalStrict imageFrames.frame := by
  intro left right distinct
  obtain ⟨i, rfl⟩ := (slotTransport singleBonded e frames).slotPerm.surjective left
  obtain ⟨j, rfl⟩ := (slotTransport singleBonded e frames).slotPerm.surjective right
  have sourceDistinct : i ≠ j := fun same => distinct (by rw [same])
  rw [image_cursorAt singleBonded e frames imageFrames i,
    image_cursorAt singleBonded e frames imageFrames j]
  exact constitutionallySeparated_transport input.certified singleBonded e
    (frames_cursor_aligned frames i) (frames_cursor_aligned frames j)
    (frames_cursor_valid frames i) (frames_cursor_valid frames j) (strict i j sourceDistinct)

/-- **The image contextual priority permutation** is the source one followed by the actual
slot permutation. -/
theorem image_priorityOrder (strict : FrameConstitutionalStrict frames.frame) :
    priorityOrder imageFrames (image_strict singleBonded e frames imageFrames strict)
        singleBonded =
      (slotTransport singleBonded e frames).slotPerm * priorityOrder frames strict singleBonded := by
  symm
  apply priorityOrder_unique imageFrames (image_strict singleBonded e frames imageFrames strict)
    singleBonded
  intro p q lower
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    image_cursorAt singleBonded e frames imageFrames, image_cursorAt singleBonded e frames imageFrames]
  exact constitutionallyAbove_transport input.certified singleBonded e
    (frames_cursor_aligned frames _) (frames_cursor_aligned frames _)
    (frames_cursor_valid frames _) (frames_cursor_valid frames _)
    (priorityOrder_above frames strict singleBonded lower)

/-- The image compilation's detected center is the transported center. -/
theorem image_center_val :
    imageFrames.center.1 = (e : Equiv.Perm input.certified.Atom) frames.center.1 := by
  have imageMeaning := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _
    imageFrames.center).mp imageFrames.centerComputed
  have sourceMeaning := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target
    frames.center).mp frames.centerComputed
  have current := imageMeaning.2
  rw [transportOccurrence_node] at current
  simp only [mapOfficialNode, sourceMeaning.2, Option.map_some, Option.some.injEq] at current
  exact current.symm

/-- The image compilation's detected center, as a center of the detected molecule. -/
theorem image_center :
    (imageFrames.center : input.certified.detectedMultiCenterMolecule.Center) =
      input.certified.physicalImageCenter e frames.center := by
  apply Subtype.ext
  rw [input.certified.physicalImageCenter_eq e frames.center]
  exact image_center_val singleBonded e frames imageFrames

/-- The detected ligand permutations satisfy `α' ∘ slotPerm = framePerm ∘ α`. -/
theorem image_detectedLigandPermutation (i : Fin 4) :
    imageFrames.detectedLigandPermutation ((slotTransport singleBonded e frames).slotPerm i) =
      input.certified.framePerm e frames.center.1 (input.certified.sourceTetra frames.center)
        (frames.detectedLigandPermutation i) := by
  apply input.certified.detectedMultiCenterMolecule.ligandAtomAt_injective
    (input.certified.physicalImageCenter e frames.center)
  have imageAt := imageFrames.ligandAt ((slotTransport singleBonded e frames).slotPerm i)
  rw [image_cursorAt singleBonded e frames imageFrames i, transportCursor_occurrence,
    transportOccurrence_node] at imageAt
  have sourceAt := frames.ligandAt i
  simp only [mapOfficialNode, sourceAt, Option.map_some, Option.some.injEq] at imageAt
  rw [input.certified.framePerm_ligandAtom_transport e frames.center
    (frames.detectedLigandPermutation i), ← image_center singleBonded e frames imageFrames]
  exact imageAt.symm

/-- Parity form of the ligand-permutation law. -/
theorem image_detectedLigandPermutation_handedness :
    permHandedness imageFrames.detectedLigandPermutation *
        permHandedness (slotTransport singleBonded e frames).slotPerm =
      permHandedness (input.certified.framePerm e frames.center.1
          (input.certified.sourceTetra frames.center)) *
        permHandedness frames.detectedLigandPermutation := by
  have composed : imageFrames.detectedLigandPermutation *
      (slotTransport singleBonded e frames).slotPerm =
      input.certified.framePerm e frames.center.1 (input.certified.sourceTetra frames.center) *
        frames.detectedLigandPermutation := by
    apply Equiv.ext
    intro i
    exact image_detectedLigandPermutation singleBonded e frames imageFrames i
  rw [← permHandedness_mul, ← permHandedness_mul, composed]

/-! ## Physical label law -/

private theorem product_unit (σ τ ρ : Equiv.Perm (Fin 4)) :
    permHandedness σ * permHandedness τ * permHandedness ρ = 1 ∨
      permHandedness σ * permHandedness τ * permHandedness ρ = -1 := by
  rw [← permHandedness_mul, ← permHandedness_mul]
  exact permHandedness_eq_one_or_eq_neg_one _

include imageFrames in
/-- **Actual rigid label covariance under one molecular automorphism.** Assume the source frame
is constitutionally strict, both detected centers are calibrated in the physical configuration
`cfg`, and the `BranchTransport` sign law holds at the source center. Then the actual generated
states at the source occurrence and at its transported occurrence are uppercase. The image letter
is the source letter, or its reflection when `mirror` holds. -/
theorem referenceState_transport_of_calibrated
    (strict : FrameConstitutionalStrict frames.frame)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration) (mirror : Bool)
    (sourceCalibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center)
    (imageCalibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg
        (input.certified.physicalImageCenter e frames.center))
    (signLaw : input.certified.detectedMultiCenterMolecule.configurationSign cfg
          (input.certified.physicalSourceCenter frames.center) *
        permHandedness (input.certified.detectedMultiCenterMolecule.ligandPermAt
          (input.certified.physicalDetectedAut e)
          (input.certified.physicalSourceCenter frames.center)) =
      physicalMirrorFactor mirror *
        input.certified.detectedMultiCenterMolecule.configurationSign cfg
          (input.certified.detectedMultiCenterMolecule.centerPerm
            (input.certified.physicalDetectedAut e)
            (input.certified.physicalSourceCenter frames.center))) :
    ∃ raw : RS, referenceState input target = some (.chiral raw) ∧
      referenceState input (input.certified.transportOccurrence singleBonded e target) =
        some (.chiral (if mirror then RS.swap raw else raw)) := by
  have imageStrict := image_strict singleBonded e frames imageFrames strict
  have imageCalibrated' : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg imageFrames.center := by
    rw [image_center singleBonded e frames imageFrames]
    exact imageCalibrated
  have source := referenceState_eq_chiral_of_calibrated frames strict singleBonded cfg
    sourceCalibrated
  have image := referenceState_eq_chiral_of_calibrated imageFrames imageStrict singleBonded cfg
    imageCalibrated'
  -- The image configuration sign, from the sign law and `framePerm = ligandPermAt`.
  have imageSign : input.certified.detectedMultiCenterMolecule.configurationSign cfg imageFrames.center =
      physicalMirrorFactor mirror * input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
        permHandedness (input.certified.framePerm e frames.center.1
          (input.certified.sourceTetra frames.center)) := by
    have turned := configurationSign_image_of_branchSign
      input.certified.detectedMultiCenterMolecule (input.certified.physicalDetectedAut e) cfg mirror
      (input.certified.physicalSourceCenter frames.center) signLaw
    rw [← input.certified.framePerm_eq_ligandPermAt e frames.center] at turned
    rw [image_center singleBonded e frames imageFrames]
    exact turned
  have priority := image_priorityOrder singleBonded e frames imageFrames strict
  have ligands := image_detectedLigandPermutation_handedness singleBonded e frames imageFrames
  have square := permHandedness_mul_self (input.certified.framePerm e frames.center.1
    (input.certified.sourceTetra frames.center))
  have product : input.certified.detectedMultiCenterMolecule.configurationSign cfg imageFrames.center *
        permHandedness imageFrames.detectedLigandPermutation *
        permHandedness (priorityOrder imageFrames imageStrict singleBonded) =
      physicalMirrorFactor mirror * (input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
        permHandedness frames.detectedLigandPermutation *
        permHandedness (priorityOrder frames strict singleBonded)) := by
    rw [imageSign, priority, permHandedness_mul]
    calc
      physicalMirrorFactor mirror * input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
            permHandedness (input.certified.framePerm e frames.center.1
              (input.certified.sourceTetra frames.center)) *
            permHandedness imageFrames.detectedLigandPermutation *
            (permHandedness (slotTransport singleBonded e frames).slotPerm *
              permHandedness (priorityOrder frames strict singleBonded))
          = physicalMirrorFactor mirror * input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
              permHandedness (input.certified.framePerm e frames.center.1
                (input.certified.sourceTetra frames.center)) *
              (permHandedness imageFrames.detectedLigandPermutation *
                permHandedness (slotTransport singleBonded e frames).slotPerm) *
              permHandedness (priorityOrder frames strict singleBonded) := by ring
      _ = physicalMirrorFactor mirror * input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
              permHandedness (input.certified.framePerm e frames.center.1
                (input.certified.sourceTetra frames.center)) *
              (permHandedness (input.certified.framePerm e frames.center.1
                  (input.certified.sourceTetra frames.center)) *
                permHandedness frames.detectedLigandPermutation) *
              permHandedness (priorityOrder frames strict singleBonded) := by rw [ligands]
      _ = physicalMirrorFactor mirror * input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
              (permHandedness (input.certified.framePerm e frames.center.1
                  (input.certified.sourceTetra frames.center)) *
                permHandedness (input.certified.framePerm e frames.center.1
                  (input.certified.sourceTetra frames.center))) *
              permHandedness frames.detectedLigandPermutation *
              permHandedness (priorityOrder frames strict singleBonded) := by ring
      _ = physicalMirrorFactor mirror * (input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
            permHandedness frames.detectedLigandPermutation *
            permHandedness (priorityOrder frames strict singleBonded)) := by
          rw [square]
          ring
  refine ⟨_, source, ?_⟩
  rw [image, product]
  have unit := product_unit (cfg frames.center) frames.detectedLigandPermutation
    (priorityOrder frames strict singleBonded)
  change permHandedness (cfg frames.center) * _ * _ = 1 ∨
      permHandedness (cfg frames.center) * _ * _ = -1 at unit
  cases mirror with
  | false =>
      simp [physicalMirrorFactor]
  | true =>
      rcases unit with one | negOne
      · have one' : input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
            permHandedness frames.detectedLigandPermutation *
            permHandedness (priorityOrder frames strict singleBonded) = 1 := one
        rw [one']
        norm_num [physicalMirrorFactor, RS.swap]
      · have negOne' : input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
            permHandedness frames.detectedLigandPermutation *
            permHandedness (priorityOrder frames strict singleBonded) = -1 := negOne
        rw [negOne']
        norm_num [physicalMirrorFactor, RS.swap]

include imageFrames in
/-- The same law in label-map form: the image state is the source state, or its uppercase
reflection. -/
theorem referenceState_transport_eq_reflect
    (strict : FrameConstitutionalStrict frames.frame)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration) (mirror : Bool)
    (sourceCalibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center)
    (imageCalibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg
        (input.certified.physicalImageCenter e frames.center))
    (signLaw : input.certified.detectedMultiCenterMolecule.configurationSign cfg
          (input.certified.physicalSourceCenter frames.center) *
        permHandedness (input.certified.detectedMultiCenterMolecule.ligandPermAt
          (input.certified.physicalDetectedAut e)
          (input.certified.physicalSourceCenter frames.center)) =
      physicalMirrorFactor mirror *
        input.certified.detectedMultiCenterMolecule.configurationSign cfg
          (input.certified.detectedMultiCenterMolecule.centerPerm
            (input.certified.physicalDetectedAut e)
            (input.certified.physicalSourceCenter frames.center))) :
    referenceState input (input.certified.transportOccurrence singleBonded e target) =
      (if mirror then reflectUppercaseOptionalLabel else id) (referenceState input target) := by
  obtain ⟨raw, source, image⟩ := referenceState_transport_of_calibrated singleBonded e frames
    imageFrames strict cfg mirror sourceCalibrated imageCalibrated signLaw
  rw [image, source]
  cases mirror <;> simp [reflectUppercaseOptionalLabel, reflectUppercaseAuxiliaryLabel]

end Frames

/-! ## Endpoint at a real detected occurrence -/

/-- **Endpoint: actual rigid label covariance at a real detected occurrence.** For the chosen
actual compilation of a real detected occurrence of a simple-bonded input, source-frame
constitutional strictness, calibration at both detected centers and the `BranchTransport` sign
law give the actual generated labels at the source and transported occurrences. The image letter
is the source letter, or its uppercase reflection when `mirror` holds. -/
theorem referenceState_transport_of_real
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (strict : FrameConstitutionalStrict
      (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).frame)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration) (mirror : Bool)
    (sourceCalibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg
      (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).center)
    (imageCalibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg
        (input.certified.physicalImageCenter e
          (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).center))
    (signLaw :
      let center :=
        (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).center
      input.certified.detectedMultiCenterMolecule.configurationSign cfg
          (input.certified.physicalSourceCenter center) *
        permHandedness (input.certified.detectedMultiCenterMolecule.ligandPermAt
          (input.certified.physicalDetectedAut e) (input.certified.physicalSourceCenter center)) =
      physicalMirrorFactor mirror *
        input.certified.detectedMultiCenterMolecule.configurationSign cfg
          (input.certified.detectedMultiCenterMolecule.centerPerm
            (input.certified.physicalDetectedAut e)
            (input.certified.physicalSourceCenter center))) :
    ∃ raw : RS, referenceState input target = some (.chiral raw) ∧
      referenceState input (input.certified.transportOccurrence singleBonded e target) =
        some (.chiral (if mirror then RS.swap raw else raw)) :=
  referenceState_transport_of_calibrated singleBonded e
    (cyclicContextFrameCompilation input singleBonded target real unit targetUnit)
    (cyclicContextFrameCompilation input singleBonded
      (input.certified.transportOccurrence singleBonded e target)
      (transportOccurrence_real input singleBonded e target real)
      (input.certified.transportDetectedOccurrence e unit)
      (transportOccurrence_unit input singleBonded e target unit targetUnit))
    strict cfg mirror sourceCalibrated imageCalibrated signLaw

/-- **Endpoint from `DetectedBranchTransport`.** At a center reached by the transported branch,
the accepted branch-transport sign field supplies the sign law. -/
theorem referenceState_transport_of_branchTransport
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (strict : FrameConstitutionalStrict
      (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).frame)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.detectedMultiCenterMolecule.Center) (i j : Fin 4) (mirror : Bool)
    (transport : input.certified.DetectedBranchTransport e cfg root i j mirror)
    (reached : RootedTetrahedralBranchSymmetry.LigandBranchReaches
      input.certified.detectedMultiCenterMolecule root i
      (input.certified.physicalSourceCenter
        (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).center).1)
    (sourceCalibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg
      (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).center)
    (imageCalibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg
        (input.certified.physicalImageCenter e
          (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).center)) :
    ∃ raw : RS, referenceState input target = some (.chiral raw) ∧
      referenceState input (input.certified.transportOccurrence singleBonded e target) =
        some (.chiral (if mirror then RS.swap raw else raw)) :=
  referenceState_transport_of_real input singleBonded e target real unit targetUnit strict cfg
    mirror sourceCalibrated imageCalibrated
    (transport.signLaw (input.certified.physicalSourceCenter
      (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).center)
      reached)

/-! ## Endpoint at a general-rigid auxiliary target in a tied root arm -/

/-- **Actual rigid label covariance at an auxiliary target in a tied root arm.** The input is
simple-bonded with constant formal charge; rings are allowed. Take a real nonroot detected
occurrence in an actual root arm whose Rule-1a table ties with another distinct real root arm.
Its frame strictness is derived (`frameConstitutionalStrict_of_rootArmRule1aTie_of_physicalRigid`).
Assume the explicit physical hypotheses: calibration of both detected centers in `cfg`, and the
`BranchTransport` sign law at the source center. Then the actual generated states at the target
and at its transported occurrence are uppercase. The image letter is the source letter, or its
reflection when `mirror` holds. -/
theorem referenceState_transport_of_tiedRootArm
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (rootCursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (armMem : armCursor ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input) → Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.certified.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (inside : input.certified.RootBranchContains armCursor.occurrence target)
    (nonroot : target.1.address ≠ [])
    (e : input.certified.moleculeGraph.Aut)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration) (mirror : Bool)
    (sourceCalibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg
      (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).center)
    (imageCalibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg
        (input.certified.physicalImageCenter e
          (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).center))
    (signLaw :
      let center :=
        (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).center
      input.certified.detectedMultiCenterMolecule.configurationSign cfg
          (input.certified.physicalSourceCenter center) *
        permHandedness (input.certified.detectedMultiCenterMolecule.ligandPermAt
          (input.certified.physicalDetectedAut e) (input.certified.physicalSourceCenter center)) =
      physicalMirrorFactor mirror *
        input.certified.detectedMultiCenterMolecule.configurationSign cfg
          (input.certified.detectedMultiCenterMolecule.centerPerm
            (input.certified.physicalDetectedAut e)
            (input.certified.physicalSourceCenter center))) :
    ∃ raw : RS, referenceState input target = some (.chiral raw) ∧
      referenceState input (input.certified.transportOccurrence singleBonded e target) =
        some (.chiral (if mirror then RS.swap raw else raw)) := by
  let frames := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
  have centerMeaning := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target
    frames.center).mp frames.centerComputed
  have strict : FrameConstitutionalStrict frames.frame :=
    frameConstitutionalStrict_of_rootArmRule1aTie_of_physicalRigid input.certified singleBonded
      charge rootCursor rootAddress armCursor armCursor' armMem armMem' armDistinct armReal
      armReal' armRead armRead' armKey armKey' armBuilt armBuilt' tie target real inside
      frames.frame (frame_computed frames) nonroot cfg frames.center centerMeaning.2
      sourceCalibrated
  exact referenceState_transport_of_real input singleBonded e target real unit targetUnit strict
    cfg mirror sourceCalibrated imageCalibrated signLaw

end LocalizedCyclicGeneralRigidLabelCovariance
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.officialNodeAtomLabel_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.rule1bRootDistance_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.rootKey_observable_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.assemble_observable_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.declarative_observable_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.ruleMajorBuild_declarative
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.ruleMajorBuild_observable_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.ruleMajorBuild_compare_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.constitutionallySeparated_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.constitutionallyAbove_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.slotTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.slotTransport_sourceFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.slotTransport_imageFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.image_cursorAt
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.frames_cursor_aligned
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.frames_cursor_valid
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.image_strict
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.image_priorityOrder
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.image_center_val
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.image_center
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.image_detectedLigandPermutation
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.image_detectedLigandPermutation_handedness
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.referenceState_transport_of_calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.referenceState_transport_eq_reflect
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.transportOccurrence_real
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.transportOccurrence_unit
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.referenceState_transport_of_real
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.referenceState_transport_of_branchTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance.referenceState_transport_of_tiedRootArm
