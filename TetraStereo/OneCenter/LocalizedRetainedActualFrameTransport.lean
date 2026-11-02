import TetraStereo.OneCenter.Basic
import TetraStereo.OneCenter.CIPRationalTetrahedralParityPermutation
import TetraStereo.OneCenter.LocalizedRetainedCursorTransport
import TetraStereo.OneCenter.LocalizedRule3DemandRankProducer
import TetraStereo.OneCenter.LocalizedSimpleBondFourLigandFrames
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Actual frame slots under a molecular automorphism

The four-ligand frame is the executable zipper of `{occurrence, previous? := none}`.
Its order is that list, including the real parent and ring-duplicate leaves.
`framePerm` is a different enumeration: `ligandEquivOfIsTetrahedralCenter`.

`slotPerm` is the `Fin 4` reindexing induced by
`executableLocalizedRerootChildren_transport_perm`. It is not supplied.
`sourceReindex` and `imageReindex` conjugate `framePerm` onto `slotPerm`.

Coordinates are read back by `spatialPointAt?`. A missing point stays `none`.
The volume sign of a slot reordering is the permutation parity. A proper copy or a
`z`-reflection of those points is an extra physical hypothesis, not a consequence
of the automorphism and not a CIP letter.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput)

private theorem cursorList_unique {fuel : Nat}
    (previous : Option (input.LocalizedCIPOccurrence fuel)) :
    ∀ (first second : List (input.LocalizedRerootCursor fuel)),
      first.map (fun child => child.occurrence.1) =
          second.map (fun child => child.occurrence.1) →
        (∀ child ∈ first, child.previous? = previous) →
          (∀ child ∈ second, child.previous? = previous) →
            first = second
  | [], [], _mapped, _firstPrevious, _secondPrevious => rfl
  | [], _ :: _, mapped, _firstPrevious, _secondPrevious => by
      simp at mapped
  | _ :: _, [], mapped, _firstPrevious, _secondPrevious => by
      simp at mapped
  | head :: tail, head2 :: tail2, mapped, firstPrevious, secondPrevious => by
      simp only [List.map_cons, List.cons.injEq] at mapped
      rcases mapped with ⟨headFrame, tailFrames⟩
      have headPrevious : head.previous? = head2.previous? :=
        (firstPrevious head (by simp)).trans (secondPrevious head2 (by simp)).symm
      have headIdentity : head = head2 := by
        apply LocalizedRerootCursor.ext input
        · exact Subtype.ext headFrame
        · exact headPrevious
      have tailIdentity : tail = tail2 :=
        cursorList_unique previous tail tail2 tailFrames
          (fun child present =>
            firstPrevious child (List.mem_cons_of_mem head present))
          (fun child present =>
            secondPrevious child (List.mem_cons_of_mem head2 present))
      simp [headIdentity, tailIdentity]

/-- The four-ligand frame list is the executable zipper at `previous? = none`, in that order. -/
theorem fourLigandFrame_cursors_eq_executable {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    frame.cursors =
      input.executableLocalizedRerootChildren
        ({ occurrence := target, previous? := none } :
          input.LocalizedRerootCursor carrierFuel) := by
  let root : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := none }
  have derived :=
    (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target frame).mp computed
  have execDecl := input.executableLocalizedRerootChildren_declarative root
  have mapped :
      frame.cursors.map (fun child => child.occurrence.1) =
        (input.executableLocalizedRerootChildren root).map
          (fun child => child.occurrence.1) := by
    rw [derived.1.1, execDecl.1]
  exact input.cursorList_unique (some root.occurrence) frame.cursors
    (input.executableLocalizedRerootChildren root) mapped derived.1.2 execDecl.2

/-- A real center node transports to the real center node of the image atom. -/
theorem realTetrahedralCenterNode_transport
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center) :
    input.RealTetrahedralCenterNode
      (input.transportOccurrence singleBonded e target).1.node
      (input.transportTetrahedralCenter e center) := by
  rw [transportOccurrence_node]
  refine ⟨?_, ?_⟩
  · simp [mapOfficialNode, meaning.1]
  · simp [mapOfficialNode, meaning.2, transportTetrahedralCenter_val]

private def frameSlotRaw {α : Type*} [DecidableEq α]
    (source image : List α) (sourceLength : source.length = 4) (imageLength : image.length = 4)
    (same : ∀ a, a ∈ source ↔ a ∈ image) (index : Fin 4) : Fin 4 :=
  let item := source.get (Fin.cast sourceLength.symm index)
  have itemMem : item ∈ image :=
    (same item).mp (List.get_mem source (Fin.cast sourceLength.symm index))
  ⟨image.idxOf item, by
    have ltLen : image.idxOf item < image.length := List.idxOf_lt_length_iff.mpr itemMem
    exact imageLength ▸ ltLen⟩

private theorem frameSlotRaw_get {α : Type*} [DecidableEq α]
    (source image : List α) (sourceLength : source.length = 4) (imageLength : image.length = 4)
    (same : ∀ a, a ∈ source ↔ a ∈ image) (index : Fin 4) :
    image.get (Fin.cast imageLength.symm
        (frameSlotRaw source image sourceLength imageLength same index)) =
      source.get (Fin.cast sourceLength.symm index) := by
  let item := source.get (Fin.cast sourceLength.symm index)
  have itemMem : item ∈ image :=
    (same item).mp (List.get_mem source (Fin.cast sourceLength.symm index))
  have finEq :
      Fin.cast imageLength.symm
          (frameSlotRaw source image sourceLength imageLength same index) =
        ⟨image.idxOf item, List.idxOf_lt_length_iff.mpr itemMem⟩ := by
    apply Fin.ext
    simp [frameSlotRaw, item]
  rw [finEq]
  exact List.idxOf_get _

private theorem frameSlotRaw_injective {α : Type*} [DecidableEq α]
    (source image : List α) (sourceNodup : source.Nodup)
    (sourceLength : source.length = 4) (imageLength : image.length = 4)
    (same : ∀ a, a ∈ source ↔ a ∈ image) :
    Function.Injective (frameSlotRaw source image sourceLength imageLength same) := by
  intro left right equal
  apply Fin.cast_injective sourceLength.symm
  apply (List.nodup_iff_injective_get.mp sourceNodup)
  have leftGet := frameSlotRaw_get source image sourceLength imageLength same left
  have rightGet := frameSlotRaw_get source image sourceLength imageLength same right
  rw [equal] at leftGet
  exact leftGet.symm.trans rightGet

private def frameSlotIndex {α : Type*} [DecidableEq α]
    (source image : List α) (sourceNodup : source.Nodup) (imageNodup : image.Nodup)
    (sourceLength : source.length = 4) (imageLength : image.length = 4)
    (same : ∀ a, a ∈ source ↔ a ∈ image) : Equiv.Perm (Fin 4) where
  toFun := frameSlotRaw source image sourceLength imageLength same
  invFun := frameSlotRaw image source imageLength sourceLength fun a => (same a).symm
  left_inv index := by
    apply Fin.cast_injective sourceLength.symm
    apply (List.nodup_iff_injective_get.mp sourceNodup)
    exact (frameSlotRaw_get image source imageLength sourceLength (fun a => (same a).symm)
      (frameSlotRaw source image sourceLength imageLength same index)).trans
        (frameSlotRaw_get source image sourceLength imageLength same index)
  right_inv index := by
    apply Fin.cast_injective imageLength.symm
    apply (List.nodup_iff_injective_get.mp imageNodup)
    exact (frameSlotRaw_get source image sourceLength imageLength same
      (frameSlotRaw image source imageLength sourceLength (fun a => (same a).symm) index)).trans
        (frameSlotRaw_get image source imageLength sourceLength (fun a => (same a).symm) index)

private theorem frameSlotIndex_get {α : Type*} [DecidableEq α]
    (source image : List α) (sourceNodup : source.Nodup) (imageNodup : image.Nodup)
    (sourceLength : source.length = 4) (imageLength : image.length = 4)
    (same : ∀ a, a ∈ source ↔ a ∈ image) (index : Fin 4) :
    image.get (Fin.cast imageLength.symm
        (frameSlotIndex source image sourceNodup imageNodup sourceLength imageLength same
          index)) =
      source.get (Fin.cast sourceLength.symm index) := by
  simpa [frameSlotIndex] using
    frameSlotRaw_get source image sourceLength imageLength same index

private theorem map_cursor_get
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat} (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (index : Fin 4) :
    (frame.cursors.map (input.transportCursor singleBonded e)).get
        (Fin.cast (Eq.trans
          (List.length_map (as := frame.cursors) (input.transportCursor singleBonded e))
          frame.length_eq).symm index) =
      input.transportCursor singleBonded e (frame.cursorAt index) := by
  simp [LocalizedOccurrenceFourLigandFrame.cursorAt, List.get_eq_getElem, List.getElem_map]

/-- Source frame, transported frame, and the executable-list slot permutation. -/
structure ActualFrameSlotTransport
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter) where
  sourceFrame : input.LocalizedOccurrenceFourLigandFrame carrierFuel
  imageFrame : input.LocalizedOccurrenceFourLigandFrame carrierFuel
  sourceLigand : Fin 4 ≃ input.moleculeGraph.Neighbor center.1
  imageLigand : Fin 4 ≃
    input.moleculeGraph.Neighbor (input.transportTetrahedralCenter e center).1
  slotPerm : Equiv.Perm (Fin 4)
  sourceReindex : Equiv.Perm (Fin 4)
  imageReindex : Equiv.Perm (Fin 4)
  sourceComputed : input.localizedOccurrenceFourLigandFrame? target = some sourceFrame
  imageComputed : input.localizedOccurrenceFourLigandFrame?
      (input.transportOccurrence singleBonded e target) = some imageFrame
  cursorAt_eq : ∀ i, imageFrame.cursorAt (slotPerm i) =
    input.transportCursor singleBonded e (sourceFrame.cursorAt i)
  source_current : ∀ i, (sourceFrame.cursorAt i).occurrence.1.node.current? =
    some (sourceLigand i).1
  image_current : ∀ i, (imageFrame.cursorAt i).occurrence.1.node.current? =
    some (imageLigand i).1
  current_eq : ∀ i, (imageFrame.cursorAt (slotPerm i)).occurrence.1.node.current? =
    ((sourceFrame.cursorAt i).occurrence.1.node.current?).map (e : Equiv.Perm input.Atom)
  source_spatial : ∀ i, input.localizedRerootCursorSpatialPoint? (sourceFrame.cursorAt i) =
    input.spatialPointAt? (sourceLigand i).1
  image_spatial : ∀ i,
    input.localizedRerootCursorSpatialPoint? (imageFrame.cursorAt (slotPerm i)) =
      input.spatialPointAt? ((e : Equiv.Perm input.Atom) (sourceLigand i).1)
  neighbor_eq : ∀ i, imageLigand (slotPerm i) =
    input.neighborTransport e center.1 (sourceLigand i)
  reindex_source : ∀ i, sourceLigand i =
    input.moleculeGraph.ligandEquivOfIsTetrahedralCenter center.1
      ((input.moleculeGraph.mem_tetrahedralCenterSet center.1).mp center.2) (sourceReindex i)
  reindex_image : ∀ i, imageLigand i =
    input.moleculeGraph.ligandEquivOfIsTetrahedralCenter
      (input.transportTetrahedralCenter e center).1
      ((input.moleculeGraph.isTetrahedralCenter_apply_aut_iff e center.1).2
        ((input.moleculeGraph.mem_tetrahedralCenterSet center.1).mp center.2)) (imageReindex i)
  slotPerm_eq : slotPerm =
    (sourceReindex.trans (input.framePerm e center.1
      ((input.moleculeGraph.mem_tetrahedralCenterSet center.1).mp center.2))).trans
      imageReindex.symm

/-- Actual frames at a detected center and at its transported occurrence, with the
executable-list slot permutation and the reindexing onto `framePerm`. -/
noncomputable def actualFrameSlotTransport
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center) :
    input.ActualFrameSlotTransport singleBonded e target center := by
  classical
  let root : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := none }
  let imageTarget := input.transportOccurrence singleBonded e target
  let imageCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := imageTarget, previous? := none }
  have sourceExists :=
    input.exists_simpleBond_localizedOccurrenceFourLigandFrame_and_neighborEquiv
      singleBonded enough target center meaning
  let sourceFrame := Classical.choose sourceExists
  have sourceRest := Classical.choose_spec sourceExists
  let sourceLigand := Classical.choose sourceRest
  have sourceFacts := Classical.choose_spec sourceRest
  have sourceComputed := sourceFacts.1
  have sourceSpec := sourceFacts.2
  have imageMeaning :=
    input.realTetrahedralCenterNode_transport singleBonded e target center meaning
  have imageExists :=
    input.exists_simpleBond_localizedOccurrenceFourLigandFrame_and_neighborEquiv
      singleBonded enough imageTarget (input.transportTetrahedralCenter e center) imageMeaning
  let imageFrame := Classical.choose imageExists
  have imageRest := Classical.choose_spec imageExists
  let imageLigand := Classical.choose imageRest
  have imageFacts := Classical.choose_spec imageRest
  have imageComputed := imageFacts.1
  have imageSpec := imageFacts.2
  have rootTransport :
      input.transportCursor singleBonded e root = imageCursor := by
    apply LocalizedRerootCursor.ext input
    · rfl
    · simp [root, imageCursor, transportCursor]
  have sourceCursors :=
    input.fourLigandFrame_cursors_eq_executable target sourceFrame sourceComputed
  have imageCursors :=
    input.fourLigandFrame_cursors_eq_executable imageTarget imageFrame imageComputed
  have perm := input.executableLocalizedRerootChildren_transport_perm singleBonded e
    (input.cursorPreviousRootAligned_of_none root rfl)
  rw [rootTransport] at perm
  rw [← sourceCursors, ← imageCursors] at perm
  have sourceNodup : sourceFrame.cursors.Nodup := by
    rw [sourceCursors]
    exact input.executableLocalizedRerootChildren_nodup root
  have imageNodup : imageFrame.cursors.Nodup := by
    rw [imageCursors]
    exact input.executableLocalizedRerootChildren_nodup imageCursor
  let mapped := sourceFrame.cursors.map (input.transportCursor singleBonded e)
  have mappedNodup : mapped.Nodup :=
    List.Nodup.map (input.transportCursor_injective singleBonded e carrierFuel) sourceNodup
  have mappedLength : mapped.length = 4 := by
    rw [List.length_map]
    exact sourceFrame.length_eq
  have same : ∀ cursor, cursor ∈ mapped ↔ cursor ∈ imageFrame.cursors :=
    fun cursor => List.Perm.mem_iff (a := cursor) perm
  let slotPerm := frameSlotIndex mapped imageFrame.cursors mappedNodup imageNodup
    mappedLength imageFrame.length_eq same
  have cursorAt_eq : ∀ i, imageFrame.cursorAt (slotPerm i) =
      input.transportCursor singleBonded e (sourceFrame.cursorAt i) := by
    intro i
    have got := frameSlotIndex_get mapped imageFrame.cursors mappedNodup imageNodup
      mappedLength imageFrame.length_eq same i
    rw [input.map_cursor_get singleBonded e sourceFrame i] at got
    simpa [LocalizedOccurrenceFourLigandFrame.cursorAt] using got
  let tetra := (input.moleculeGraph.mem_tetrahedralCenterSet center.1).mp center.2
  let imageTetra :=
    (input.moleculeGraph.isTetrahedralCenter_apply_aut_iff e center.1).2 tetra
  let sourceEnum := input.moleculeGraph.ligandEquivOfIsTetrahedralCenter center.1 tetra
  let imageEnum := input.moleculeGraph.ligandEquivOfIsTetrahedralCenter
    (input.transportTetrahedralCenter e center).1 imageTetra
  let sourceReindex : Equiv.Perm (Fin 4) := sourceLigand.trans sourceEnum.symm
  let imageReindex : Equiv.Perm (Fin 4) := imageLigand.trans imageEnum.symm
  have reindex_source : ∀ i, sourceLigand i = sourceEnum (sourceReindex i) := by
    intro i
    simp [sourceReindex, Equiv.trans_apply]
  have reindex_image : ∀ i, imageLigand i = imageEnum (imageReindex i) := by
    intro i
    simp only [imageReindex, Equiv.trans_apply]
    exact (imageEnum.apply_symm_apply (imageLigand i)).symm
  have current_eq : ∀ i,
      (imageFrame.cursorAt (slotPerm i)).occurrence.1.node.current? =
        ((sourceFrame.cursorAt i).occurrence.1.node.current?).map
          (e : Equiv.Perm input.Atom) := by
    intro i
    rw [cursorAt_eq i]
    simp [transportCursor_occurrence, transportOccurrence_node, mapOfficialNode]
  have neighbor_eq : ∀ i, imageLigand (slotPerm i) =
      input.neighborTransport e center.1 (sourceLigand i) := by
    intro i
    apply Subtype.ext
    have imageAtom := imageSpec (slotPerm i)
    rw [current_eq i, sourceSpec i] at imageAtom
    simp only [Option.map_some, Option.some.injEq] at imageAtom
    unfold neighborTransport
    rw [Equiv.ofBijective_apply]
    exact imageAtom.symm
  have slotPerm_eq : slotPerm =
      (sourceReindex.trans (input.framePerm e center.1 tetra)).trans imageReindex.symm := by
    apply Equiv.ext
    intro i
    apply imageLigand.injective
    rw [neighbor_eq i]
    have imageOfReindex : imageLigand (imageReindex.symm
          (input.framePerm e center.1 tetra (sourceReindex i))) =
        imageEnum (input.framePerm e center.1 tetra (sourceReindex i)) := by
      simp only [imageReindex, Equiv.symm_trans_apply]
      exact imageLigand.apply_symm_apply _
    rw [Equiv.trans_apply, Equiv.trans_apply, imageOfReindex]
    have frameImage : imageEnum (input.framePerm e center.1 tetra (sourceReindex i)) =
        input.neighborTransport e center.1 (sourceEnum (sourceReindex i)) := by
      simp only [framePerm, Equiv.trans_apply]
      exact imageEnum.apply_symm_apply _
    rw [frameImage, reindex_source i]
  have source_spatial : ∀ i,
      input.localizedRerootCursorSpatialPoint? (sourceFrame.cursorAt i) =
        input.spatialPointAt? (sourceLigand i).1 := by
    intro i
    unfold localizedRerootCursorSpatialPoint?
    rw [sourceSpec i]
    rfl
  have image_spatial : ∀ i,
      input.localizedRerootCursorSpatialPoint? (imageFrame.cursorAt (slotPerm i)) =
        input.spatialPointAt? ((e : Equiv.Perm input.Atom) (sourceLigand i).1) := by
    intro i
    unfold localizedRerootCursorSpatialPoint?
    rw [current_eq i, sourceSpec i]
    rfl
  exact {
    sourceFrame, imageFrame, sourceLigand, imageLigand, slotPerm, sourceReindex, imageReindex,
    sourceComputed, imageComputed, cursorAt_eq, source_current := sourceSpec,
    image_current := imageSpec, current_eq, source_spatial, image_spatial, neighbor_eq,
    reindex_source := by simpa [tetra, sourceEnum] using reindex_source,
    reindex_image := by
      simpa [imageTetra, imageEnum, transportTetrahedralCenter_val] using reindex_image,
    slotPerm_eq }

/-- `z`-reflection. Used only as a physical calibration of stored points. -/
def actualFrameReflectZ (point : CartesianPoint3) : CartesianPoint3 where
  x := point.x
  y := point.y
  z := -point.z

/-- Identity when `mirror` is false, and `actualFrameReflectZ` when it is true. -/
def actualFrameConfiguredPoint (mirror : Bool) (point : CartesianPoint3) : CartesianPoint3 :=
  if mirror then actualFrameReflectZ point else point

theorem orientedVolume_actualFrameReflectZ (a b c d : CartesianPoint3) :
    CartesianPoint3.orientedVolume (actualFrameReflectZ a) (actualFrameReflectZ b)
        (actualFrameReflectZ c) (actualFrameReflectZ d) =
      -CartesianPoint3.orientedVolume a b c d := by
  simp only [CartesianPoint3.orientedVolume, actualFrameReflectZ]
  ring

theorem orientedVolume_actualFrameConfiguredPoint (mirror : Bool) (a b c d : CartesianPoint3) :
    CartesianPoint3.orientedVolume (actualFrameConfiguredPoint mirror a)
        (actualFrameConfiguredPoint mirror b) (actualFrameConfiguredPoint mirror c)
        (actualFrameConfiguredPoint mirror d) =
      (if mirror then (-1 : ℚ) else 1) * CartesianPoint3.orientedVolume a b c d := by
  cases mirror with
  | false => simp [actualFrameConfiguredPoint]
  | true =>
      simp [actualFrameConfiguredPoint, orientedVolume_actualFrameReflectZ]

open Rule6HandednessSemantics

private theorem permutationIsEven_inv (σ : Equiv.Perm (Fin 4)) :
    RawMolecule.permutationIsEven (finFourPermutationList σ⁻¹) =
      RawMolecule.permutationIsEven (finFourPermutationList σ) := by
  rw [finFourPermutationIsEven_eq_sign, finFourPermutationIsEven_eq_sign, Equiv.Perm.sign_inv]

private theorem pointVector_slot (point : Fin 4 → CartesianPoint3) (index : Fin 4) :
    RationalTetrahedralPermutation.pointVector (point 0) (point 1) (point 2) (point 3) index =
      point index := by
  fin_cases index <;> rfl

/-- Slot reordering multiplies the oriented volume by the parity of `σ`. The four points stay
fixed: this does not move a conformation. -/
theorem actualFrame_orientedVolume_slotPerm (point : Fin 4 → CartesianPoint3)
    (σ : Equiv.Perm (Fin 4)) :
    RationalTetrahedralPermutation.permutedOrientedVolume
        (point 0) (point 1) (point 2) (point 3) σ =
      if RawMolecule.permutationIsEven (finFourPermutationList σ) then
        CartesianPoint3.orientedVolume (point 0) (point 1) (point 2) (point 3)
      else
        -CartesianPoint3.orientedVolume (point 0) (point 1) (point 2) (point 3) :=
  RationalTetrahedralPermutation.permutedOrientedVolume_eq_if_permutationIsEven
    (point 0) (point 1) (point 2) (point 3) σ

/-- If the image points are the proper copy or the `z`-reflection of the source points,
read in slot order `σ`, the volume picks up that calibration and the parity of `σ`.
The calibration is physical input. It is not implied by a graph automorphism. -/
theorem actualFrame_orientedVolume_calibration (mirror : Bool) (σ : Equiv.Perm (Fin 4))
    (sourcePoint imagePoint : Fin 4 → CartesianPoint3)
    (calibration : ∀ i, imagePoint (σ i) =
      actualFrameConfiguredPoint mirror (sourcePoint i)) :
    CartesianPoint3.orientedVolume (imagePoint 0) (imagePoint 1) (imagePoint 2) (imagePoint 3) =
      (if mirror then (-1 : ℚ) else 1) *
        (if RawMolecule.permutationIsEven (finFourPermutationList σ) then
          CartesianPoint3.orientedVolume
            (sourcePoint 0) (sourcePoint 1) (sourcePoint 2) (sourcePoint 3)
        else
          -CartesianPoint3.orientedVolume
            (sourcePoint 0) (sourcePoint 1) (sourcePoint 2) (sourcePoint 3)) := by
  have imageAt : ∀ k, imagePoint k =
      actualFrameConfiguredPoint mirror (sourcePoint (σ⁻¹ k)) := by
    intro k
    simpa using calibration (σ⁻¹ k)
  rw [imageAt 0, imageAt 1, imageAt 2, imageAt 3,
    orientedVolume_actualFrameConfiguredPoint]
  have permuted :
      CartesianPoint3.orientedVolume (sourcePoint (σ⁻¹ 0)) (sourcePoint (σ⁻¹ 1))
          (sourcePoint (σ⁻¹ 2)) (sourcePoint (σ⁻¹ 3)) =
        RationalTetrahedralPermutation.permutedOrientedVolume
          (sourcePoint 0) (sourcePoint 1) (sourcePoint 2) (sourcePoint 3) σ⁻¹ := by
    simp [RationalTetrahedralPermutation.permutedOrientedVolume, pointVector_slot]
  rw [permuted, RationalTetrahedralPermutation.permutedOrientedVolume_eq_if_permutationIsEven,
    permutationIsEven_inv]

/-- A zero oriented volume is the existing descriptor refusal. It is not a CIP letter. -/
theorem actualFrame_zero_volume_refuses (volume : ℚ) (zero : volume = 0) :
    descriptorOfOrientedVolume? volume = none := by
  rw [descriptorOfOrientedVolume?_eq_none_iff, zero]

private theorem permHandedness_trans (σ τ : Equiv.Perm (Fin 4)) :
    permHandedness (σ.trans τ) = permHandedness τ * permHandedness σ := by
  have compose : σ.trans τ = τ * σ := by
    ext i
    rfl
  rw [compose, permHandedness_mul]

/-- `permHandedness slotPerm` is `frameParity` multiplied by the two enumeration reindex signs. -/
theorem actualFrameSlotTransport_handedness
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center) :
    let packed := input.actualFrameSlotTransport singleBonded e enough target center meaning
    permHandedness packed.slotPerm =
      permHandedness packed.imageReindex *
        (permHandedness (input.framePerm e center.1
          ((input.moleculeGraph.mem_tetrahedralCenterSet center.1).mp center.2)) *
          permHandedness packed.sourceReindex) := by
  intro packed
  rw [packed.slotPerm_eq, permHandedness_trans, permHandedness_trans]
  simp [permHandedness, Equiv.Perm.sign_symm]

/-- Every actual frame slot, including a real parent or a ring leaf, is classified by the
simple-bond frame theorem. -/
theorem actualFrameSlotTransport_classified
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center)
    (index : Fin 4) :
    let packed := input.actualFrameSlotTransport singleBonded e enough target center meaning
    let child := packed.sourceFrame.cursorAt index
    ∃ w, child.occurrence.1.node.current? = some w ∧
      input.moleculeGraph.Adj center.1 w ∧
      ((∃ certificate : input.LocalizedParentFrameHistory target,
          child.occurrence = certificate.parent ∧
          certificate.parent.1.node.ActiveSimple ∧
          target.1.node.parent? = some w ∧
          w ∈ target.1.node.history) ∨
        (child.occurrence.1.node = target.1.node.extend w 0 ∧
          target.1.node.parent? ≠ some w ∧
          (w ∈ target.1.node.history →
            child.occurrence.1.node.provenance =
              OfficialCIPNodeProvenance.ringDuplicate
                (target.1.node.duplicateRootDistance w) ∧
            child.occurrence.1.node.isDuplicateLeaf = true ∧
            input.executableOfficialCIPChildren child.occurrence.1.node = []) ∧
          (w ∉ target.1.node.history →
            child.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom))) := by
  intro packed child
  exact input.simpleBond_fourLigandFrame_cursor_classified singleBonded target center meaning
    packed.sourceFrame packed.sourceComputed child
    (List.get_mem packed.sourceFrame.cursors
      (Fin.cast packed.sourceFrame.length_eq.symm index))

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.fourLigandFrame_cursors_eq_executable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realTetrahedralCenterNode_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.orientedVolume_actualFrameReflectZ
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.orientedVolume_actualFrameConfiguredPoint
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrame_orientedVolume_slotPerm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrame_orientedVolume_calibration
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrame_zero_volume_refuses
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrameSlotTransport_handedness
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrameSlotTransport_classified
