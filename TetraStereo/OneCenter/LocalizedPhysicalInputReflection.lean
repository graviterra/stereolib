import TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision
import TetraStereo.OneCenter.LocalizedAcyclicPhysicalPseudoFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false



































namespace TetraStereo.OneCenter.LocalizedPhysicalInputReflection

open CertifiedLocalizedCIPInput RootedTetrahedralBranchSymmetry
open LocalizedRecursiveAuxiliaryPhysicalDomain FinitePhysicalBranchTransport
open LocalizedActualPhysicalBranchDecision

/-! ## The reflected input -/

def reflectSpatial (spatial : SpatialConfiguration) : SpatialConfiguration :=
  { positions := spatial.positions.map CartesianPoint3.reflectX }

/-- Reflect the spatial coordinate table; all other fields are unchanged. -/
def reflectedSource (source : AuthoritativeChemicalInput) : AuthoritativeChemicalInput :=
  { source with spatial? := source.spatial?.map reflectSpatial }

theorem reflectedSource_wellFormed (source : AuthoritativeChemicalInput)
    (wellFormed : source.StructurallyWellFormed) :
    (reflectedSource source).StructurallyWellFormed := by
  rcases wellFormed with ⟨moleculeWellFormed, spatialWellFormed, diagramWellFormed⟩
  refine ⟨moleculeWellFormed, ?_, diagramWellFormed⟩
  cases spatialEq : source.spatial? with
  | none => simp [reflectedSource, AuthoritativeChemicalInput.SpatialIndicesWellFormed, spatialEq]
  | some spatial =>
      have lengthEq : spatial.positions.length = source.molecule.atomCount := by
        simpa [AuthoritativeChemicalInput.SpatialIndicesWellFormed, spatialEq] using
          spatialWellFormed
      simpa [reflectedSource, AuthoritativeChemicalInput.SpatialIndicesWellFormed, spatialEq,
        reflectSpatial] using lengthEq

def reflectedCertified (input : CertifiedLocalizedCIPInput) : CertifiedLocalizedCIPInput where
  certified :=
    { input := reflectedSource input.certified.input
      structurallyWellFormed :=
        reflectedSource_wellFormed _ input.certified.structurallyWellFormed }
  graphReady := input.graphReady

/-- The spatial mirror (`x ↦ -x`) of an actual certified reference input. -/
def reflectInput (input : LocalizedRuleMajorReference.Input) : LocalizedRuleMajorReference.Input where
  certified := reflectedCertified input.certified

/-! ## Transport of the occurrence carrier (graph unchanged) -/

section Transport

variable (input : CertifiedLocalizedCIPInput)

theorem moleculeGraph_reflected :
    (reflectedCertified input).moleculeGraph = input.moleculeGraph := rfl

theorem spatialPointAt?_reflected (atom : input.Atom) :
    (reflectedCertified input).spatialPointAt? atom =
      (input.spatialPointAt? atom).map CartesianPoint3.reflectX := by
  unfold CertifiedLocalizedCIPInput.spatialPointAt?
  simp only [reflectedCertified, reflectedSource]
  cases input.certified.input.spatial? <;> simp [reflectSpatial, List.getElem?_map]

theorem executableOfficialNeighborCopies_reflected (atom : input.Atom) :
    (reflectedCertified input).executableOfficialNeighborCopies atom =
      input.executableOfficialNeighborCopies atom := rfl

theorem executableOfficialChildCopies_reflected (node : OfficialCIPNode input.Atom) :
    (reflectedCertified input).executableOfficialChildCopies node =
      input.executableOfficialChildCopies node := by
  unfold executableOfficialChildCopies
  cases node.current? with
  | none => rfl
  | some current =>
      cases node.parent? with
      | none => simp only [executableOfficialNeighborCopies_reflected]
      | some parent =>
          simp only [executableOfficialNeighborCopies_reflected]
          rfl

theorem executableOfficialCIPChildren_reflected (node : OfficialCIPNode input.Atom) :
    (reflectedCertified input).executableOfficialCIPChildren node =
      input.executableOfficialCIPChildren node := by
  unfold executableOfficialCIPChildren
  rw [executableOfficialChildCopies_reflected]
  rfl

variable {input}

def mapFrame (frame : input.LocalizedCIPOccurrenceFrame) :
    (reflectedCertified input).LocalizedCIPOccurrenceFrame :=
  { root := frame.root, address := frame.address, node := frame.node,
    remaining := frame.remaining }

def unmapFrame (frame : (reflectedCertified input).LocalizedCIPOccurrenceFrame) :
    input.LocalizedCIPOccurrenceFrame :=
  { root := frame.root, address := frame.address, node := frame.node,
    remaining := frame.remaining }

theorem unmapFrame_mapFrame (frame : input.LocalizedCIPOccurrenceFrame) :
    unmapFrame (mapFrame frame) = frame := rfl

theorem mapFrame_unmapFrame (frame : (reflectedCertified input).LocalizedCIPOccurrenceFrame) :
    mapFrame (unmapFrame frame) = frame := rfl

theorem mapFrame_injective : Function.Injective (mapFrame (input := input)) :=
  fun left right equal => by
    have h := congrArg unmapFrame equal
    simpa [unmapFrame_mapFrame] using h

variable (input)

theorem localizedOccurrenceSubtree_reflected (root : input.Atom) (fuel : Nat) (path : List Nat)
    (node : OfficialCIPNode input.Atom) :
    (reflectedCertified input).localizedOccurrenceSubtree root fuel path node =
      (input.localizedOccurrenceSubtree root fuel path node).map mapFrame := by
  induction fuel generalizing path node with
  | zero => rfl
  | succ fuel ih =>
      simp only [localizedOccurrenceSubtree, List.map_cons]
      rw [executableOfficialCIPChildren_reflected]
      simp only [List.map_flatMap]
      apply congrArg (List.cons _)
      apply List.flatMap_congr
      intro child _childPresent
      exact ih _ _

theorem localizedOccurrences_reflected (fuel : Nat) :
    (reflectedCertified input).localizedOccurrences fuel =
      (input.localizedOccurrences fuel).map mapFrame := by
  unfold localizedOccurrences
  change
    ((List.finRange input.certified.input.molecule.atomCount).flatMap
      ((reflectedCertified input).localizedOccurrencesAtAtom fuel)).dedup = _
  rw [← List.dedup_map_of_injective]
  · apply congrArg List.dedup
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro atom _atomPresent
    unfold localizedOccurrencesAtAtom
    exact localizedOccurrenceSubtree_reflected input atom _ _ _
  · exact mapFrame_injective

variable {input}

/-- The reflected input's occurrence with the same frame. -/
def mapOcc {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel) :
    (reflectedCertified input).LocalizedCIPOccurrence fuel :=
  ⟨mapFrame occurrence.1, by
    rw [localizedOccurrences_reflected]
    exact List.mem_map.mpr ⟨occurrence.1, occurrence.2, rfl⟩⟩

/-- The original occurrence with the same frame (constructive inverse). -/
def unmapOcc {fuel : Nat} (occurrence : (reflectedCertified input).LocalizedCIPOccurrence fuel) :
    input.LocalizedCIPOccurrence fuel :=
  ⟨unmapFrame occurrence.1, by
    have present : occurrence.1 ∈ (input.localizedOccurrences fuel).map mapFrame := by
      rw [← localizedOccurrences_reflected]
      exact occurrence.2
    obtain ⟨frame, framePresent, frameEq⟩ := List.mem_map.mp present
    rw [← frameEq]
    exact framePresent⟩

theorem unmapOcc_mapOcc {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel) :
    unmapOcc (mapOcc occurrence) = occurrence := rfl

theorem mapOcc_unmapOcc {fuel : Nat}
    (occurrence : (reflectedCertified input).LocalizedCIPOccurrence fuel) :
    mapOcc (unmapOcc occurrence) = occurrence := rfl

def mapCursor {fuel : Nat} (cursor : input.LocalizedRerootCursor fuel) :
    (reflectedCertified input).LocalizedRerootCursor fuel :=
  { occurrence := mapOcc cursor.occurrence, previous? := cursor.previous?.map mapOcc }

variable (input)

theorem localizedCarrierParentFrames_reflected {fuel : Nat}
    (frame : input.LocalizedCIPOccurrenceFrame) :
    (reflectedCertified input).localizedCarrierParentFrames (fuel := fuel) (mapFrame frame) =
      (input.localizedCarrierParentFrames (fuel := fuel) frame).map mapFrame := by
  unfold localizedCarrierParentFrames
  rw [localizedOccurrences_reflected, List.filter_map]
  rfl

theorem localizedCarrierOutwardChildFrames_reflected {fuel : Nat}
    (frame : input.LocalizedCIPOccurrenceFrame) :
    (reflectedCertified input).localizedCarrierOutwardChildFrames (fuel := fuel)
        (mapFrame frame) =
      (input.localizedCarrierOutwardChildFrames (fuel := fuel) frame).map mapFrame := by
  unfold localizedCarrierOutwardChildFrames
  rw [localizedOccurrences_reflected, List.filter_map]
  rfl

theorem localizedRerootNeighborFrames_reflected {fuel : Nat}
    (frame : input.LocalizedCIPOccurrenceFrame) :
    (reflectedCertified input).localizedRerootNeighborFrames (fuel := fuel) (mapFrame frame) =
      (input.localizedRerootNeighborFrames (fuel := fuel) frame).map mapFrame := by
  simp [localizedRerootNeighborFrames, localizedCarrierParentFrames_reflected,
    localizedCarrierOutwardChildFrames_reflected]

theorem intendedLocalizedRerootChildFrames_reflected {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    (reflectedCertified input).intendedLocalizedRerootChildFrames (mapCursor cursor) =
      (input.intendedLocalizedRerootChildFrames cursor).map mapFrame := by
  unfold intendedLocalizedRerootChildFrames
  simp only [mapCursor, mapOcc]
  by_cases duplicate : cursor.occurrence.1.node.isDuplicateLeaf
  · simp [mapFrame, duplicate]
  · simp only [mapFrame, if_neg duplicate]
    cases previousEq : cursor.previous? with
    | none =>
        change (reflectedCertified input).localizedRerootNeighborFrames
            (mapFrame cursor.occurrence.1) = _
        exact localizedRerootNeighborFrames_reflected input _
    | some previous =>
        simp only [Option.map_some]
        change List.filter (fun frame => frame.address != previous.1.address)
            ((reflectedCertified input).localizedRerootNeighborFrames
              (mapFrame cursor.occurrence.1)) = _
        rw [localizedRerootNeighborFrames_reflected, List.filter_map]
        rfl

private theorem list_eq_of_map_eq {α β : Type*} (f : α → β) (P : α → Prop)
    (injective : ∀ x y, P x → P y → f x = f y → x = y) :
    ∀ (l₁ l₂ : List α), (∀ x ∈ l₁, P x) → (∀ x ∈ l₂, P x) → l₁.map f = l₂.map f → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l₁, b :: l₂, h₁, h₂, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      rw [injective a b (h₁ a (by simp)) (h₂ b (by simp)) h.1,
        list_eq_of_map_eq f P injective l₁ l₂ (fun x hx => h₁ x (by simp [hx]))
          (fun x hx => h₂ x (by simp [hx])) h.2]

theorem executableLocalizedRerootChildren_reflected {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    (reflectedCertified input).executableLocalizedRerootChildren (mapCursor cursor) =
      (input.executableLocalizedRerootChildren cursor).map mapCursor := by
  apply list_eq_of_map_eq (fun child => child.occurrence.1)
    (fun child => child.previous? = some (mapCursor cursor).occurrence)
  · intro x y hx hy hxy
    apply LocalizedRerootCursor.ext
    · exact Subtype.ext hxy
    · rw [hx, hy]
  · intro x hx
    exact (reflectedCertified input).executableLocalizedRerootChildren_previous _ x hx
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have previous := input.executableLocalizedRerootChildren_previous cursor y hy
    simp [mapCursor, previous]
  · rw [(reflectedCertified input).executableLocalizedRerootChildren_map,
      intendedLocalizedRerootChildFrames_reflected, ← input.executableLocalizedRerootChildren_map,
      List.map_map, List.map_map]
    rfl

variable {input}

def mapFrame4 {fuel : Nat} (frame : input.LocalizedOccurrenceFourLigandFrame fuel) :
    (reflectedCertified input).LocalizedOccurrenceFourLigandFrame fuel :=
  { cursors := frame.cursors.map mapCursor, length_eq := by simpa using frame.length_eq }

theorem cursorAt_reflected {fuel : Nat} (frame : input.LocalizedOccurrenceFourLigandFrame fuel)
    (index : Fin 4) : (mapFrame4 frame).cursorAt index = mapCursor (frame.cursorAt index) := by
  unfold LocalizedOccurrenceFourLigandFrame.cursorAt mapFrame4
  simp

variable (input)

theorem noDoubleFrame_reflected {fuel : Nat} (target : input.LocalizedCIPOccurrence fuel) :
    (reflectedCertified input).localizedNoDoubleFourLigandFrameExec? (mapOcc target) =
      (input.localizedNoDoubleFourLigandFrameExec? target).map mapFrame4 := by
  unfold localizedNoDoubleFourLigandFrameExec? executableLocalizedRerootChildren?
  have cursorEq : ({ occurrence := mapOcc target, previous? := none } :
      (reflectedCertified input).LocalizedRerootCursor fuel) =
      mapCursor { occurrence := target, previous? := none } := rfl
  rw [cursorEq, executableLocalizedRerootChildren_reflected]
  by_cases lengthEq : (input.executableLocalizedRerootChildren
      ({ occurrence := target, previous? := none } : input.LocalizedRerootCursor fuel)).length = 4
  · have mappedLength : ((input.executableLocalizedRerootChildren
        ({ occurrence := target, previous? := none } :
          input.LocalizedRerootCursor fuel)).map mapCursor).length = 4 := by simpa using lengthEq
    simp [lengthEq, mappedLength, mapFrame4]
  · simp [lengthEq]

theorem cursorSpatialPoint_reflected {fuel : Nat} (cursor : input.LocalizedRerootCursor fuel) :
    (reflectedCertified input).localizedRerootCursorSpatialPoint? (mapCursor cursor) =
      (input.localizedRerootCursorSpatialPoint? cursor).map CartesianPoint3.reflectX := by
  unfold localizedRerootCursorSpatialPoint?
  have currentEq : (mapCursor cursor).occurrence.1.node.current? =
      cursor.occurrence.1.node.current? := rfl
  rw [currentEq]
  cases cursor.occurrence.1.node.current? with
  | none => rfl
  | some atom => exact spatialPointAt?_reflected input atom

theorem molecularFrameUnit_reflected (frame : input.LocalizedCIPOccurrenceFrame) :
    (reflectedCertified input).molecularFrameUnit (mapFrame frame) =
      input.molecularFrameUnit frame := rfl

theorem occurrenceCarrierNode_reflected (singleBonded : input.moleculeGraph.SimpleBonded)
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel) :
    (reflectedCertified input).occurrenceCarrierNode singleBonded (mapOcc occurrence) =
      input.occurrenceCarrierNode singleBonded occurrence := rfl

end Transport

/-! ## Physical configuration -/

theorem calibrated_reflectInput (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom) (cfg : m.Configuration) (c : m.Center)
    (calibrated : ActualPhysicalCalibratedCoordinates input m cfg c) :
    ActualPhysicalCalibratedCoordinates (reflectedCertified input) m
      (m.mirrorConfiguration cfg) c := by
  obtain ⟨p, observed, nonzero, sign⟩ := calibrated
  refine ⟨fun i => CartesianPoint3.reflectX (p i), fun i => ?_, ?_, ?_⟩
  · rw [spatialPointAt?_reflected, observed i]
    rfl
  · rw [CartesianPoint3.orientedVolume_reflectX]
    exact neg_ne_zero.mpr nonzero
  · rw [CartesianPoint3.orientedVolume_reflectX, rationalVolumeSign_neg, sign,
      MultiCenterMolecule.configurationSign_mirrorConfiguration]

theorem domain_reflectInput (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center)
    (domain : RecursiveAuxiliaryPhysicalDomain input cfg root) :
    RecursiveAuxiliaryPhysicalDomain (reflectedCertified input)
      (input.detectedMultiCenterMolecule.mirrorConfiguration cfg) root := by
  refine ⟨fun center notRoot => ?_⟩
  rcases domain.centerCase center notRoot with twin | calibrated
  · exact Or.inl twin
  · exact Or.inr (calibrated_reflectInput input _ cfg center calibrated)

theorem physicalPairCount_mirrorConfiguration {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center) :
    physicalEnantiomorphicPairCount m (m.mirrorConfiguration cfg) c =
      physicalEnantiomorphicPairCount m cfg c := by
  unfold physicalEnantiomorphicPairCount
  exact sourceEnantiomorphicPairCount_congr _ _
    (fun a b _ => (enantiomorphic_mirrorConfiguration m cfg c a b).symm)

/-- **The executable source-coordinate count is reflection invariant** on the original domain. -/
theorem computedPairCount_coordinateCfg_reflectInput (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center)
    (domain : RecursiveAuxiliaryPhysicalDomain input cfg root) :
    computedPairCount (actualCanonicalMolecule (reflectedCertified input))
        (coordinateCfg (reflectedCertified input)) ⟨root.1, root.2⟩ =
      computedPairCount (actualCanonicalMolecule input) (coordinateCfg input)
        ⟨root.1, root.2⟩ := by
  rw [computedPairCount_coordinateCfg_eq_physical (reflectedCertified input) _ root
      (domain_reflectInput input cfg root domain),
    computedPairCount_coordinateCfg_eq_physical input cfg root domain]
  exact physicalPairCount_mirrorConfiguration _ cfg root

end TetraStereo.OneCenter.LocalizedPhysicalInputReflection

assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalInputReflection.spatialPointAt?_reflected
assert_kernel_only
  TetraStereo.OneCenter.LocalizedPhysicalInputReflection.localizedOccurrences_reflected
assert_kernel_only
  TetraStereo.OneCenter.LocalizedPhysicalInputReflection.executableLocalizedRerootChildren_reflected
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalInputReflection.noDoubleFrame_reflected
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalInputReflection.cursorSpatialPoint_reflected
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalInputReflection.calibrated_reflectInput
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalInputReflection.domain_reflectInput
assert_kernel_only
  TetraStereo.OneCenter.LocalizedPhysicalInputReflection.physicalPairCount_mirrorConfiguration
assert_kernel_only
  TetraStereo.OneCenter.LocalizedPhysicalInputReflection.computedPairCount_coordinateCfg_reflectInput
