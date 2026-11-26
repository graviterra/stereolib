import TetraStereo.Engine.RingCoordinateReportTransport
import TetraStereo.Engine.RingStereoKeyCoordinates

/-! Transport a constitutionally strict tetrahedral reading to independently admitted
coordinates using only the molecular words and a physical ligand row. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingConstitutionalHand
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader Labels)
open RingActivePairReport (Slot)
attribute [local instance] lexOrd

/-- A genuinely descending constitutional ligand row, independently of geometry. -/
structure DescendingFrame {i : Input} {q : Site i} (fr : Frame i q) (ids : List Nat) where
  row : List Slot
  strict : Function.Injective (RingFullPathConstitution.word fr)
  legal : RingStereoSiblingPass.Legal (RingFullPathConstitution.word fr) (List.finRange 4) row
  atoms_eq : fr.atoms row = ids

/-- A finite, purely constitutional orientation certificate. No descriptor or
coordinate readback occurs in its hypotheses. -/
structure OrientationFrame {i : Input} {q : Site i} (fr : Frame i q) (ids : List Nat) where
  row : List Slot
  permutation : row.Perm (List.finRange 4)
  atoms_eq : fr.atoms row = ids
  parity : RingOrientation.orientation (RingFullPathConstitution.word fr) =
    if RawMolecule.permutationIsEven (row.map Fin.val) then 1 else -1

def DescendingFrame.ranked {i : Input} {q : Site i} {fr : Frame i q} {ids}
    (cert : DescendingFrame fr ids) : OrientationFrame fr ids where
  row := cert.row
  permutation := cert.legal.perm
  atoms_eq := cert.atoms_eq
  parity := by
    have parity := RingFullPathConstitution.sorted_parity cert.strict cert.legal
      (fun j k => compare (RingFullPathConstitution.word fr j)
        (RingFullPathConstitution.word fr k) == .lt)
      (fun j k _ => by simp only [beq_iff_eq,RingFullPathConstitution.word_lt])
    rw [RingFullPathConstitution.strict_orientation _ cert.strict]
    change RawMolecule.permutationIsEven (cert.row.map Fin.val) = _ at parity
    rw [parity]
    simp

theorem OrientationFrame.strict {i : Input} {q : Site i} {fr : Frame i q} {ids}
    (cert : OrientationFrame fr ids) : Function.Injective (RingFullPathConstitution.word fr) := by
  by_contra h
  have zero := (RingOrientation.orientation_zero _).mpr h
  rw [cert.parity] at zero
  split at zero <;> norm_num at zero

/-- The actual native publisher reads the hand in the certified parity-compatible
ligand-ID order, for any ready frozen reader and any admitted geometry. -/
theorem centre_read {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {fr : Frame i q} {ids : List Nat} (cert : OrientationFrame fr ids)
    {r : Reader i} (ready : RingGroupedStereo.Ready q r) :
    RingFullPathPublication.centre? fr r = some
      ((readback? (inputGeometry i.certified) ids).map fun h =>
        (LocalizedTetrahedralRSPseudoDescriptor.chiral h, LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap)) := by
  rw [RingFullPathConstitution.strict_centre geom fr cert.strict ready]
  have read := RingOrientation.frame_read fr (inputGeometry i.certified)
    (⟨cert.row,cert.permutation⟩ : RingJointObservations.Order)
  rw [cert.atoms_eq] at read
  rw [read,cert.parity]
  change some (RingGeometryCriterion.Signature.letters
    ⟨LocalizedChemicalRingPromotionAggregation.readingScore
      (readback? (inputGeometry i.certified) (fr.atoms (List.finRange 4))) *
        (if RawMolecule.permutationIsEven (cert.row.map Fin.val) then 1 else -1),0⟩) = _
  cases hp : RawMolecule.permutationIsEven (cert.row.map Fin.val) <;>
    cases hr : readback? (inputGeometry i.certified) (fr.atoms (List.finRange 4)) with
    | none => simp [RingJointObservations.parity,hp,
        RingGeometryCriterion.Signature.letters,
        LocalizedChemicalRingPromotionAggregation.readingScore,
        RingChemicalPriority.ReferenceFrame.survivingHand]
    | some h => cases h <;> simp [RingJointObservations.parity,hp,
        RingGeometryCriterion.Signature.letters,
        LocalizedChemicalRingPromotionAggregation.readingScore,
        RingChemicalPriority.ReferenceFrame.survivingHand,RingNestedActivePair.label,RS.swap]

/-- Constitution and slot orientation are independent of the coordinate table. -/
theorem word_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = RingSpatialTransport.size i)
    {q : Site i} (fr : Frame i q)
    (other : Frame (RingSpatialTransport.atGeometry i g full)
      (RingSpatialTransport.reindexSite i g full q)) :
    RingFullPathConstitution.word other = RingFullPathConstitution.word fr := by
  funext k
  have old := RingRetainedChemicalPreorder.read_key (fr.direction k)
  have new := RingRetainedChemicalPreorder.read_key (other.direction k)
  have keys := RingStereoKeyCoordinates.constitution_key_atGeometry i g full
    (RingGroupedCentre.cursor fr k)
  change RingRetainedChemicalTrace.key? (RingSpatialTransport.atGeometry i g full)
    (RingSpatialTransport.reindexArm i g full (RingGroupedCentre.cursor fr k)) = _ at keys
  rw [← RingSpatialTransport.frame_cursor_eq i g full fr other k] at keys
  have eqn := Option.some.inj (new.symm.trans (keys.trans old))
  exact congrArg RingRetainedChemicalPreorder.orderWord eqn

def OrientationFrame.atGeometry {i : Input} {q : Site i} {fr : Frame i q} {ids}
    (cert : OrientationFrame fr ids) (g : SpatialConfiguration)
    (full : g.positions.length = RingSpatialTransport.size i)
    (other : Frame (RingSpatialTransport.atGeometry i g full)
      (RingSpatialTransport.reindexSite i g full q)) : OrientationFrame other ids where
  row := cert.row
  permutation := cert.permutation
  atoms_eq := (RingSpatialTransport.frame_atoms_eq i g full fr other cert.row).trans cert.atoms_eq
  parity := by rw [word_atGeometry i g full fr other]; exact cert.parity

theorem root_read {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) {fr : Frame i (RingGroupedReport.origin i a)} {ids}
    (framed : RingNestedActivePair.frame? i (RingGroupedReport.origin i a) = some fr)
    (tetra : RingPyramidalPublication.focusP i (RingGroupedReport.origin i a) = none)
    (cert : OrientationFrame fr ids) :
    RingChemicalGraphProof.root i a = some
      ((readback? (inputGeometry i.certified) ids).map fun h =>
        (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap)) := by
  rw [RingChemicalGraphProof.root,
    RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i),
    ← RingChemicalGraphProof.state, RingChemicalGraphProof.state_eq]
  rw [RingPyramidalPublication.publish,tetra]
  rw [RingFullPathConstitution.fast_local geom (RingChemicalGraphProof.ready geom _)]
  simp only [RingFullPathPublication.publish?,framed]
  exact centre_read geom cert (RingChemicalGraphProof.ready geom _)

/-- A reference certificate controls the independently executed native root
on every admitted full coordinate table of the same fixed topology. -/
theorem root_atGeometry (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = RingSpatialTransport.size i)
    (geom : LocalizedChemicalRing.coordinatesAdmitted
      (RingSpatialTransport.atGeometry i g full) = true)
    (a : i.certified.Atom) {fr : Frame i (RingGroupedReport.origin i a)} {ids}
    (tetra : RingPyramidalPublication.focusP i (RingGroupedReport.origin i a) = none)
    (cert : OrientationFrame fr ids) :
    RingChemicalGraphProof.root (RingSpatialTransport.atGeometry i g full) a = some
      ((readback? (inputGeometry (RingSpatialTransport.atGeometry i g full).certified) ids).map fun h =>
        (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap)) := by
  have recognized := (RingSpatialTransport.recognized_center i g full
    (RingGroupedReport.origin i a)).trans fr.recognized
  have both : ∃ other : Frame (RingSpatialTransport.atGeometry i g full)
      (RingSpatialTransport.reindexSite i g full (RingGroupedReport.origin i a)),
      RingNestedActivePair.frame? _ _ = some other ∧ Nonempty (OrientationFrame other ids) := by
    obtain ⟨other,framed⟩ := RingGroupedGeometry.frame_exists recognized
    exact ⟨other,framed,⟨cert.atGeometry g full other⟩⟩
  rw [RingSpatialTransport.reindex_origin] at both
  obtain ⟨other,framed,⟨ranked⟩⟩ := both
  have nonP := (RingSpatialTransport.focusP_reindex i g full
    (RingGroupedReport.origin i a)).trans tetra
  rw [RingSpatialTransport.reindex_origin] at nonP
  exact root_read geom a framed nonP ranked

theorem root_atGeometry_isSome (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = RingSpatialTransport.size i)
    (geom : LocalizedChemicalRing.coordinatesAdmitted
      (RingSpatialTransport.atGeometry i g full) = true)
    (a : i.certified.Atom) {fr : Frame i (RingGroupedReport.origin i a)} {ids}
    (cert : OrientationFrame fr ids) :
    (readback? (inputGeometry (RingSpatialTransport.atGeometry i g full).certified) ids).isSome = true := by
  have recognized := (RingSpatialTransport.recognized_center i g full
    (RingGroupedReport.origin i a)).trans fr.recognized
  obtain ⟨other,_⟩ := RingGroupedGeometry.frame_exists recognized
  have transported := cert.atGeometry g full other
  rw [← transported.atoms_eq]
  exact RingGroupedGeometry.calibrated geom other _ transported.permutation

end TetraStereo.Engine.RingConstitutionalHand

assert_kernel_only TetraStereo.Engine.RingConstitutionalHand.DescendingFrame.ranked
assert_kernel_only TetraStereo.Engine.RingConstitutionalHand.OrientationFrame.strict
assert_kernel_only TetraStereo.Engine.RingConstitutionalHand.centre_read
assert_kernel_only TetraStereo.Engine.RingConstitutionalHand.word_atGeometry
assert_kernel_only TetraStereo.Engine.RingConstitutionalHand.OrientationFrame.atGeometry
assert_kernel_only TetraStereo.Engine.RingConstitutionalHand.root_read
assert_kernel_only TetraStereo.Engine.RingConstitutionalHand.root_atGeometry
assert_kernel_only TetraStereo.Engine.RingConstitutionalHand.root_atGeometry_isSome
