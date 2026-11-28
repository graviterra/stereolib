import TetraStereo.Engine.RingSecondShellDecision
import TetraStereo.Engine.RingReferenceCasing

/-! Two occurrence-dependent physical priority orders at one tetrahedral
atom. An odd relative permutation reverses its published auxiliary hand. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOccurrenceHandParity
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingActivePairs (Site)
open RingNestedActivePair (Frame)
open RingConstitutionalHand (OrientationFrame)
open RingChemicalPriority.ReferenceFrame (pairCount)
open private normalized from TetraStereo.Engine.RingReferenceCasing
open private four_eta from TetraStereo.Engine.RingGroupedGeometry
open private frame_eq from TetraStereo.Engine.RingGroupedReport
open private ranked from TetraStereo.Engine.RingSecondShellDecision

def labels (h : RS) : RingNestedActivePair.Labels := (.chiral h,.chiral h.swap)

private theorem inversions (xs : List Nat) :
    pairCount (fun a b => decide (b < a)) xs = RawMolecule.inversionCount xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [pairCount,RawMolecule.inversionCount,ih,List.countP_eq_length_filter]

private theorem relative_readback (g : Geometry) {xs ys : List Nat} (perm : xs.Perm ys)
    (four : xs.length = 4) (distinct : xs.Nodup) :
    readback? g ys = if RawMolecule.permutationIsEven xs = RawMolecule.permutationIsEven ys then
      readback? g xs else (readback? g xs).map RS.swap := by
  have norm := normalized perm g (fun a b => decide (b < a)) [] (by simpa using four)
    (fun a _ b _ ne => by apply Bool.eq_iff_iff.mpr; simp; omega) distinct
  simp only [List.nil_append,inversions] at norm
  change (if RawMolecule.inversionCount xs % 2 = 0 then readback? g xs else (readback? g xs).map RS.swap) =
    (if RawMolecule.inversionCount ys % 2 = 0 then readback? g ys else (readback? g ys).map RS.swap) at norm
  unfold RawMolecule.permutationIsEven
  by_cases p : RawMolecule.inversionCount xs % 2 = 0 <;>
    by_cases q : RawMolecule.inversionCount ys % 2 = 0 <;>
    cases x : readback? g xs <;> cases y : readback? g ys <;>
    simp_all
  simpa using congrArg RS.swap norm.symm

private theorem trace {i : Input} {q : Site i} {fr : Frame i q} {xs : List Nat}
    (order : OrientationFrame fr xs) :
    xs.Perm (RingRetainedAuxiliary.canonical i.certified fr.center) := by
  rw [←order.atoms_eq]
  have all : fr.atoms (List.finRange 4) = fr.ids := four_eta _ (by
    simpa [RingRetainedAuxiliary.canonical] using fr.physical.length_eq)
  exact ((order.permutation.map _).trans (List.Perm.of_eq all)).trans fr.physical

private theorem state {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {fr : Frame i q} {ids : List Nat} (order : OrientationFrame fr ids) :
    RingChemicalGraphProof.state i q =
      some ((readback? (inputGeometry i.certified) ids).map labels) := by
  have focus := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q fr.center).mp fr.recognized
  have degree := (i.certified.moleculeGraph.mem_tetrahedralCenterSet fr.center.val).mp fr.center.property
  have noP : RingPyramidalPublication.focusP i q = none := by
    have off := RingHydrogenLeafGeometry.notP_of_degree_four (i := i) fr.center.val degree
    simp [RingPyramidalPublication.focusP,focus.1,focus.2,off]
  rw [RingChemicalGraphProof.state_eq,RingPyramidalPublication.publish,noP,
    RingFullPathConstitution.fast_local geom (RingChemicalGraphProof.ready geom q),
    RingFullPathPublication.publish?,frame_eq fr]
  exact RingConstitutionalHand.centre_read geom order (RingChemicalGraphProof.ready geom q)

/-- Arbitrary ranked physical rows, valid even when the constitutional
distinction is deeper than two shells. Admission supplies the nonzero volume. -/
theorem orientation {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {u v : Site i} {a : Frame i u} {b : Frame i v} (center : a.center = b.center)
    {xs ys : List Nat} (left : OrientationFrame a xs) (right : OrientationFrame b ys) :
    ∃ h : RS, readback? (inputGeometry i.certified) xs = some h ∧
      RingChemicalGraphProof.state i u = some (some (labels h)) ∧
      RingChemicalGraphProof.state i v = some (some (labels
        (if RawMolecule.permutationIsEven xs = RawMolecule.permutationIsEven ys then h else h.swap))) := by
  have lp := trace left
  have rp := trace right
  rw [←center] at rp
  have nd : (RingRetainedAuxiliary.canonical i.certified a.center).Nodup :=
    (List.nodup_finRange 4).map (Fin.val_injective.comp (i.certified.canonicalLigandAtom_injective a.center))
  have four : xs.length = 4 := lp.length_eq.trans (by simp [RingRetainedAuxiliary.canonical])
  have nonzero := RingGroupedGeometry.calibrated geom a left.row left.permutation
  rw [left.atoms_eq] at nonzero
  obtain ⟨h,hx⟩ := Option.isSome_iff_exists.mp nonzero
  have hy := relative_readback (inputGeometry i.certified) (lp.trans rp.symm) four (lp.nodup_iff.mpr nd)
  rw [hx] at hy
  refine ⟨h,hx,by rw [state geom left,hx]; rfl,?_⟩
  rw [state geom right,hy]
  split <;> rfl

/-- Executable, graph-only comparison of two strict two-shell orders.
`some true` means the two addresses visit the same atom with opposite
physical order parity; `some false` means their parities agree. -/
def opposite? (i : Input) (u v : Site i) : Option Bool := do
  let a ← RingNestedActivePair.frame? i u
  let b ← RingNestedActivePair.frame? i v
  guard (a.center = b.center)
  let x ← RingSecondShellDecision.row? a
  let y ← RingSecondShellDecision.row? b
  return RawMolecule.permutationIsEven (a.atoms x) != RawMolecule.permutationIsEven (b.atoms y)

theorem checked {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (u v : Site i) {odd : Bool} (got : opposite? i u v = some odd) :
    ∃ h : RS, RingChemicalGraphProof.state i u = some (some (labels h)) ∧
      RingChemicalGraphProof.state i v = some (some (labels (if odd then h.swap else h))) := by
  unfold opposite? at got
  obtain ⟨a,_,h⟩ := Option.bind_eq_some_iff.mp got
  obtain ⟨b,_,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_,guarded,h⟩ := Option.bind_eq_some_iff.mp h
  have center : a.center = b.center := by simpa [guard] using guarded
  obtain ⟨x,hx,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨y,hy,out⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj out
  obtain ⟨hand,_,l,r⟩ := orientation geom center (ranked a hx) (ranked b hy)
  exact ⟨hand,l,by simpa only [bne_iff_ne,ite_not] using r⟩

/-- In particular, swapping priorities two and three between two visits
reverses the actual hand and its reflected partner. -/
theorem swap_middle {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {u v : Site i} {a : Frame i u} {b : Frame i v} {x y z w : Nat}
    (left : OrientationFrame a [x,y,z,w]) (right : OrientationFrame b [x,z,y,w]) :
    ∃ h : RS, RingChemicalGraphProof.state i u = some (some (labels h)) ∧
      RingChemicalGraphProof.state i v = some (some (labels h.swap)) := by
  have nonzero := RingGroupedGeometry.calibrated geom a left.row left.permutation
  rw [left.atoms_eq] at nonzero
  obtain ⟨h,hx⟩ := Option.isSome_iff_exists.mp nonzero
  exact ⟨h,by rw [state geom left,hx]; rfl,by
    rw [state geom right,LocalizedMarkedTerminalGaugeSwap.readback_swap23 (inputGeometry i.certified) x y z w,hx]
    rfl⟩

/-- Closure can exchange the two middle physical directions. Strict
two-shell checks and the atom IDs of the returned rows suffice. -/
theorem two_shell_swap_middle {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {u v : Site i} {a : Frame i u} {b : Frame i v} {left right : List RingActivePairReport.Slot}
    (ha : RingSecondShellDecision.row? a = some left) (hb : RingSecondShellDecision.row? b = some right)
    {x y z w : Nat} (first : a.atoms left = [x,y,z,w]) (second : b.atoms right = [x,z,y,w]) :
    ∃ h : RS, RingChemicalGraphProof.state i u = some (some (labels h)) ∧
      RingChemicalGraphProof.state i v = some (some (labels h.swap)) :=
  swap_middle geom (first ▸ ranked a ha) (second ▸ ranked b hb)

end TetraStereo.Engine.RingOccurrenceHandParity
assert_kernel_only TetraStereo.Engine.RingOccurrenceHandParity.orientation
assert_kernel_only TetraStereo.Engine.RingOccurrenceHandParity.checked
assert_kernel_only TetraStereo.Engine.RingOccurrenceHandParity.swap_middle
assert_kernel_only TetraStereo.Engine.RingOccurrenceHandParity.two_shell_swap_middle
