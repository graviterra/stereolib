import TetraStereo.Engine.RingActivePairReport

set_option autoImplicit false

namespace TetraStereo.Engine.RingJointObservations
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingActivePairReport (Slot changes)
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry inputGeometry_val)

abbrev Order := {ss : List Slot // ss.Perm (List.finRange 4)}
abbrev Joint := Order × Order

/-- A completed refusal or a jointly attainable actual/reflected ranking. Unknown input
has no constructor here: the caller must establish which completions are reachable. -/
inductive Completed where
  | refused
  | ranked (orders : Joint)

def parity (o : Order) := RawMolecule.permutationIsEven (o.val.map Fin.val)

def observable : Completed → Option (Bool × Bool)
  | .refused => none
  | .ranked (a,b) => some (parity a,parity b)

def oriented (base : RS) (even : Bool) := if even then base else base.swap

/-- Reflected coordinates reverse the baseline orientation before reordering the four
ligands. Both parity bits refer to the very same original ligand indexing. -/
def letter (base : RS) : Option (Bool × Bool) → Option LocalizedAuxiliaryLabel
  | none => none
  | some (a,b) => caseFromMirror? (some (oriented base a)) (some (oriented base b).swap)

theorem letter_injective (base : RS) : Function.Injective (letter base) := by
  intro x y h
  cases x with
  | none => cases y with
    | none => rfl
    | some p => obtain ⟨a,b⟩ := p; cases base <;> cases a <;> cases b <;> contradiction
  | some p =>
    obtain ⟨a,b⟩ := p
    cases y with
    | none => cases base <;> cases a <;> cases b <;> contradiction
    | some p =>
      obtain ⟨c,d⟩ := p
      cases base <;> cases a <;> cases b <;> cases c <;> cases d <;> first | rfl | contradiction

def canonicalFrame {i : Input} (c : i.certified.TetrahedralCenter) :=
  [(i.certified.canonicalLigandAtom c 0).val,(i.certified.canonicalLigandAtom c 1).val,
   (i.certified.canonicalLigandAtom c 2).val,(i.certified.canonicalLigandAtom c 3).val]

def read (g : Geometry) (ids : List Nat) (o : Order) :=
  (atomsAt? ids (o.val.map Fin.val)).bind (readback? g)

def physical (g : Geometry) (ids : List Nat) : Completed → Option LocalizedAuxiliaryLabel
  | .refused => none
  | .ranked (a,b) => caseFromMirror? (read g ids a) (read (mirror g) ids b)

/-- A single canonical coordinate calibration works simultaneously for every joint
ranking at the molecular center, even when several incompatible comparisons remain. -/
theorem calibration (i : Input) (c : i.certified.TetrahedralCenter)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    ∃ base : RS, ∀ w, physical (inputGeometry i.certified) (canonicalFrame c) w = letter base (observable w) := by
  obtain ⟨pt,points,nz,_⟩ := LocalizedChemicalRingPhysicalAdmission.canonical_all_calibrated i.certified admit c
  let atom := fun k : Slot => (i.certified.canonicalLigandAtom c k).val
  have coord (k : Slot) : inputGeometry i.certified (atom k) = some (pt k) :=
    (inputGeometry_val i.certified _).trans (points k)
  have present : (descriptorOfPriorityOrderedPoints? [pt 0,pt 1,pt 2,pt 3]).isSome = true := by
    rcases lt_or_gt_of_ne nz with neg | pos
    · simp [descriptorOfPriorityOrderedPoints?,descriptorOfOrientedVolume?,neg]
    · simp [descriptorOfPriorityOrderedPoints?,descriptorOfOrientedVolume?,pos,not_lt.mpr pos.le]
  obtain ⟨base,raw⟩ := Option.isSome_iff_exists.mp present
  have forward (o : Order) : read (inputGeometry i.certified) (canonicalFrame c) o = some (oriented base (parity o)) := by
    have eqn := LocalizedMarkedFrameCalibration.reordered_readback (inputGeometry i.certified) atom pt coord
      (o.val.map Fin.val) (show (o.val.map Fin.val).Perm [0,1,2,3] from o.property.map Fin.val)
    change (atomsAt? [atom 0,atom 1,atom 2,atom 3] (o.val.map Fin.val)).bind (readback? (inputGeometry i.certified)) = _
    rw [eqn,raw]
    by_cases e : parity o <;> simp_all [oriented,parity]
  have backwards (o : Order) : read (mirror (inputGeometry i.certified)) (canonicalFrame c) o =
      some (oriented base (parity o)).swap := by
    have out := forward o
    unfold read at out ⊢
    cases hs : atomsAt? (canonicalFrame c) (o.val.map Fin.val) <;> simp [hs,readback_mirror] at out ⊢
    simp [out]
  refine ⟨base,?_⟩
  rintro (_ | ⟨a,b⟩)
  · rfl
  · simp [physical,observable,letter,forward,backwards]

/-- Relative order parity across all six named molecular edges. -/
theorem same_parity (a b : Order) : parity a = parity b ↔ changes a.val b.val % 2 = 0 := by
  have all : ∀ a ∈ (List.finRange 4).permutations', ∀ b ∈ (List.finRange 4).permutations',
      RawMolecule.permutationIsEven (a.map Fin.val) = RawMolecule.permutationIsEven (b.map Fin.val) ↔
      changes a b % 2 = 0 := by decide +kernel
  exact all _ (List.mem_permutations'.mpr a.property) _ (List.mem_permutations'.mpr b.property)

/-- When both completions assign, exact physical letters agree precisely when an even
number of pair directions changes on each geometry. No individual direction need agree. -/
theorem ranked_agreement (i : Input) (c : i.certified.TetrahedralCenter)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true) (a b : Joint) :
    physical (inputGeometry i.certified) (canonicalFrame c) (.ranked a) =
      physical (inputGeometry i.certified) (canonicalFrame c) (.ranked b) ↔
    changes a.1.val b.1.val % 2 = 0 ∧ changes a.2.val b.2.val % 2 = 0 := by
  obtain ⟨base,calib⟩ := calibration i c admit
  rw [calib,calib,(letter_injective base).eq_iff]
  simp [observable,Prod.ext_iff,same_parity]

def isLower : Option LocalizedAuxiliaryLabel → Bool
  | some (.pseudoasymmetric _) => true
  | _ => false

private theorem same_case (base : RS) (a b c d : Bool) :
    isLower (letter base (some (a,b))) = isLower (letter base (some (c,d))) ↔
      (a = c ↔ b = d) := by
  cases base <;> cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- Changes of odd parity on *both* geometries change the absolute letter while
preserving its case. More generally case is preserved precisely when the parities
of the two changes agree. This requires fewer observations than the absolute letter. -/
theorem ranked_case_agreement (i : Input) (c : i.certified.TetrahedralCenter)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true) (a b : Joint) :
    isLower (physical (inputGeometry i.certified) (canonicalFrame c) (.ranked a)) =
      isLower (physical (inputGeometry i.certified) (canonicalFrame c) (.ranked b)) ↔
    (changes a.1.val b.1.val % 2 = 0 ↔ changes a.2.val b.2.val % 2 = 0) := by
  obtain ⟨base,calib⟩ := calibration i c admit
  rw [calib,calib,← same_parity,← same_parity]
  exact same_case base _ _ _ _

/-- An observation of an arbitrary family of reachable molecular histories is sufficient
for the whole letter/casing/refusal exactly when it separates the five distinguishable
outcomes. This also applies to infinitely many histories; it requires no independent
variation of the two tied arms or of the two geometries. -/
theorem sufficient_iff {H X : Type} (i : Input) (c : i.certified.TetrahedralCenter)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (obs : H → X) (ends : H → Completed) :
    (∃ decode : X → Option LocalizedAuxiliaryLabel, ∀ h, decode (obs h) =
      physical (inputGeometry i.certified) (canonicalFrame c) (ends h)) ↔
    ∀ h k, obs h = obs k → observable (ends h) = observable (ends k) := by
  obtain ⟨base,calib⟩ := calibration i c admit
  constructor
  · rintro ⟨decoder,ok⟩ h k indist
    apply letter_injective base
    rw [← calib,← calib,← ok,← ok,indist]
  · intro separates
    classical
    refine ⟨fun x => if hx : ∃ h, obs h = x then letter base (observable (ends hx.choose)) else none,?_⟩
    intro h
    have seen : ∃ k, obs k = obs h := ⟨h,rfl⟩
    simp only [dif_pos seen,calib]
    exact congrArg (letter base) (separates _ _ seen.choose_spec)

/-- The chosen occurrence or reference observations determine the complete physical
answer exactly when they hit a difference between each pair of distinguishable histories.
This identifies the evidence that must be proved; other comparisons may remain free. -/
theorem observations_hit_iff {H A V : Type} (i : Input) (c : i.certified.TetrahedralCenter)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (keys : Set A) (observe : H → A → V) (ends : H → Completed) :
    (∃ decode : (keys → V) → Option LocalizedAuxiliaryLabel, ∀ h, decode (fun k => observe h k.val) =
      physical (inputGeometry i.certified) (canonicalFrame c) (ends h)) ↔
    ∀ h k, observable (ends h) ≠ observable (ends k) →
      ∃ a ∈ keys, observe h a ≠ observe k a := by
  rw [sufficient_iff i c admit (fun h (a : keys) => observe h a.val) ends]
  constructor
  · intro enough h k different
    by_contra! never
    exact different (enough h k (funext (fun a => never a.val a.property)))
  · intro hits h k same
    by_contra bad
    obtain ⟨a,inSet,distinct⟩ := hits h k bad
    exact distinct (congrFun same ⟨a,inSet⟩)

/-- Consensus of a finite family of jointly reachable completed alternatives. The outer
option is empty for an empty or disagreeing family; the inner absence is a unanimous
completed refusal. -/
def consensus? : List Completed → Option (Option (Bool × Bool))
  | [] => none
  | w :: ws => if ws.all (fun t => observable t == observable w) then some (observable w) else none

theorem consensus_exact (ws : List Completed) (key : Option (Bool × Bool)) :
    consensus? ws = some key ↔ ws ≠ [] ∧ ∀ w ∈ ws, observable w = key := by
  cases ws with
  | nil => simp [consensus?]
  | cons a rest =>
    by_cases same : ∀ t ∈ rest, observable t = observable a
    · have ok : rest.all (fun t => observable t == observable a) = true := by simpa using same
      simp [consensus?,ok]
      exact fun eqn => eqn ▸ same
    · have bad : rest.all (fun t => observable t == observable a) = false := by simpa using same
      simp [consensus?,bad]
      intro eqn
      push_neg at same
      exact eqn ▸ same

/-- A complete finite over-approximation can already determine the exact physical
answer. Passing this check needs no witness for the attainability of every alternative;
the caller supplies coverage of the actual histories. A failure of the check likewise
makes no assertion that a conflicting alternative is attainable. -/
theorem determined_by_cover {H : Type} (i : Input) (c : i.certified.TetrahedralCenter)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true) (ends : H → Completed)
    (ws : List Completed) (cover : ∀ h, ends h ∈ ws) {key} (hit : consensus? ws = some key) :
    ∃ result, ∀ h, physical (inputGeometry i.certified) (canonicalFrame c) (ends h) = result := by
  obtain ⟨base,calib⟩ := calibration i c admit
  exact ⟨letter base key,fun h => (calib (ends h)).trans
    (congrArg (letter base) (((consensus_exact ws key).mp hit).2 _ (cover h)))⟩

private def straight : Order := ⟨[0,1,2,3],by decide⟩
private def bothPairs : Order := ⟨[1,0,3,2],by decide⟩
private def onePair : Order := ⟨[1,0,2,3],by decide⟩

/-- Treating two coupled two-pair reversals as free choices adds a false ambiguity.
The result holds for every coordinate-admitted canonical tetrahedron and covers both
geometries. It does not assume that a particular molecule realizes either choice. -/
theorem two_pair_coupling (i : Input) (c : i.certified.TetrahedralCenter)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    let result := fun a => physical (inputGeometry i.certified) (canonicalFrame c) (.ranked (a,a))
    result straight = result bothPairs ∧ result straight ≠ result onePair := by
  dsimp only
  constructor
  · exact (ranked_agreement i c admit _ _).mpr (by decide)
  · intro same
    have bad := (ranked_agreement i c admit _ _).mp same
    exact (by decide : ¬changes straight.val onePair.val % 2 = 0) bad.1

end TetraStereo.Engine.RingJointObservations

assert_kernel_only TetraStereo.Engine.RingJointObservations.calibration
assert_kernel_only TetraStereo.Engine.RingJointObservations.ranked_agreement
assert_kernel_only TetraStereo.Engine.RingJointObservations.sufficient_iff

assert_kernel_only TetraStereo.Engine.RingJointObservations.observations_hit_iff
assert_kernel_only TetraStereo.Engine.RingJointObservations.two_pair_coupling

assert_kernel_only TetraStereo.Engine.RingJointObservations.consensus_exact
assert_kernel_only TetraStereo.Engine.RingJointObservations.determined_by_cover

assert_kernel_only TetraStereo.Engine.RingJointObservations.ranked_case_agreement
