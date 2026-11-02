import TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Geometry transport through the actual recursive marked evaluator

Agreement of geometric readbacks propagates through every generated promotion context,
temporary fact, mirrored recomputation and center report. In particular the public evaluator
is independent of the coordinate origin, for arbitrary molecular graphs and recursion depths.

This proves an evaluator invariance, not chemical soundness or success. Reducing the readback
agreement premise to the intended canonical center configurations remains a separate obligation.
The supplied auxiliary state is the same on both sides; generated states are transported by
induction rather than assumed equal.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedGeometryTransport

open LocalizedGenericMarkedRecalculation CertifiedLocalizedCIPInput

/-- Equality of local geometric orientation observations, including refusal. -/
def SameReadbacks (first second : Geometry) : Prop :=
  ∀ atoms, readback? first atoms = readback? second atoms

theorem SameReadbacks.mirror {first second : Geometry}
    (agree : SameReadbacks first second) :
    SameReadbacks (mirror first) (mirror second) := by
  intro atoms
  rw [readback_mirror, readback_mirror, agree atoms]

theorem markedReadback_congr (mol : RawMolecule) (fuel : Nat)
    {first second : Geometry} (agree : SameReadbacks first second)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) (mark : Nat) :
    markedReadback? mol fuel first state node mark =
      markedReadback? mol fuel second state node mark := by
  have readings : readback? first = readback? second := funext agree
  unfold markedReadback?
  rw [readings]

theorem rawStep_congr (mol : RawMolecule) (fuel : Nat)
    {first second : Geometry} (agree : SameReadbacks first second)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (underFirst underSecond : Nat → OccurrenceAuxState)
    (under : ∀ mark, underFirst mark = underSecond mark) :
    rawStep? mol fuel first state ctx node underFirst =
      rawStep? mol fuel second state ctx node underSecond := by
  have readings : readback? first = readback? second := funext agree
  have marked : markedReadback? mol fuel first = markedReadback? mol fuel second := by
    funext s n r
    exact markedReadback_congr mol fuel agree s n r
  rw [show underFirst = underSecond from funext under]
  unfold rawStep?
  rw [readings, marked]

theorem rawWith_congr (mol : RawMolecule) (fuel : Nat)
    {first second : Geometry} (agree : SameReadbacks first second)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (subFirst subSecond : Geometry → OccurrenceAuxState → Option Nat →
      RawMolecule.CanonicalBranchNode → OccurrenceAuxState)
    (sub : ∀ s x child, subFirst first s x child = subSecond second s x child) :
    rawWith? mol fuel first state ctx node subFirst =
      rawWith? mol fuel second state ctx node subSecond := by
  apply rawStep_congr mol fuel agree
  intro mark
  unfold underWith
  exact flatMap_congr_mem _ _ _ fun child _ => sub state (some mark) child

/-- Every generated fact agrees; this includes refusal and arbitrary carried contexts. -/
theorem facts_congr (mol : RawMolecule) (fuel depth : Nat) :
    ∀ (first second : Geometry), SameReadbacks first second →
      ∀ (state : OccurrenceAuxState) (ctx : Option Nat)
        (node : RawMolecule.CanonicalBranchNode),
      facts mol fuel depth first state ctx node = facts mol fuel depth second state ctx node := by
  induction depth with
  | zero => intros; rfl
  | succ depth ih =>
      intro first second agree state ctx node
      have descriptor : descriptor? mol fuel depth first state ctx node =
          descriptor? mol fuel depth second state ctx node := by
        unfold descriptor? descriptorWith?
        rw [rawWith_congr mol fuel agree state ctx node _ _ (ih first second agree),
          rawWith_congr mol fuel agree.mirror state ctx node _ _
            (ih (mirror first) (mirror second) agree.mirror)]
      rw [facts_succ, facts_succ, descriptor]
      congr 1
      exact flatMap_congr_mem _ _ _ fun child _ => ih first second agree state ctx child

theorem descriptor_congr (mol : RawMolecule) (fuel depth : Nat)
    {first second : Geometry} (agree : SameReadbacks first second)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode) :
    descriptor? mol fuel depth first state ctx node =
      descriptor? mol fuel depth second state ctx node := by
  unfold descriptor? descriptorWith?
  rw [rawWith_congr mol fuel agree state ctx node _ _ (facts_congr mol fuel depth _ _ agree),
    rawWith_congr mol fuel agree.mirror state ctx node _ _
      (facts_congr mol fuel depth _ _ agree.mirror)]

theorem assignCenter_congr (mol : RawMolecule) (fuel center : Nat)
    {first second : Geometry} (agree : SameReadbacks first second) :
    assignCenter? mol fuel first center = assignCenter? mol fuel second center :=
  descriptor_congr mol fuel _ agree [] none _

/-- Equality of the actual complete emitted report, not only a chosen center. -/
theorem assign_congr (mol : RawMolecule) {first second : Geometry}
    (agree : SameReadbacks first second) : assign mol first = assign mol second := by
  have centers : assignCenter? mol (comparatorFuel mol) first =
      assignCenter? mol (comparatorFuel mol) second := by
    funext center
    exact assignCenter_congr mol _ center agree
  unfold assign
  rw [centers]

def mapGeometry (f : CartesianPoint3 → CartesianPoint3) (geom : Geometry) : Geometry :=
  fun atom => (geom atom).map f

theorem mapM_mapGeometry (f : CartesianPoint3 → CartesianPoint3) (geom : Geometry)
    (atoms : List Nat) :
    atoms.mapM (mapGeometry f geom) = (atoms.mapM geom).map (List.map f) := by
  induction atoms with
  | nil => rfl
  | cons atom tail ih =>
      simp only [List.mapM_cons, mapGeometry, ih]
      cases geom atom <;> cases tail.mapM geom <;> rfl

private def translatePoint (point offset : CartesianPoint3) : CartesianPoint3 :=
  { x := point.x + offset.x, y := point.y + offset.y, z := point.z + offset.z }

theorem points_translated (points : List CartesianPoint3) (offset : CartesianPoint3) :
    descriptorOfPriorityOrderedPoints? (points.map fun p => translatePoint p offset) =
      descriptorOfPriorityOrderedPoints? points := by
  rcases points with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, tail⟩⟩⟩⟩⟩ <;>
    simp [descriptorOfPriorityOrderedPoints?, translatePoint, CartesianPoint3.orientedVolume]

theorem readbacks_translated (geom : Geometry) (offset : CartesianPoint3) :
    SameReadbacks (mapGeometry (fun p => translatePoint p offset) geom) geom := by
  intro atoms
  unfold readback?
  rw [mapM_mapGeometry]
  cases atoms.mapM geom with
  | none => rfl
  | some points => exact points_translated points offset

/-- Moving the coordinate origin preserves all internally recalculated auxiliary facts. -/
theorem facts_translated (mol : RawMolecule) (fuel depth : Nat)
    (geom : Geometry) (offset : CartesianPoint3) (state : OccurrenceAuxState)
    (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode) :
    facts mol fuel depth (mapGeometry (fun p => translatePoint p offset) geom) state ctx node =
      facts mol fuel depth geom state ctx node :=
  facts_congr mol fuel depth _ _ (readbacks_translated geom offset) state ctx node

/-- Translation preserves the public report with its generated states, case and refusals. -/
theorem assign_translated (mol : RawMolecule) (geom : Geometry) (offset : CartesianPoint3) :
    assign mol (mapGeometry (fun p => translatePoint p offset) geom) = assign mol geom :=
  assign_congr mol (readbacks_translated geom offset)

end TetraStereo.OneCenter.LocalizedMarkedGeometryTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedGeometryTransport.facts_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedGeometryTransport.assign_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedGeometryTransport.readbacks_translated
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedGeometryTransport.facts_translated
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedGeometryTransport.assign_translated
