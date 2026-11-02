import TetraStereo.OneCenter.LocalizedMarkedUncappedEvaluator
import TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-!
# A bridge-subdivision probe for inherited promotion references

This input subdivides every bridge of the accepted cage once. The executable observations below
are diagnostic only; no physical-completeness counterexample is claimed without the separate
physical-domain and transport proofs.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedSubdividedCageProbe

open LocalizedGenericMarkedRecalculation
open LocalizedMarkedOperationEvaluator
open LocalizedRecursiveAuxiliaryPhysicalCompletion

private def bond (source target : Nat) : RawBond :=
  { source := source, target := target, kind := .single }

def mol : RawMolecule :=
  { atoms := LocalizedHiddenParityMarkedProbe.cageRaw.atoms ++
      List.replicate 6 (AtomSpec.aliphatic .O)
    bonds := [bond 0 1, bond 0 2, bond 0 3, bond 0 9,
      bond 3 5, bond 3 6, bond 3 7, bond 4 8,
      bond 5 15, bond 15 8, bond 6 16, bond 16 8, bond 7 17, bond 17 8,
      bond 9 11, bond 9 12, bond 9 13, bond 10 14,
      bond 11 18, bond 18 14, bond 12 19, bond 19 14, bond 13 20, bond 20 14]
    neighborOrder := [[1,2,3,9], [0], [0], [0,5,6,7], [8], [3,15], [3,16], [3,17],
      [4,15,16,17], [0,11,12,13], [14], [9,18], [9,19], [9,20], [10,18,19,20],
      [5,8], [6,8], [7,8], [11,14], [12,14], [13,14]] }

def far : RawMolecule.CanonicalBranchNode :=
  { atom := 8, parent := 15, history := [8,15,5,3,0], provenance := .realAtom }

def points : List CartesianPoint3 :=
  positions ++ [point (7/2) (1/2) 0, point (7/2) (-1/2) (1/2),
    point (7/2) (-1/2) (-1/2), point (-7/2) (1/2) 0,
    point (-7/2) (-1/2) (1/2), point (-7/2) (-1/2) (-1/2)]

def geom : Geometry := fun atom => points[atom]?

theorem far_frame :
    LocalizedGenericMarkedRecalculation.frameAtoms? mol far = some [15,4,16,17] := by
  decide +kernel

theorem inherited_reference_not_in_frame : 6 ∉ [15,4,16,17] := by decide

/-- The existing atom-wide ranker, called directly with the inherited atom. -/
def directInheritedRanking? : Option Rule6TrackedRanking := do
  let roots ← occurrenceLigandFrame? mol far
  AuthoritativeCIPRule6ReferenceFamily.rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?
    mol [] 6 (LocalizedMarkedUncappedOperations.comparisonFuel mol) roots

/-- Experimental only: retain an inherited atom even when it lies deeper than the frame. -/
def inheritedOperations (input : RawMolecule) : Operations where
  ordinary := LocalizedMarkedUncappedOperations.ordinary? input
  marked := fun state node mark => do
    let roots ← occurrenceLigandFrame? input node
    AuthoritativeCIPRule6ReferenceFamily.rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?
      input state mark (LocalizedMarkedUncappedOperations.comparisonFuel input) roots

def inheritedRawStep? (input : RawMolecule) (g : Geometry) (state : OccurrenceAuxState)
    (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (under : Nat → OccurrenceAuxState) : Option RS := do
  let atoms ← frameAtoms? input node
  let (sorted, adjacent) ← (inheritedOperations input).ordinary state node
  if ¬ atoms.Nodup ∨ consistent adjacent = false then none
  else if strict adjacent then
    let ranked ← atomsAt? atoms sorted
    readback? g ranked
  else
    let evaluate := fun r => do
      let temp ← appendFacts? state (under r)
      markedReading? input (inheritedOperations input) g temp node r
    let fallback := fun (_ : Unit) => consensus ((eligibleOf atoms sorted adjacent).map evaluate)
    match ctx with
    | some r => if atoms.contains r then evaluate r else
      match evaluate r with
      | some d => some d
      | none => fallback ()
    | none => fallback ()

def inheritedDescriptorWith? (input : RawMolecule) (g : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (sub : Geometry → OccurrenceAuxState → Option Nat → RawMolecule.CanonicalBranchNode →
      OccurrenceAuxState) : Option LocalizedTetrahedralRSPseudoDescriptor :=
  caseFromMirror?
    (inheritedRawStep? input g state ctx node
      (underWith input (inheritedOperations input) g state node sub))
    (inheritedRawStep? input (mirror g) state ctx node
      (underWith input (inheritedOperations input) (mirror g) state node sub))

def inheritedFacts (input : RawMolecule) : Nat → Geometry → OccurrenceAuxState → Option Nat →
    RawMolecule.CanonicalBranchNode → OccurrenceAuxState
  | 0, _, _, _, _ => []
  | depth + 1, g, state, ctx, node =>
    (inheritedDescriptorWith? input g state ctx node (inheritedFacts input depth)).toList.map
      (factOf node) ++ (input.canonicalChildren node).flatMap (inheritedFacts input depth g state ctx)

def inheritedAssign? (input : RawMolecule) (g : Geometry) (center : Nat) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  inheritedDescriptorWith? input g [] none (canonicalCenterRoot center)
    (inheritedFacts input (structuralDepth input (canonicalCenterRoot center)))

def equalParityGeom : Geometry := fun atom =>
  if atom = 10 then some (point (-5) 0 0) else geom atom

/- These checks execute the evaluator. They are not used as kernel proofs. -/
/-- info: true -/
#guard_msgs in
#eval (LocalizedMarkedUncappedEvaluator.assignCenter? mol geom 0).isNone

/-- info: true -/
#guard_msgs in
#eval decide (directInheritedRanking? = some
  { positions := [0,2,3,1], unique := true, pseudoComparisons := 1 })

/-- info: true -/
#guard_msgs in
#eval inheritedAssign? mol geom 0 == some (.chiral .S)

/-- info: true -/
#guard_msgs in
#eval inheritedAssign? mol (mirror geom) 0 == some (.chiral .R)

/-- info: true -/
#guard_msgs in
#eval (inheritedAssign? mol equalParityGeom 0).isNone

/-- info: true -/
#guard_msgs in
#eval inheritedAssign? LocalizedHiddenParityMarkedProbe.cageRaw
  (fun atom => positions[atom]?) 0 == some (.chiral .S)

end TetraStereo.OneCenter.LocalizedMarkedSubdividedCageProbe

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedSubdividedCageProbe.far_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedSubdividedCageProbe.inherited_reference_not_in_frame
