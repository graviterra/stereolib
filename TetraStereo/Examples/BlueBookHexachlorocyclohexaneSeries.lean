import TetraStereo.Examples.HexachlorocyclohexaneClassification

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option Elab.async false
namespace TetraStereo.Examples.BlueBookHexachlorocyclohexaneSeries
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open Engine.RingChemicalPriority Recursive BlueBookHexachlorocyclohexane HexachlorocyclohexaneFamily

/-- Face bits run from back right along the right edge and across the bold
front edge. Set means chlorine lies above the ring plane in the printed drawing.
The source model of P-92.5.2.2 Example 3 has mask 37. -/
def faces (mask : Fin 64) : Geometry := fun j =>
  if 6 ≤ j ∧ j < 18 ∧ mask.val.testBit (j%6) != (37 : Nat).testBit (j%6) then
    geometry (if j < 12 then j+6 else j-6)
  else geometry j

/-- All 64 numbered up/down patterns are realized. Every fixed-frame volume
exists and its sign records precisely the face of that carbon's chlorine. -/
theorem face_hands (mask : Fin 64) (i : Fin 6) :
    readback? (faces mask) (fixedFrame i.val) = some (if mask.val.testBit i.val then .S else .R) := by
  fin_cases i <;> fin_cases mask <;> decide +kernel

theorem all_faces_assigned (mask : Fin 64) (i : Fin 6) : (assign? (faces mask) i).isSome = true := by
  apply (assignment_iff _ _).2
  intro j
  rw [face_hands]
  rfl

abbrev Letter := LocalizedTetrahedralRSPseudoDescriptor
private abbrev bigR : Letter := .chiral .R
private abbrev bigS : Letter := .chiral .S
private abbrev littleR : Letter := .pseudoasymmetric .r
private abbrev littleS : Letter := .pseudoasymmetric .s

structure SourceRow where
  mask : Fin 64
  locants : List (Fin 6)
  expected : List Letter

/-- The third preferred locant sequence reads drawn atoms 4,3,2,1,6,5.
The additional theorem below also verifies the drawing's literal numbering. -/
def series : List SourceRow := [
  ⟨39,[0,5,4,3,2,1],[bigR,bigR,bigS,bigR,bigS,bigS]⟩,
  ⟨47,[0,5,4,3,2,1],[bigR,bigR,littleR,bigS,bigS,littleS]⟩,
  ⟨53,[4,3,2,1,0,5],[bigR,bigS,littleR,bigR,bigS,littleS]⟩,
  ⟨45,[5,4,3,2,1,0],[bigR,littleR,bigS,bigR,littleR,bigS]⟩,
  ⟨42,[5,0,1,2,3,4],[littleR,littleR,littleR,littleR,littleR,littleR]⟩,
  ⟨63,[5,0,1,2,3,4],[littleS,littleS,littleS,littleS,littleS,littleS]⟩,
  ⟨56,[5,0,1,2,3,4],[bigR,bigR,littleS,bigS,bigS,littleS]⟩]

def report (mask : Fin 64) (locants : List (Fin 6)) : Option (List Letter) :=
  locants.mapM fun i => do
    let a ← assign? (faces mask) i
    (reading a.profile a.center).label

theorem seven_published_reports : ∀ row ∈ series, report row.mask row.locants = some row.expected := by
  decide +kernel

theorem third_drawing : report 53 [1,2,3,4,5,0] = some [bigR,littleR,bigS,bigR,littleS,bigS] := by
  decide +kernel

/-- Reversing the convention for traversing the numbered cycle changes the
sign of the fixed-frame hand. Rotation preserves the sign. -/
def sameCycleWord (a b : Fin 64) : Bool :=
  (List.range 6).any fun offset =>
    ((List.range 6).all fun k => a.val.testBit k == b.val.testBit ((offset+k)%6)) ||
    ((List.range 6).all fun k => a.val.testBit k != b.val.testBit ((offset+6-k)%6))

def representatives : List (Fin 64) := series.map SourceRow.mask ++ [37,26]

/-- The seven achiral examples plus the P-92.5.2.2 chiral example and its
mirror cover every up/down word, exactly once under cyclic renumbering. -/
theorem complete_face_table (mask : Fin 64) :
    (representatives.filter (sameCycleWord mask)).length = 1 := by
  fin_cases mask <;> decide +kernel

theorem mirror_classes :
    (∀ row ∈ series, sameCycleWord row.mask (Fin.ofNat 64 (63-row.mask.val)) = true) ∧
    sameCycleWord 37 26 = false := by decide +kernel

end TetraStereo.Examples.BlueBookHexachlorocyclohexaneSeries
assert_kernel_only TetraStereo.Examples.BlueBookHexachlorocyclohexaneSeries.seven_published_reports
assert_kernel_only TetraStereo.Examples.BlueBookHexachlorocyclohexaneSeries.third_drawing
assert_kernel_only TetraStereo.Examples.BlueBookHexachlorocyclohexaneSeries.complete_face_table
assert_kernel_only TetraStereo.Examples.BlueBookHexachlorocyclohexaneSeries.mirror_classes
assert_kernel_only TetraStereo.Examples.BlueBookHexachlorocyclohexaneSeries.face_hands
assert_kernel_only TetraStereo.Examples.BlueBookHexachlorocyclohexaneSeries.all_faces_assigned
