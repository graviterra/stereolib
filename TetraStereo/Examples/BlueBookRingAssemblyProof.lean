import TetraStereo.Examples.BlueBookRingAssembly
import TetraStereo.Engine.RingRule4bEquivalence

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 3000000
namespace TetraStereo.Examples.BlueBookRingAssembly
open OneCenter Engine.RingChemicalPriority Recursive

/-- Each local certificate discharges its own molecular comparisons. Parent
steps reference the earlier proofs at every discovered occurrence. -/
private abbrev At := Supported molecule geometry

private theorem at_1_2_3_4 : At [1,2,3,4] ⟨.S,.R⟩ :=
  .atomic (depth := 3) (order := [7,3,5,24]) (by decide +kernel) (by decide +kernel)

private theorem at_1_2_3_4_7_8 : At [1,2,3,4,7,8] ⟨.S,.R⟩ :=
  .atomic (depth := 5) (order := [0,9,7,31]) (by decide +kernel) (by decide +kernel)

private theorem at_1_2_3_4_7_8_9_10_11_12_13 : At [1,2,3,4,7,8,9,10,11,12,13] ⟨.S,.R⟩ :=
  .atomic (depth := 3) (order := [12,14,16,39]) (by decide +kernel) (by decide +kernel)

private theorem at_1_2_3_4_7_8_9_10_15_14_13 : At [1,2,3,4,7,8,9,10,15,14,13] ⟨.R,.S⟩ :=
  .atomic (depth := 3) (order := [14,12,16,39]) (by decide +kernel) (by decide +kernel)

private theorem at_1_2_3_4_7_8_9_10 : At [1,2,3,4,7,8,9,10] ⟨.S,.S⟩ :=
  supported_of_step
    (ls := [([1,2,3,4,7,8,9,10,11,12,13],⟨.S,.R⟩)])
    (rs := [([1,2,3,4,7,8,9,10,15,14,13],⟨.R,.S⟩)])
    (depth := 3) (f := (hints [1,2,3,4,7,8,9,10]).get (by decide +kernel)) (by decide +kernel)
    (List.forall_mem_cons.mpr ⟨at_1_2_3_4_7_8_9_10_11_12_13,by simp⟩)
    (List.forall_mem_cons.mpr ⟨at_1_2_3_4_7_8_9_10_15_14_13,by simp⟩)

private theorem at_1_6_5_4 : At [1,6,5,4] ⟨.R,.S⟩ :=
  .atomic (depth := 3) (order := [7,5,3,24]) (by decide +kernel) (by decide +kernel)

private theorem at_1_6_5_4_7_8 : At [1,6,5,4,7,8] ⟨.S,.R⟩ :=
  .atomic (depth := 5) (order := [0,9,7,31]) (by decide +kernel) (by decide +kernel)

private theorem at_1_6_5_4_7_8_9_10_11_12_13 : At [1,6,5,4,7,8,9,10,11,12,13] ⟨.S,.R⟩ :=
  .atomic (depth := 3) (order := [12,14,16,39]) (by decide +kernel) (by decide +kernel)

private theorem at_1_6_5_4_7_8_9_10_15_14_13 : At [1,6,5,4,7,8,9,10,15,14,13] ⟨.R,.S⟩ :=
  .atomic (depth := 3) (order := [14,12,16,39]) (by decide +kernel) (by decide +kernel)

private theorem at_1_6_5_4_7_8_9_10 : At [1,6,5,4,7,8,9,10] ⟨.S,.S⟩ :=
  supported_of_step
    (ls := [([1,6,5,4,7,8,9,10,11,12,13],⟨.S,.R⟩)])
    (rs := [([1,6,5,4,7,8,9,10,15,14,13],⟨.R,.S⟩)])
    (depth := 3) (f := (hints [1,6,5,4,7,8,9,10]).get (by decide +kernel)) (by decide +kernel)
    (List.forall_mem_cons.mpr ⟨at_1_6_5_4_7_8_9_10_11_12_13,by simp⟩)
    (List.forall_mem_cons.mpr ⟨at_1_6_5_4_7_8_9_10_15_14_13,by simp⟩)

private theorem at_1 : At [1] ⟨.S,.R⟩ :=
  supported_of_step
    (ls := [([1,2,3,4],⟨.S,.R⟩),
      ([1,2,3,4,7,8],⟨.S,.R⟩),
      ([1,2,3,4,7,8,9,10],⟨.S,.S⟩),
      ([1,2,3,4,7,8,9,10,11,12,13],⟨.S,.R⟩),
      ([1,2,3,4,7,8,9,10,15,14,13],⟨.R,.S⟩)])
    (rs := [([1,6,5,4],⟨.R,.S⟩),
      ([1,6,5,4,7,8],⟨.S,.R⟩),
      ([1,6,5,4,7,8,9,10],⟨.S,.S⟩),
      ([1,6,5,4,7,8,9,10,11,12,13],⟨.S,.R⟩),
      ([1,6,5,4,7,8,9,10,15,14,13],⟨.R,.S⟩)])
    (depth := 3) (f := (hints [1]).get (by decide +kernel)) (by decide +kernel)
    (List.forall_mem_cons.mpr ⟨at_1_2_3_4,List.forall_mem_cons.mpr ⟨at_1_2_3_4_7_8,List.forall_mem_cons.mpr ⟨at_1_2_3_4_7_8_9_10,List.forall_mem_cons.mpr ⟨at_1_2_3_4_7_8_9_10_11_12_13,List.forall_mem_cons.mpr ⟨at_1_2_3_4_7_8_9_10_15_14_13,by simp⟩⟩⟩⟩⟩)
    (List.forall_mem_cons.mpr ⟨at_1_6_5_4,List.forall_mem_cons.mpr ⟨at_1_6_5_4_7_8,List.forall_mem_cons.mpr ⟨at_1_6_5_4_7_8_9_10,List.forall_mem_cons.mpr ⟨at_1_6_5_4_7_8_9_10_11_12_13,List.forall_mem_cons.mpr ⟨at_1_6_5_4_7_8_9_10_15_14_13,by simp⟩⟩⟩⟩⟩)

private theorem at_4_3_2_1 : At [4,3,2,1] ⟨.S,.R⟩ :=
  .atomic (depth := 3) (order := [2,6,17,19]) (by decide +kernel) (by decide +kernel)

private theorem at_4_5_6_1 : At [4,5,6,1] ⟨.R,.S⟩ :=
  .atomic (depth := 3) (order := [6,2,17,19]) (by decide +kernel) (by decide +kernel)

private theorem at_4 : At [4] ⟨.R,.R⟩ :=
  supported_of_step
    (ls := [([4,3,2,1],⟨.S,.R⟩)])
    (rs := [([4,5,6,1],⟨.R,.S⟩)])
    (depth := 3) (f := (hints [4]).get (by decide +kernel)) (by decide +kernel)
    (List.forall_mem_cons.mpr ⟨at_4_3_2_1,by simp⟩)
    (List.forall_mem_cons.mpr ⟨at_4_5_6_1,by simp⟩)

private theorem at_8_7_4_3_2_1 : At [8,7,4,3,2,1] ⟨.S,.R⟩ :=
  .atomic (depth := 3) (order := [2,6,17,19]) (by decide +kernel) (by decide +kernel)

private theorem at_8_7_4_5_6_1 : At [8,7,4,5,6,1] ⟨.R,.S⟩ :=
  .atomic (depth := 3) (order := [6,2,17,19]) (by decide +kernel) (by decide +kernel)

private theorem at_8_7_4 : At [8,7,4] ⟨.R,.R⟩ :=
  supported_of_step
    (ls := [([8,7,4,3,2,1],⟨.S,.R⟩)])
    (rs := [([8,7,4,5,6,1],⟨.R,.S⟩)])
    (depth := 3) (f := (hints [8,7,4]).get (by decide +kernel)) (by decide +kernel)
    (List.forall_mem_cons.mpr ⟨at_8_7_4_3_2_1,by simp⟩)
    (List.forall_mem_cons.mpr ⟨at_8_7_4_5_6_1,by simp⟩)

private theorem at_8_9_10_11_12_13 : At [8,9,10,11,12,13] ⟨.S,.R⟩ :=
  .atomic (depth := 3) (order := [12,14,16,39]) (by decide +kernel) (by decide +kernel)

private theorem at_8_9_10_15_14_13 : At [8,9,10,15,14,13] ⟨.R,.S⟩ :=
  .atomic (depth := 3) (order := [14,12,16,39]) (by decide +kernel) (by decide +kernel)

private theorem at_8_9_10 : At [8,9,10] ⟨.S,.S⟩ :=
  supported_of_step
    (ls := [([8,9,10,11,12,13],⟨.S,.R⟩)])
    (rs := [([8,9,10,15,14,13],⟨.R,.S⟩)])
    (depth := 3) (f := (hints [8,9,10]).get (by decide +kernel)) (by decide +kernel)
    (List.forall_mem_cons.mpr ⟨at_8_9_10_11_12_13,by simp⟩)
    (List.forall_mem_cons.mpr ⟨at_8_9_10_15_14_13,by simp⟩)

private def leftOfEight : Facts :=
  [([8,7,4],⟨.R,.R⟩),([8,7,4,3,2,1],⟨.S,.R⟩),([8,7,4,5,6,1],⟨.R,.S⟩)]
private def rightOfEight : Facts :=
  [([8,9,10],⟨.S,.S⟩),([8,9,10,11,12,13],⟨.S,.R⟩),([8,9,10,15,14,13],⟨.R,.S⟩)]

private theorem leftOfEight_supported : ∀ x ∈ leftOfEight, At x.1 x.2 :=
  List.forall_mem_cons.mpr ⟨at_8_7_4,List.forall_mem_cons.mpr
    ⟨at_8_7_4_3_2_1,List.forall_mem_cons.mpr ⟨at_8_7_4_5_6_1,by simp⟩⟩⟩
private theorem rightOfEight_supported : ∀ x ∈ rightOfEight, At x.1 x.2 :=
  List.forall_mem_cons.mpr ⟨at_8_9_10,List.forall_mem_cons.mpr
    ⟨at_8_9_10_11_12_13,List.forall_mem_cons.mpr ⟨at_8_9_10_15_14_13,by simp⟩⟩⟩

private theorem at_8 : At [8] ⟨.R,.S⟩ :=
  supported_of_step (ls := leftOfEight) (rs := rightOfEight)
    (depth := 3) (f := (hints [8]).get (by decide +kernel)) (by decide +kernel)
    leftOfEight_supported rightOfEight_supported

/-- Both arms in the C-8 digraph contain a genuinely mixed highest chiral
population. Their R- and S-reference paired digraphs agree as alternatives,
before Rule 4c distinguishes their lower-case attachment descriptors. -/
theorem central_rule4b_tie : ∃ t : Rule4bTie molecule geometry [8],
    t.frame.left = 7 ∧ t.frame.right = 9 ∧
    t.left.references = [.R,.S] ∧ t.right.references = [.R,.S] ∧
    t.left.codes = t.right.codes := by
  let check := verifyRule4bTie? molecule geometry [8] 3 ((hints [8]).get (by decide +kernel))
    leftOfEight rightOfEight leftOfEight_supported rightOfEight_supported
  have passed : (check.map fun t =>
    (t.frame.left,t.frame.right,t.left.references,t.right.references,decide (t.left.codes = t.right.codes))) =
      some (7,9,[.R,.S],[.R,.S],true) := by decide +kernel
  obtain ⟨t,_,eq⟩ := Option.map_eq_some_iff.mp passed
  exact ⟨t,by simpa using eq⟩

private theorem at_10_11_12_13 : At [10,11,12,13] ⟨.S,.R⟩ :=
  .atomic (depth := 3) (order := [12,14,16,39]) (by decide +kernel) (by decide +kernel)

private theorem at_10_15_14_13 : At [10,15,14,13] ⟨.R,.S⟩ :=
  .atomic (depth := 3) (order := [14,12,16,39]) (by decide +kernel) (by decide +kernel)

private theorem at_10 : At [10] ⟨.S,.S⟩ :=
  supported_of_step
    (ls := [([10,11,12,13],⟨.S,.R⟩)])
    (rs := [([10,15,14,13],⟨.R,.S⟩)])
    (depth := 3) (f := (hints [10]).get (by decide +kernel)) (by decide +kernel)
    (List.forall_mem_cons.mpr ⟨at_10_11_12_13,by simp⟩)
    (List.forall_mem_cons.mpr ⟨at_10_15_14_13,by simp⟩)

private theorem at_13_12_11_10 : At [13,12,11,10] ⟨.R,.S⟩ :=
  .atomic (depth := 3) (order := [9,11,15,34]) (by decide +kernel) (by decide +kernel)

private theorem at_13_12_11_10_9_8 : At [13,12,11,10,9,8] ⟨.R,.S⟩ :=
  .atomic (depth := 5) (order := [0,7,9,31]) (by decide +kernel) (by decide +kernel)

private theorem at_13_12_11_10_9_8_7_4_3_2_1 : At [13,12,11,10,9,8,7,4,3,2,1] ⟨.S,.R⟩ :=
  .atomic (depth := 3) (order := [2,6,17,19]) (by decide +kernel) (by decide +kernel)

private theorem at_13_12_11_10_9_8_7_4_5_6_1 : At [13,12,11,10,9,8,7,4,5,6,1] ⟨.R,.S⟩ :=
  .atomic (depth := 3) (order := [6,2,17,19]) (by decide +kernel) (by decide +kernel)

private theorem at_13_12_11_10_9_8_7_4 : At [13,12,11,10,9,8,7,4] ⟨.R,.R⟩ :=
  supported_of_step
    (ls := [([13,12,11,10,9,8,7,4,3,2,1],⟨.S,.R⟩)])
    (rs := [([13,12,11,10,9,8,7,4,5,6,1],⟨.R,.S⟩)])
    (depth := 3) (f := (hints [13,12,11,10,9,8,7,4]).get (by decide +kernel)) (by decide +kernel)
    (List.forall_mem_cons.mpr ⟨at_13_12_11_10_9_8_7_4_3_2_1,by simp⟩)
    (List.forall_mem_cons.mpr ⟨at_13_12_11_10_9_8_7_4_5_6_1,by simp⟩)

private theorem at_13_14_15_10 : At [13,14,15,10] ⟨.S,.R⟩ :=
  .atomic (depth := 3) (order := [9,15,11,34]) (by decide +kernel) (by decide +kernel)

private theorem at_13_14_15_10_9_8 : At [13,14,15,10,9,8] ⟨.R,.S⟩ :=
  .atomic (depth := 5) (order := [0,7,9,31]) (by decide +kernel) (by decide +kernel)

private theorem at_13_14_15_10_9_8_7_4_3_2_1 : At [13,14,15,10,9,8,7,4,3,2,1] ⟨.S,.R⟩ :=
  .atomic (depth := 3) (order := [2,6,17,19]) (by decide +kernel) (by decide +kernel)

private theorem at_13_14_15_10_9_8_7_4_5_6_1 : At [13,14,15,10,9,8,7,4,5,6,1] ⟨.R,.S⟩ :=
  .atomic (depth := 3) (order := [6,2,17,19]) (by decide +kernel) (by decide +kernel)

private theorem at_13_14_15_10_9_8_7_4 : At [13,14,15,10,9,8,7,4] ⟨.R,.R⟩ :=
  supported_of_step
    (ls := [([13,14,15,10,9,8,7,4,3,2,1],⟨.S,.R⟩)])
    (rs := [([13,14,15,10,9,8,7,4,5,6,1],⟨.R,.S⟩)])
    (depth := 3) (f := (hints [13,14,15,10,9,8,7,4]).get (by decide +kernel)) (by decide +kernel)
    (List.forall_mem_cons.mpr ⟨at_13_14_15_10_9_8_7_4_3_2_1,by simp⟩)
    (List.forall_mem_cons.mpr ⟨at_13_14_15_10_9_8_7_4_5_6_1,by simp⟩)

private theorem at_13 : At [13] ⟨.S,.R⟩ :=
  supported_of_step
    (ls := [([13,12,11,10],⟨.R,.S⟩),
      ([13,12,11,10,9,8],⟨.R,.S⟩),
      ([13,12,11,10,9,8,7,4],⟨.R,.R⟩),
      ([13,12,11,10,9,8,7,4,3,2,1],⟨.S,.R⟩),
      ([13,12,11,10,9,8,7,4,5,6,1],⟨.R,.S⟩)])
    (rs := [([13,14,15,10],⟨.S,.R⟩),
      ([13,14,15,10,9,8],⟨.R,.S⟩),
      ([13,14,15,10,9,8,7,4],⟨.R,.R⟩),
      ([13,14,15,10,9,8,7,4,3,2,1],⟨.S,.R⟩),
      ([13,14,15,10,9,8,7,4,5,6,1],⟨.R,.S⟩)])
    (depth := 3) (f := (hints [13]).get (by decide +kernel)) (by decide +kernel)
    (List.forall_mem_cons.mpr ⟨at_13_12_11_10,List.forall_mem_cons.mpr ⟨at_13_12_11_10_9_8,List.forall_mem_cons.mpr ⟨at_13_12_11_10_9_8_7_4,List.forall_mem_cons.mpr ⟨at_13_12_11_10_9_8_7_4_3_2_1,List.forall_mem_cons.mpr ⟨at_13_12_11_10_9_8_7_4_5_6_1,by simp⟩⟩⟩⟩⟩)
    (List.forall_mem_cons.mpr ⟨at_13_14_15_10,List.forall_mem_cons.mpr ⟨at_13_14_15_10_9_8,List.forall_mem_cons.mpr ⟨at_13_14_15_10_9_8_7_4,List.forall_mem_cons.mpr ⟨at_13_14_15_10_9_8_7_4_3_2_1,List.forall_mem_cons.mpr ⟨at_13_14_15_10_9_8_7_4_5_6_1,by simp⟩⟩⟩⟩⟩)

/-- First two chiral sites from C-1 along each arm of the published Rule 4b
digraph. One pair is S₀/S₀; the other is R₀/S₀. -/
theorem first_like_pair :
    At [1,2,3,4] ⟨.S,.R⟩ ∧ At [1,2,3,4,7,8] ⟨.S,.R⟩ ∧
    At [1,6,5,4] ⟨.R,.S⟩ ∧ At [1,6,5,4,7,8] ⟨.S,.R⟩ :=
  ⟨at_1_2_3_4,at_1_2_3_4_7_8,at_1_6_5_4,at_1_6_5_4_7_8⟩

/-- At C-1 the C-2 arm has two later occurrences of C-13 reached through
different arcs of the other ring. All five child readings are derived at
their own addresses in the original C-1 digraph. -/
def armThroughTwo : Facts :=
  [([1,2,3,4],⟨.S,.R⟩),([1,2,3,4,7,8],⟨.S,.R⟩),([1,2,3,4,7,8,9,10],⟨.S,.S⟩),
   ([1,2,3,4,7,8,9,10,11,12,13],⟨.S,.R⟩),([1,2,3,4,7,8,9,10,15,14,13],⟨.R,.S⟩)]

private def throughTwoWords (reverse : Bool) := do
  let arm ← occurrence? molecule [1,2]
  let ps ← carbonSites molecule (molecule.atomCount+1) arm
  guard (ps == armThroughTwo.map Prod.fst)
  let [ref] ← molecularReferences? molecule arm armThroughTwo reverse | none
  let old ← referenceRange? [ref] (chiralSpheres armThroughTwo reverse)
  let new := pairedRange molecule arm armThroughTwo reverse ref
  return (ref,old.low.flatten,old.high.flatten,new.low.flatten,new.high.flatten)

/-- The complete paired word in this arm has a unique final ordering on
both geometries. A distance-only interval admits both 1101 and 1110. -/
theorem two_later_occurrences :
    (∀ x ∈ armThroughTwo, Supported molecule geometry x.1 x.2) ∧
    throughTwoWords false = some (.S,[1,1,0,1],[1,1,1,0],[1,1,1,0],[1,1,1,0]) ∧
    throughTwoWords true = some (.R,[1,1,0,1],[1,1,1,0],[1,1,1,0],[1,1,1,0]) := by
  refine ⟨?_,by decide +kernel,by decide +kernel⟩
  exact List.forall_mem_cons.mpr ⟨at_1_2_3_4,List.forall_mem_cons.mpr ⟨at_1_2_3_4_7_8,
    List.forall_mem_cons.mpr ⟨at_1_2_3_4_7_8_9_10,List.forall_mem_cons.mpr
    ⟨at_1_2_3_4_7_8_9_10_11_12_13,List.forall_mem_cons.mpr
    ⟨at_1_2_3_4_7_8_9_10_15_14_13,by simp⟩⟩⟩⟩⟩

/-- The two ring attachment auxiliaries in the C-8 digraph are reflection
invariant. Their r/s order gives the reflection-variant central R. -/
theorem central_four_c :
    At [8,7,4] ⟨.R,.R⟩ ∧ At [8,9,10] ⟨.S,.S⟩ ∧ At [8] ⟨.R,.S⟩ :=
  ⟨at_8_7_4,at_8_9_10,at_8⟩

def rootReadings : List (Nat × Reading) :=
  [(1,⟨.S,.R⟩),(4,⟨.R,.R⟩),(8,⟨.R,.S⟩),(10,⟨.S,.S⟩),(13,⟨.S,.R⟩)]

/-- All five numbered stereocenters in P-93.6 Example 1 carry a finite
derivation from the same graph and coordinates. -/
theorem published_report :
    saturatedCHO molecule = true ∧
    (rootReadings.mapM fun (i,r) => r.label.map (i,·)) =
      some [(1,.chiral .S),(4,.pseudoasymmetric .r),(8,.chiral .R),
            (10,.pseudoasymmetric .s),(13,.chiral .S)] ∧
    ∀ e ∈ rootReadings, Supported molecule geometry [e.1] e.2 :=
  ⟨by decide +kernel,by decide +kernel,
    List.forall_mem_cons.mpr ⟨at_1,List.forall_mem_cons.mpr ⟨at_4,List.forall_mem_cons.mpr ⟨at_8,List.forall_mem_cons.mpr ⟨at_10,List.forall_mem_cons.mpr ⟨at_13,by simp⟩⟩⟩⟩⟩⟩

end TetraStereo.Examples.BlueBookRingAssembly
assert_kernel_only TetraStereo.Examples.BlueBookRingAssembly.first_like_pair
assert_kernel_only TetraStereo.Examples.BlueBookRingAssembly.central_four_c
assert_kernel_only TetraStereo.Examples.BlueBookRingAssembly.published_report
assert_kernel_only TetraStereo.Examples.BlueBookRingAssembly.central_rule4b_tie
assert_kernel_only TetraStereo.Examples.BlueBookRingAssembly.two_later_occurrences
