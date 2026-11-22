import TetraStereo.Examples.HexachlorocyclohexaneFamily

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option Elab.async false
namespace TetraStereo.Examples.HexachlorocyclohexaneFamily
open OneCenter LocalizedGenericMarkedRecalculation CertifiedLocalizedCIPInput
open Engine.RingChemicalPriority Recursive BlueBookHexachlorocyclohexane

private theorem priorities0 (p : Fin 32) : priorityCheck 0 p := by
  fin_cases p <;> decide +kernel

private theorem priorities1 (p : Fin 32) : priorityCheck 1 p := by
  fin_cases p <;> decide +kernel

private theorem priorities2 (p : Fin 32) : priorityCheck 2 p := by
  fin_cases p <;> decide +kernel

private theorem priorities3 (p : Fin 32) : priorityCheck 3 p := by
  fin_cases p <;> decide +kernel

private theorem priorities4 (p : Fin 32) : priorityCheck 4 p := by
  fin_cases p <;> decide +kernel

private theorem priorities5 (p : Fin 32) : priorityCheck 5 p := by
  fin_cases p <;> decide +kernel

/-- Both order decisions in all 192 rooted neighbor profiles are checked in
the actual molecular digraph. The focus hand is free in each profile. -/
theorem all_priorities (i : Fin 6) (p : Fin 32) : priorityCheck i p := by
  fin_cases i <;> first | apply priorities0 | apply priorities1 | apply priorities2 |
                          apply priorities3 | apply priorities4 | apply priorities5

private def rBit (h : RS) := (h == .R).toNat
private def packed (a b c d e : RS) : Fin 32 :=
  Fin.ofNat 32 (rBit a + 2*rBit b + 4*rBit c + 8*rBit d + 16*rBit e)

private theorem unpack (a b c d e : RS) :
    let p := packed a b c d e
    hand p 0 = a ∧ hand p 1 = b ∧ hand p 2 = c ∧ hand p 3 = d ∧ hand p 4 = e := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide +kernel

private def packFive (hs : Fin 5 → RS) := packed (hs 0) (hs 1) (hs 2) (hs 3) (hs 4)

private theorem packFive_hand (hs : Fin 5 → RS) (k : Fin 5) : hand (packFive hs) k = hs k := by
  obtain ⟨a,b,c,d,e⟩ := unpack (hs 0) (hs 1) (hs 2) (hs 3) (hs 4)
  fin_cases k <;> first | exact a | exact b | exact c | exact d | exact e

abbrev Nondegenerate (g : Geometry) :=
  ∀ j : Fin 6, (readback? g (fixedFrame j.val)).isSome = true

structure Assignment (g : Geometry) (i : Fin 6) where
  profile : Fin 32
  center : RS
  focusRead : readback? g (fixedFrame i.val) = some center
  neighborReads : ∀ k, readback? g (fixedFrame (forwardSite i k)) = some (hand profile k)
  justified : Supported molecule g [i.val] (reading profile center)

private def nextCarbon (i : Fin 6) (k : Fin 5) : Fin 6 :=
  ⟨forwardSite i k,Nat.mod_lt _ (by decide)⟩

/-- Exact letters and case from the six physical volumes of the chlorinated
ring. Every successful result carries its recursive chemical derivation. -/
def assign? (g : Geometry) (i : Fin 6) : Option (Assignment g i) :=
  if h : Nondegenerate g then Id.run do
    let atC (j : Fin 6) := (readback? g (fixedFrame j.val)).get (h j)
    let hs (k : Fin 5) := atC (nextCarbon i k)
    let p := packFive hs
    have focus : readback? g (fixedFrame i.val) = some (atC i) := (Option.some_get _).symm
    have neighbors (k : Fin 5) : readback? g (fixedFrame (forwardSite i k)) = some (hand p k) := by
      rw [packFive_hand]
      exact (Option.some_get (h (nextCarbon i k))).symm
    return some ⟨p,atC i,focus,neighbors,supported_at (all_priorities i p) focus neighbors⟩
  else none

theorem assignment_iff (g : Geometry) (i : Fin 6) : (assign? g i).isSome = true ↔ Nondegenerate g := by
  by_cases h : Nondegenerate g <;> simp [assign?,h]

/-- The criterion is expressed in physical neighbor hands. It applies to
every nondegenerate realization of this molecular graph. -/
theorem Assignment.lowercase_iff {g i} (a : Assignment g i) :
    (∃ q, (reading a.profile a.center).label = some (.pseudoasymmetric q)) ↔
      hand a.profile 0 = hand a.profile 4 ∧ hand a.profile 1 = hand a.profile 3 := by
  have pal : palindrome a.profile = true ↔
      hand a.profile 0 = hand a.profile 4 ∧ hand a.profile 1 = hand a.profile 3 := by
    simp [palindrome]
  rw [← pal,exact_case]
  cases palindrome a.profile <;> simp

end TetraStereo.Examples.HexachlorocyclohexaneFamily
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexaneFamily.all_priorities
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexaneFamily.assign?
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexaneFamily.assignment_iff
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexaneFamily.Assignment.lowercase_iff
