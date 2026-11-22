import TetraStereo.Examples.BlueBookHexachlorocyclohexane

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option Elab.async false
namespace TetraStereo.Examples.BlueBookHexachlorocyclohexane
open OneCenter Engine.RingChemicalPriority Recursive Certificate.CanonicalSphereKey

private def aux (i : Fin 6) (cw : Bool) (k : Fin 5) :=
  let o := order i cw k
  (geometric geometry o o).getD ⟨.R,.S⟩

private theorem aux_read (i : Fin 6) (cw : Bool) (k : Fin 5) :
    geometric geometry (order i cw k) (order i cw k) = some (aux i cw k) := by
  fin_cases i <;> cases cw <;> fin_cases k <;> decide +kernel

/-- All sixty auxiliary occurrences have strict molecular ligand orders and
spatial readbacks in their own root's digraph. -/
theorem all_auxiliaries (i : Fin 6) (cw : Bool) (k : Fin 5) :
    Supported molecule geometry (path i cw k) (aux i cw k) :=
  auxiliary_of_geometry geometry i cw k _ (aux_read i cw k)

private def facts (i : Fin 6) (cw : Bool) : Facts :=
  (List.finRange 5).map fun k => (path i cw k,aux i cw k)

private theorem valid_facts (i : Fin 6) (cw : Bool) :
    ∀ x ∈ facts i cw, Supported molecule geometry x.1 x.2 := by
  intro x hx
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hx
  exact all_auxiliaries i cw k

/-- Both first pairs are like and both second pairs unlike. The two occurrences
of C-4 are the third comparison, where the C-2 arm first wins. -/
theorem deciding_pairs :
    pairSpheres? (facts 0 true) false = some [[],[],[true],[false],[true],[true],[false]] ∧
    pairSpheres? (facts 0 false) false = some [[],[],[true],[false],[false],[true],[false]] := by
  decide +kernel

private def hand (i : Fin 6) : RS := if i.val < 4 then .R else .S

private theorem local_step (i : Fin 6) :
    (step? molecule geometry [i.val] 0 ((hints [i.val]).get (by rfl))
      (facts i true) (facts i false)).map Subtype.val = some ⟨hand i,(hand i).swap⟩ := by
  fin_cases i <;> decide +kernel

/-- All six locants of P-92.5.2.2 Example 3, each certified in a fresh digraph. -/
theorem published_report :
    saturatedWithHalogens molecule = true ∧
    ∀ i : Fin 6, let h : RS := if i.val < 4 then .R else .S
      Supported molecule geometry [i.val] ⟨h,h.swap⟩ ∧
      (Reading.mk h h.swap).label = some (.chiral h) := by
  refine ⟨by decide +kernel,?_⟩
  intro i h
  exact ⟨supported_of_step (local_step i) (valid_facts i true) (valid_facts i false),
    by cases h <;> rfl⟩

end TetraStereo.Examples.BlueBookHexachlorocyclohexane
assert_kernel_only TetraStereo.Examples.BlueBookHexachlorocyclohexane.all_auxiliaries
assert_kernel_only TetraStereo.Examples.BlueBookHexachlorocyclohexane.deciding_pairs
assert_kernel_only TetraStereo.Examples.BlueBookHexachlorocyclohexane.published_report
