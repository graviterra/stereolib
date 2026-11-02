import TetraStereo.OneCenter.LocalizedPlanarAxisGeometryDomain
import TetraStereo.OneCenter.LocalizedRule3RouteCompleteness
import TetraStereo.OneCenter.LocalizedRule3OddOriginalTargetDemand
import TetraStereo.OneCenter.LocalizedRule3OriginalTargetDemand
import TetraStereo.OneCenter.LocalizedOccurrenceFiniteCarrier
import TetraStereo.Examples.LocalizedShortCircuitDoubleBondProbe
import TetraStereo.Examples.LocalizedRule3ShortCircuitOddProbe
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput














































namespace SourceAxisGeometryWitnesses

/-! ## The two actual certified inputs -/

/-- The existing certified cis-difluoroethene source. -/
def difluoroSource : AuthoritativeChemicalInput :=
  TetraStereo.Examples.LocalizedShortCircuitDoubleBondProbe.source true

/-- The certified semantic input produced by the repository's own intake for difluoroethene. -/
def difluoroCertified : CertifiedAuthoritativeChemicalInput :=
  (difluoroSource.certify?).get (by decide)

/-- The actual localized certified input for cis-difluoroethene, with its certified molecular
graph. -/
def difluoroInput : CertifiedLocalizedCIPInput :=
  (difluoroCertified.certifyLocalizedCIP?).get (by decide)

/-- The existing certified linked odd-cumulene source. -/
def oddSource : AuthoritativeChemicalInput :=
  TetraStereo.Examples.LocalizedRule3ShortCircuitOddProbe.source

/-- The certified semantic input produced by the repository's own intake for the odd cumulene. -/
def oddCertified : CertifiedAuthoritativeChemicalInput :=
  (oddSource.certify?).get (by decide)

/-- The actual localized certified input for the linked odd cumulene. -/
def oddInput : CertifiedLocalizedCIPInput :=
  (oddCertified.certifyLocalizedCIP?).get (by decide)

theorem difluoro_atomCount : difluoroInput.certified.input.molecule.atomCount = 6 := by
  decide

theorem odd_atomCount : oddInput.certified.input.molecule.atomCount = 14 := by
  decide

/-! ## Exact atom names -/

def f0 : difluoroInput.Atom := ⟨0, by decide⟩
def f1 : difluoroInput.Atom := ⟨1, by decide⟩
def f2 : difluoroInput.Atom := ⟨2, by decide⟩
def f3 : difluoroInput.Atom := ⟨3, by decide⟩
def f4 : difluoroInput.Atom := ⟨4, by decide⟩
def f5 : difluoroInput.Atom := ⟨5, by decide⟩

def o0 : oddInput.Atom := ⟨0, by decide⟩
def o1 : oddInput.Atom := ⟨1, by decide⟩
def o2 : oddInput.Atom := ⟨2, by decide⟩
def o3 : oddInput.Atom := ⟨3, by decide⟩
def o4 : oddInput.Atom := ⟨4, by decide⟩
def o5 : oddInput.Atom := ⟨5, by decide⟩
def o6 : oddInput.Atom := ⟨6, by decide⟩
def o7 : oddInput.Atom := ⟨7, by decide⟩
def o8 : oddInput.Atom := ⟨8, by decide⟩
def o9 : oddInput.Atom := ⟨9, by decide⟩
def o10 : oddInput.Atom := ⟨10, by decide⟩
def o11 : oddInput.Atom := ⟨11, by decide⟩
def o12 : oddInput.Atom := ⟨12, by decide⟩
def o13 : oddInput.Atom := ⟨13, by decide⟩

/-! ## Exact source coordinates -/

/-- The actual source coordinates of the odd cumulene fixture. -/
def q0 : CartesianPoint3 := { x := 0, y := 0, z := 0 }
def q1 : CartesianPoint3 := { x := 1, y := 0, z := 0 }
def q2 : CartesianPoint3 := { x := 2, y := 0, z := 0 }
def q3 : CartesianPoint3 := { x := 3, y := 0, z := 0 }
def q4 : CartesianPoint3 := { x := 3, y := 1, z := 0 }
def q5 : CartesianPoint3 := { x := 4, y := 1, z := 0 }
def q6 : CartesianPoint3 := { x := 5, y := 1, z := 0 }
def q7 : CartesianPoint3 := { x := 6, y := 1, z := 0 }
def q8 : CartesianPoint3 := { x := 0, y := 1, z := 0 }
def q9 : CartesianPoint3 := { x := 0, y := -1, z := 0 }
def q10 : CartesianPoint3 := { x := 6, y := 2, z := 0 }
def q11 : CartesianPoint3 := { x := 6, y := 0, z := 0 }
def q12 : CartesianPoint3 := { x := 3, y := -1, z := 0 }
def q13 : CartesianPoint3 := { x := 3, y := 2, z := 0 }

/-! ## Coordinate lookup from the certified source -/

theorem difluoro_point_zero :
    difluoroInput.spatialPointAt? f0 = some PlanarDifluoroetheneExample.leftEndpoint := by
  decide

theorem difluoro_point_one :
    difluoroInput.spatialPointAt? f1 = some PlanarDifluoroetheneExample.rightEndpoint := by
  decide

theorem difluoro_point_two :
    difluoroInput.spatialPointAt? f2 = some PlanarDifluoroetheneExample.leftFirst := by
  decide

theorem difluoro_point_three :
    difluoroInput.spatialPointAt? f3 = some PlanarDifluoroetheneExample.rightFirst := by
  decide

theorem difluoro_point_four :
    difluoroInput.spatialPointAt? f4 = some PlanarDifluoroetheneExample.leftSecond := by
  decide

theorem difluoro_point_five :
    difluoroInput.spatialPointAt? f5 = some PlanarDifluoroetheneExample.rightSecond := by
  decide

theorem odd_point_zero : oddInput.spatialPointAt? o0 = some q0 := by decide
theorem odd_point_one : oddInput.spatialPointAt? o1 = some q1 := by decide
theorem odd_point_two : oddInput.spatialPointAt? o2 = some q2 := by decide
theorem odd_point_three : oddInput.spatialPointAt? o3 = some q3 := by decide
theorem odd_point_four : oddInput.spatialPointAt? o4 = some q4 := by decide
theorem odd_point_five : oddInput.spatialPointAt? o5 = some q5 := by decide
theorem odd_point_six : oddInput.spatialPointAt? o6 = some q6 := by decide
theorem odd_point_seven : oddInput.spatialPointAt? o7 = some q7 := by decide
theorem odd_point_eight : oddInput.spatialPointAt? o8 = some q8 := by decide
theorem odd_point_nine : oddInput.spatialPointAt? o9 = some q9 := by decide
theorem odd_point_ten : oddInput.spatialPointAt? o10 = some q10 := by decide
theorem odd_point_eleven : oddInput.spatialPointAt? o11 = some q11 := by decide
theorem odd_point_twelve : oddInput.spatialPointAt? o12 = some q12 := by decide
theorem odd_point_thirteen : oddInput.spatialPointAt? o13 = some q13 := by decide

/-! ## Actual adjacency and neighbour finsets of the certified graphs -/

theorem difluoro_adj_iff (a b : difluoroInput.Atom) :
    difluoroInput.moleculeGraph.Adj a b ↔
      (a.val = 0 ∧ (b.val = 1 ∨ b.val = 2 ∨ b.val = 4)) ∨
      (a.val = 1 ∧ (b.val = 0 ∨ b.val = 3 ∨ b.val = 5)) ∨
      (a.val = 2 ∧ b.val = 0) ∨ (a.val = 3 ∧ b.val = 1) ∨
      (a.val = 4 ∧ b.val = 0) ∨ (a.val = 5 ∧ b.val = 1) := by
  revert a b
  decide

theorem odd_adj_iff (a b : oddInput.Atom) :
    oddInput.moleculeGraph.Adj a b ↔
      (a.val = 0 ∧ (b.val = 1 ∨ b.val = 8 ∨ b.val = 9)) ∨
      (a.val = 1 ∧ (b.val = 0 ∨ b.val = 2)) ∨
      (a.val = 2 ∧ (b.val = 1 ∨ b.val = 3)) ∨
      (a.val = 3 ∧ (b.val = 2 ∨ b.val = 4 ∨ b.val = 12)) ∨
      (a.val = 4 ∧ (b.val = 3 ∨ b.val = 5 ∨ b.val = 13)) ∨
      (a.val = 5 ∧ (b.val = 4 ∨ b.val = 6)) ∨
      (a.val = 6 ∧ (b.val = 5 ∨ b.val = 7)) ∨
      (a.val = 7 ∧ (b.val = 6 ∨ b.val = 10 ∨ b.val = 11)) ∨
      (a.val = 8 ∧ b.val = 0) ∨ (a.val = 9 ∧ b.val = 0) ∨
      (a.val = 10 ∧ b.val = 7) ∨ (a.val = 11 ∧ b.val = 7) ∨
      (a.val = 12 ∧ b.val = 3) ∨ (a.val = 13 ∧ b.val = 4) := by
  revert a b
  decide

theorem difluoro_neighbor_finset_zero :
    difluoroInput.moleculeGraph.neighborFinset f0 =
      ({f1, f2, f4} : Finset difluoroInput.Atom) := by
  ext a
  rw [MoleculeGraph.mem_neighborFinset, difluoro_adj_iff]
  fin_cases a <;> simp [difluoro_atomCount, f0, f1, f2, f3, f4, f5]

theorem difluoro_neighbor_finset_one :
    difluoroInput.moleculeGraph.neighborFinset f1 =
      ({f0, f3, f5} : Finset difluoroInput.Atom) := by
  ext a
  rw [MoleculeGraph.mem_neighborFinset, difluoro_adj_iff]
  fin_cases a <;> simp [difluoro_atomCount, f0, f1, f2, f3, f4, f5]

theorem odd_neighbor_finset_zero :
    oddInput.moleculeGraph.neighborFinset o0 =
      ({o1, o8, o9} : Finset oddInput.Atom) := by
  ext a
  rw [MoleculeGraph.mem_neighborFinset, odd_adj_iff]
  fin_cases a <;> simp [odd_atomCount, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13]

theorem odd_neighbor_finset_one :
    oddInput.moleculeGraph.neighborFinset o1 =
      ({o0, o2} : Finset oddInput.Atom) := by
  ext a
  rw [MoleculeGraph.mem_neighborFinset, odd_adj_iff]
  fin_cases a <;> simp [odd_atomCount, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13]

theorem odd_neighbor_finset_two :
    oddInput.moleculeGraph.neighborFinset o2 =
      ({o1, o3} : Finset oddInput.Atom) := by
  ext a
  rw [MoleculeGraph.mem_neighborFinset, odd_adj_iff]
  fin_cases a <;> simp [odd_atomCount, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13]

theorem odd_neighbor_finset_three :
    oddInput.moleculeGraph.neighborFinset o3 =
      ({o2, o4, o12} : Finset oddInput.Atom) := by
  ext a
  rw [MoleculeGraph.mem_neighborFinset, odd_adj_iff]
  fin_cases a <;> simp [odd_atomCount, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13]

theorem odd_neighbor_finset_four :
    oddInput.moleculeGraph.neighborFinset o4 =
      ({o3, o5, o13} : Finset oddInput.Atom) := by
  ext a
  rw [MoleculeGraph.mem_neighborFinset, odd_adj_iff]
  fin_cases a <;> simp [odd_atomCount, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13]

theorem odd_neighbor_finset_five :
    oddInput.moleculeGraph.neighborFinset o5 =
      ({o4, o6} : Finset oddInput.Atom) := by
  ext a
  rw [MoleculeGraph.mem_neighborFinset, odd_adj_iff]
  fin_cases a <;> simp [odd_atomCount, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13]

theorem odd_neighbor_finset_six :
    oddInput.moleculeGraph.neighborFinset o6 =
      ({o5, o7} : Finset oddInput.Atom) := by
  ext a
  rw [MoleculeGraph.mem_neighborFinset, odd_adj_iff]
  fin_cases a <;> simp [odd_atomCount, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13]

theorem odd_neighbor_finset_seven :
    oddInput.moleculeGraph.neighborFinset o7 =
      ({o6, o10, o11} : Finset oddInput.Atom) := by
  ext a
  rw [MoleculeGraph.mem_neighborFinset, odd_adj_iff]
  fin_cases a <;> simp [odd_atomCount, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13]

/-! ## Actual candidate lists from the certified neighbour finsets -/

theorem difluoro_substituents_zero_one :
    difluoroInput.localizedRule3ExplicitSubstituents f0 f1 = [f2, f4] := by
  unfold localizedRule3ExplicitSubstituents
  rw [difluoro_neighbor_finset_zero]
  rw [show ({f1, f2, f4} : Finset difluoroInput.Atom) =
      insert f1 (insert f2 {f4}) from rfl]
  rw [Finset.erase_insert (by simp [f1, f2, f4])]
  exact (List.toFinset_sort (l := [f2, f4]) (r := (· ≤ ·)) (by decide)).mpr (by decide)

theorem difluoro_substituents_one_zero :
    difluoroInput.localizedRule3ExplicitSubstituents f1 f0 = [f3, f5] := by
  unfold localizedRule3ExplicitSubstituents
  rw [difluoro_neighbor_finset_one]
  rw [show ({f0, f3, f5} : Finset difluoroInput.Atom) =
      insert f0 (insert f3 {f5}) from rfl]
  rw [Finset.erase_insert (by simp [f0, f3, f5])]
  exact (List.toFinset_sort (l := [f3, f5]) (r := (· ≤ ·)) (by decide)).mpr (by decide)

theorem odd_substituents_zero_one :
    oddInput.localizedRule3ExplicitSubstituents o0 o1 = [o8, o9] := by
  unfold localizedRule3ExplicitSubstituents
  rw [odd_neighbor_finset_zero]
  rw [show ({o1, o8, o9} : Finset oddInput.Atom) =
      insert o1 (insert o8 {o9}) from rfl]
  rw [Finset.erase_insert (by simp [o1, o8, o9])]
  exact (List.toFinset_sort (l := [o8, o9]) (r := (· ≤ ·)) (by decide)).mpr (by decide)

theorem odd_substituents_one_zero :
    oddInput.localizedRule3ExplicitSubstituents o1 o0 = [o2] := by
  unfold localizedRule3ExplicitSubstituents
  rw [odd_neighbor_finset_one]
  rw [show ({o0, o2} : Finset oddInput.Atom) = insert o0 {o2} from rfl]
  rw [Finset.erase_insert (by simp [o0, o2])]
  simp

theorem odd_substituents_one_two :
    oddInput.localizedRule3ExplicitSubstituents o1 o2 = [o0] := by
  unfold localizedRule3ExplicitSubstituents
  rw [odd_neighbor_finset_one]
  rw [show ({o0, o2} : Finset oddInput.Atom) = insert o2 {o0} from by
    rw [Finset.pair_comm]]
  rw [Finset.erase_insert (by simp [o0, o2])]
  simp

theorem odd_substituents_two_one :
    oddInput.localizedRule3ExplicitSubstituents o2 o1 = [o3] := by
  unfold localizedRule3ExplicitSubstituents
  rw [odd_neighbor_finset_two]
  rw [show ({o1, o3} : Finset oddInput.Atom) = insert o1 {o3} from rfl]
  rw [Finset.erase_insert (by simp [o1, o3])]
  simp

theorem odd_substituents_two_three :
    oddInput.localizedRule3ExplicitSubstituents o2 o3 = [o1] := by
  unfold localizedRule3ExplicitSubstituents
  rw [odd_neighbor_finset_two]
  rw [show ({o1, o3} : Finset oddInput.Atom) = insert o3 {o1} from by
    rw [Finset.pair_comm]]
  rw [Finset.erase_insert (by simp [o1, o3])]
  simp

theorem odd_substituents_three_two :
    oddInput.localizedRule3ExplicitSubstituents o3 o2 = [o4, o12] := by
  unfold localizedRule3ExplicitSubstituents
  rw [odd_neighbor_finset_three]
  rw [show ({o2, o4, o12} : Finset oddInput.Atom) =
      insert o2 (insert o4 {o12}) from rfl]
  rw [Finset.erase_insert (by simp [o2, o4, o12])]
  exact (List.toFinset_sort (l := [o4, o12]) (r := (· ≤ ·)) (by decide)).mpr (by decide)

theorem odd_substituents_four_five :
    oddInput.localizedRule3ExplicitSubstituents o4 o5 = [o3, o13] := by
  unfold localizedRule3ExplicitSubstituents
  rw [odd_neighbor_finset_four]
  rw [show ({o3, o5, o13} : Finset oddInput.Atom) =
      insert o5 (insert o3 {o13}) from by
    rw [Finset.insert_comm o3 o5]]
  rw [Finset.erase_insert (by simp [o3, o5, o13])]
  exact (List.toFinset_sort (l := [o3, o13]) (r := (· ≤ ·)) (by decide)).mpr (by decide)

theorem odd_substituents_five_four :
    oddInput.localizedRule3ExplicitSubstituents o5 o4 = [o6] := by
  unfold localizedRule3ExplicitSubstituents
  rw [odd_neighbor_finset_five]
  rw [show ({o4, o6} : Finset oddInput.Atom) = insert o4 {o6} from rfl]
  rw [Finset.erase_insert (by simp [o4, o6])]
  simp

theorem odd_substituents_five_six :
    oddInput.localizedRule3ExplicitSubstituents o5 o6 = [o4] := by
  unfold localizedRule3ExplicitSubstituents
  rw [odd_neighbor_finset_five]
  rw [show ({o4, o6} : Finset oddInput.Atom) = insert o6 {o4} from by
    rw [Finset.pair_comm]]
  rw [Finset.erase_insert (by simp [o4, o6])]
  simp

theorem odd_substituents_six_five :
    oddInput.localizedRule3ExplicitSubstituents o6 o5 = [o7] := by
  unfold localizedRule3ExplicitSubstituents
  rw [odd_neighbor_finset_six]
  rw [show ({o5, o7} : Finset oddInput.Atom) = insert o5 {o7} from rfl]
  rw [Finset.erase_insert (by simp [o5, o7])]
  simp

theorem odd_substituents_six_seven :
    oddInput.localizedRule3ExplicitSubstituents o6 o7 = [o5] := by
  unfold localizedRule3ExplicitSubstituents
  rw [odd_neighbor_finset_six]
  rw [show ({o5, o7} : Finset oddInput.Atom) = insert o7 {o5} from by
    rw [Finset.pair_comm]]
  rw [Finset.erase_insert (by simp [o5, o7])]
  simp

theorem odd_substituents_seven_six :
    oddInput.localizedRule3ExplicitSubstituents o7 o6 = [o10, o11] := by
  unfold localizedRule3ExplicitSubstituents
  rw [odd_neighbor_finset_seven]
  rw [show ({o6, o10, o11} : Finset oddInput.Atom) =
      insert o6 (insert o10 {o11}) from rfl]
  rw [Finset.erase_insert (by simp [o6, o10, o11])]
  exact (List.toFinset_sort (l := [o10, o11]) (r := (· ≤ ·)) (by decide)).mpr (by decide)

/-! ## Actual order-two bond records -/

theorem difluoro_bond_two_characterization (a b : difluoroInput.Atom)
    (bond : difluoroInput.moleculeGraph.bond a b = 2) :
    (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0) := by
  revert a b
  decide

theorem odd_bond_two_characterization (a b : oddInput.Atom)
    (bond : oddInput.moleculeGraph.bond a b = 2) :
    (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0) ∨
      (a.val = 1 ∧ b.val = 2) ∨ (a.val = 2 ∧ b.val = 1) ∨
      (a.val = 2 ∧ b.val = 3) ∨ (a.val = 3 ∧ b.val = 2) ∨
      (a.val = 4 ∧ b.val = 5) ∨ (a.val = 5 ∧ b.val = 4) ∨
      (a.val = 5 ∧ b.val = 6) ∨ (a.val = 6 ∧ b.val = 5) ∨
      (a.val = 6 ∧ b.val = 7) ∨ (a.val = 7 ∧ b.val = 6) := by
  revert a b
  decide

/-- The odd cumulene fixture has no ordinary physical axis with two actual candidate atoms at
both endpoints: every order-two edge has a candidate list of length one at at least one endpoint. -/
theorem odd_no_ordinary_double_candidate_axis (a b : oddInput.Atom)
    (bond : oddInput.moleculeGraph.bond a b = 2) :
    (oddInput.localizedRule3ExplicitSubstituents a b).length ≠ 2 ∨
      (oddInput.localizedRule3ExplicitSubstituents b a).length ≠ 2 := by
  rcases odd_bond_two_characterization a b bond with
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have ha' : a = o0 := Fin.ext ha
    have hb' : b = o1 := Fin.ext hb
    subst a; subst b
    simp [odd_substituents_zero_one, odd_substituents_one_zero]
  · have ha' : a = o1 := Fin.ext ha
    have hb' : b = o0 := Fin.ext hb
    subst a; subst b
    simp [odd_substituents_one_zero, odd_substituents_zero_one]
  · have ha' : a = o1 := Fin.ext ha
    have hb' : b = o2 := Fin.ext hb
    subst a; subst b
    simp [odd_substituents_one_two, odd_substituents_two_one]
  · have ha' : a = o2 := Fin.ext ha
    have hb' : b = o1 := Fin.ext hb
    subst a; subst b
    simp [odd_substituents_two_one, odd_substituents_one_two]
  · have ha' : a = o2 := Fin.ext ha
    have hb' : b = o3 := Fin.ext hb
    subst a; subst b
    simp [odd_substituents_two_three, odd_substituents_three_two]
  · have ha' : a = o3 := Fin.ext ha
    have hb' : b = o2 := Fin.ext hb
    subst a; subst b
    simp [odd_substituents_three_two, odd_substituents_two_three]
  · have ha' : a = o4 := Fin.ext ha
    have hb' : b = o5 := Fin.ext hb
    subst a; subst b
    simp [odd_substituents_four_five, odd_substituents_five_four]
  · have ha' : a = o5 := Fin.ext ha
    have hb' : b = o4 := Fin.ext hb
    subst a; subst b
    simp [odd_substituents_five_four, odd_substituents_four_five]
  · have ha' : a = o5 := Fin.ext ha
    have hb' : b = o6 := Fin.ext hb
    subst a; subst b
    simp [odd_substituents_five_six, odd_substituents_six_five]
  · have ha' : a = o6 := Fin.ext ha
    have hb' : b = o5 := Fin.ext hb
    subst a; subst b
    simp [odd_substituents_six_five, odd_substituents_five_six]
  · have ha' : a = o6 := Fin.ext ha
    have hb' : b = o7 := Fin.ext hb
    subst a; subst b
    simp [odd_substituents_six_seven, odd_substituents_seven_six]
  · have ha' : a = o7 := Fin.ext ha
    have hb' : b = o6 := Fin.ext hb
    subst a; subst b
    simp [odd_substituents_seven_six, odd_substituents_six_seven]

/-! ## Reflection of declarative odd-cumulene frames into the executable detector -/

/-- The declarative right cursor of an odd-cumulene frame is a valid reroot cursor.  This is the
same carrier-parent half of the cut neighbourhood already used for complete endpoint frames. -/
theorem oddDeclarativeFrame_rightCursor_valid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (derived :
      input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence frame) :
    input.LocalizedRerootCursorValid frame.initial.rightCursor := by
  rcases derived with ⟨physical, _terminal, _walkDecl, _reverseIdentity, _rightPartnerEq,
    _rightEq, _countLt, _countOdd⟩
  rcases physical with ⟨_real, _current, _parent, _bond, parentDecl, _leftCurrent,
    _leftPrevious, rightOccurrence, rightPrevious⟩
  have parentInNeighbors : frame.initial.leftCursor.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) occurrence.1 := by
    rw [localizedRerootNeighborFrames, List.mem_append]
    exact Or.inl parentDecl
  unfold LocalizedRerootCursorValid
  rw [rightPrevious, rightOccurrence]
  exact input.mem_localizedRerootNeighborFrames_symm occurrence
    frame.initial.leftCursor.occurrence.1 parentInNeighbors

/-- The odd-cumulene endpoint walk is covered by the production traversal fuel. -/
theorem oddEndpointWalk_length_le_traversalFuel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (derived :
      input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence frame) :
    frame.rightward.length ≤ input.localizedRule3CumulatedTraversalFuel carrierFuel + 1 := by
  have rightValid := oddDeclarativeFrame_rightCursor_valid input occurrence frame derived
  rcases derived with ⟨_physical, _terminal, walkDecl, _reverseIdentity, _rightPartnerEq,
    _rightEq, _countLt, _countOdd⟩
  have steps := declarativeWalk_steps_le_budget input frame.initial.rightCursor
    frame.rightward walkDecl rightValid
  have pos := input.declarativeWalk_length_pos walkDecl
  have budgetBound := input.localizedRerootCursorBudget_le_twice frame.initial.rightCursor
  simp only [localizedRule3CumulatedTraversalFuel, localizedOccurrenceRerootEvaluationFuel]
  omega

/-- Every declarative odd-cumulene endpoint frame is returned by the executable detector, provided
the traversal fuel covers the walk.  The oddness guard is discharged by the declarative parity. -/
theorem localizedRule3OddCumuleneEndpointCursorFrame?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (walkBound : frame.rightward.length ≤ traversalFuel + 1)
    (derived :
      input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence frame) :
    input.localizedRule3OddCumuleneEndpointCursorFrame? traversalFuel occurrence = some frame := by
  rcases derived with ⟨physical, terminal, walkDecl, reverseIdentity, rightPartnerEq, rightEq,
    _countLt, _countOdd⟩
  rcases frame with ⟨initial, rightward, rightPartnerCursor, rightCursor, rightPartner, right⟩
  have initialComputed :
      input.localizedRule3PhysicalEndpointCursorFrame? occurrence = some initial :=
    input.localizedRule3PhysicalEndpointCursorFrame?_eq_some_of_declarative
      occurrence initial physical
  have terminalComputed :
      input.localizedRule3AxisTopology? initial.leftCursor = some .terminal :=
    input.localizedRule3AxisTopology?_eq_terminal_of_declarative terminal
  have walkComputed :
      input.walkLocalizedRule3CumulatedAxis? traversalFuel initial.rightCursor =
        some rightward :=
    input.walkLocalizedRule3CumulatedAxis?_eq_some_of_declarative traversalFuel
      initial.rightCursor rightward walkDecl walkBound
  obtain ⟨rest, restEq⟩ := reverseIdentity
  have guard : 1 < rightward.length ∧ Odd rightward.length := by
    constructor
    · simpa [LocalizedRule3OddCumuleneEndpointCursorFrame.doubleBondCount] using _countLt
    · simpa [LocalizedRule3OddCumuleneEndpointCursorFrame.doubleBondCount] using _countOdd
  unfold localizedRule3OddCumuleneEndpointCursorFrame?
  rw [initialComputed]
  simp only [bind, Option.bind_some]
  rw [terminalComputed]
  simp only [Option.bind_some]
  rw [walkComputed]
  simp only [Option.bind_some]
  rw [restEq]
  try dsimp only
  rw [dif_pos guard]
  try dsimp only
  try simp only [bind, Option.bind_some]
  rw [rightPartnerEq]
  try dsimp only
  try simp only [Option.bind_some]
  rw [rightEq]
  try dsimp only
  try simp only [Option.bind_some]

/-- Executable twin of odd-cumulene frame completeness. -/
theorem localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (walkBound : frame.rightward.length ≤ traversalFuel + 1)
    (derived :
      input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence frame) :
    input.localizedRule3OddCumuleneEndpointCursorFrameExec? traversalFuel occurrence = some frame := by
  rw [localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_original input traversalFuel occurrence]
  exact localizedRule3OddCumuleneEndpointCursorFrame?_eq_some_of_declarative
    input traversalFuel occurrence frame walkBound derived

/-- Every declarative odd-cumulene endpoint frame is returned by the executable detector at the
production traversal fuel. -/
theorem localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_some_at_traversalFuel_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (derived :
      input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence frame) :
    input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some frame :=
  localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_some_of_declarative
    input (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence frame
    (oddEndpointWalk_length_le_traversalFuel input occurrence frame derived) derived

/-! ## Exact outward structure of a declarative linear axis step

A cursor reached outward from its incoming carrier parent has no surviving parent-side child: the
only shorter-address neighbour is exactly the cut incoming coordinate.  Consequently a declarative
`.linear` continuation of such a cursor is an outward immediate official child, hence its atom is
fresh for the stored branch history and its history is the new atom consed onto the old history. -/

theorem linearStep_fresh
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor next : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (outward : ∃ slot, cursor.occurrence.1.address = previous.1.address ++ [slot])
    (topology : input.DeclarativeLocalizedRule3AxisTopology cursor (.linear next)) :
    ∃ current nextAtom,
      cursor.occurrence.1.node.current? = some current ∧
      next.occurrence.1.node.current? = some nextAtom ∧
      input.moleculeGraph.bond current nextAtom = 2 ∧
      nextAtom ∉ cursor.occurrence.1.node.history ∧
      next.occurrence.1.node.history =
        nextAtom :: cursor.occurrence.1.node.history ∧
      (∃ slot, next.occurrence.1.address =
        cursor.occurrence.1.address ++ [slot]) := by
  cases topology with
  | linear frame real =>
      rcases frame with ⟨children, childrenComputed, _declarativeChildren, membership⟩
      have nextIn : next ∈ children := ((membership next).mp (by simp)).1
      rcases ((membership next).mp (by simp)).2 with
        ⟨_cursorReal, childProv, currentBond⟩
      have childrenEq :
          children = input.executableLocalizedRerootChildren cursor := by
        apply Option.some.inj
        rw [← childrenComputed]
        exact input.localizedRerootChildren?_eq_some_executable cursor
      have nextExec : next ∈ input.executableLocalizedRerootChildren cursor := by
        rw [← childrenEq]
        exact nextIn
      have nextIntended :
          next.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames cursor := by
        have mapEq := input.executableLocalizedRerootChildren_map cursor
        rw [← mapEq]
        exact List.mem_map.mpr ⟨next, nextExec, rfl⟩
      have cut : next.occurrence.1.address ≠ previous.1.address :=
        input.address_ne_previous_of_mem_intended cursor previous previousEq
          next.occurrence.1 nextIntended
      rcases input.executableLocalizedRerootChild_dichotomy cursor next nextExec with
        parent | outwardNext
      · exfalso
        apply cut
        rcases outward with ⟨outwardSlot, cursorAddress⟩
        rw [parent.2, cursorAddress]
        simp
      · have neighbor :=
          input.mem_localizedRerootNeighborFrames_of_mem_intended cursor
            next.occurrence.1 nextIntended
        have adjacent :=
          (input.mem_localizedRerootNeighborFrames_iff cursor.occurrence.1
            next.occurrence.1).mp neighbor
        have sameRoot : next.occurrence.1.root = cursor.occurrence.1.root :=
          adjacent.2.1
        have cursorDerived :
            input.DeclarativeLocalizedOccurrence carrierFuel cursor.occurrence.1 :=
          (input.mem_localizedOccurrences_iff carrierFuel cursor.occurrence.1).mp
            cursor.occurrence.2
        have nextDerived :
            input.DeclarativeLocalizedOccurrence carrierFuel next.occurrence.1 :=
          (input.mem_localizedOccurrences_iff carrierFuel next.occurrence.1).mp
            next.occurrence.2
        have outwardNextKept := outwardNext
        rcases outwardNext with ⟨slot, nextAddress⟩
        obtain ⟨childNode, childAtSlot, nextFrame⟩ :=
          input.declarativeLocalizedOccurrence_immediate_child cursorDerived
            nextDerived sameRoot slot nextAddress
        have nodeEq : next.occurrence.1.node = childNode :=
          congrArg LocalizedCIPOccurrenceFrame.node nextFrame
        have childMem :
            childNode ∈ input.executableOfficialCIPChildren cursor.occurrence.1.node :=
          List.fst_mem_of_mem_zipIdx childAtSlot
        have childPhysical :
            childNode.provenance = OfficialCIPNodeProvenance.realAtom ∨
              ∃ distance, childNode.provenance =
                OfficialCIPNodeProvenance.ringDuplicate distance := by
          cases childProvenance : childNode.provenance with
          | realAtom =>
              exact Or.inl rfl
          | ringDuplicate distance =>
              exact Or.inr ⟨distance, rfl⟩
          | multipleBondDuplicate distance =>
              exfalso
              have rewritten :
                  next.occurrence.1.node.provenance =
                    OfficialCIPNodeProvenance.multipleBondDuplicate distance := by
                rw [nodeEq]
                exact childProvenance
              rw [rewritten] at childProv
              simp [LocalizedRule3PhysicalReferenceProvenance] at childProv
          | placeholder kind distance =>
              exfalso
              have rewritten :
                  next.occurrence.1.node.provenance =
                    OfficialCIPNodeProvenance.placeholder kind distance := by
                rw [nodeEq]
                exact childProvenance
              rw [rewritten] at childProv
              simp [LocalizedRule3PhysicalReferenceProvenance] at childProv
        obtain ⟨nextAtom, extendEq, _notParent⟩ :=
          input.eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
            cursor.occurrence.1.node childNode childMem childPhysical
        have nextCurrent : next.occurrence.1.node.current? = some nextAtom := by
          rw [nodeEq, extendEq]
          rfl
        have historyEq : next.occurrence.1.node.history =
            nextAtom :: cursor.occurrence.1.node.history := by
          rw [nodeEq, extendEq]
          rfl
        have fresh : nextAtom ∉ cursor.occurrence.1.node.history := by
          have provenanceReal :
              (cursor.occurrence.1.node.extend nextAtom 0).provenance =
                OfficialCIPNodeProvenance.realAtom := by
            rw [← extendEq, ← nodeEq]
            exact real
          rw [OfficialCIPNode.extend_provenance] at provenanceReal
          by_contra present
          rw [OfficialCIPNode.childProvenance] at provenanceReal
          rw [if_pos rfl, if_pos present] at provenanceReal
          simp at provenanceReal
        have currentBondExists :
            ∃ current, cursor.occurrence.1.node.current? = some current ∧
              input.moleculeGraph.bond current nextAtom = 2 := by
          cases cursorCurrent : cursor.occurrence.1.node.current? with
          | none =>
              simp [cursorCurrent] at currentBond
          | some current =>
              have bondCurrent : input.moleculeGraph.bond current nextAtom = 2 := by
                simpa [cursorCurrent, nextCurrent] using currentBond
              exact ⟨current, rfl, bondCurrent⟩
        obtain ⟨current, cursorCurrent, bondCurrent⟩ := currentBondExists
        exact ⟨current, nextAtom, cursorCurrent, nextCurrent, bondCurrent, fresh,
          historyEq, outwardNextKept⟩

/-- A declarative cumulated walk is either the singleton terminal walk or begins with a linear
topology step. -/
theorem declarativeCumulatedAxisWalk_terminal_or_step
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {walk : List (input.LocalizedRerootCursor carrierFuel)}
    (declarative : input.DeclarativeLocalizedRule3CumulatedAxisWalk cursor walk) :
    walk = [cursor] ∨
      ∃ (next : input.LocalizedRerootCursor carrierFuel)
        (tail : List (input.LocalizedRerootCursor carrierFuel)),
        walk = cursor :: tail ∧
          input.DeclarativeLocalizedRule3AxisTopology cursor (.linear next) := by
  cases declarative with
  | terminal _ => exact Or.inl rfl
  | step topology _ => exact Or.inr ⟨_, _, rfl, topology⟩

/-! ## Actual six-coordinate readiness of the real difluoroethene axis -/

theorem difluoro_forward_ready :
    difluoroInput.LocalizedRule3AxisCoordinateGeometryReady f0 f1 f2 f4 f3 f5 := by
  refine ⟨PlanarDifluoroetheneExample.leftEndpoint,
    PlanarDifluoroetheneExample.rightEndpoint,
    PlanarDifluoroetheneExample.leftFirst,
    PlanarDifluoroetheneExample.leftSecond,
    PlanarDifluoroetheneExample.rightFirst,
    PlanarDifluoroetheneExample.rightSecond, 1, 0, 1, 0,
    difluoro_point_zero, difluoro_point_one, difluoro_point_two,
    difluoro_point_four, difluoro_point_three, difluoro_point_five,
    by norm_num, by norm_num,
    PlanarDifluoroetheneExample.referencePairReady.1,
    PlanarDifluoroetheneExample.referencePairReady.2,
    PlanarDifluoroetheneExample.leftArm,
    PlanarDifluoroetheneExample.rightArm⟩

theorem difluoro_reverse_reference :
    CartesianPoint3.Rule3ReferencePairReady
      PlanarDifluoroetheneExample.rightEndpoint
      PlanarDifluoroetheneExample.leftEndpoint
      PlanarDifluoroetheneExample.rightFirst
      PlanarDifluoroetheneExample.leftFirst := by
  constructor
  · rw [CartesianPoint3.rule3Coplanarity_swap]
    exact PlanarDifluoroetheneExample.referencePairReady.1
  · rw [CartesianPoint3.rule3SideProduct_swap]
    exact PlanarDifluoroetheneExample.referencePairReady.2

theorem difluoro_reverse_leftArm :
    RationalVector3.OppositeSideArm
      (CartesianPoint3.displacement PlanarDifluoroetheneExample.rightEndpoint
        PlanarDifluoroetheneExample.rightFirst)
      (CartesianPoint3.displacement PlanarDifluoroetheneExample.rightEndpoint
        PlanarDifluoroetheneExample.rightSecond)
      (CartesianPoint3.displacement PlanarDifluoroetheneExample.rightEndpoint
        PlanarDifluoroetheneExample.leftEndpoint) 1 0 := by
  apply RationalVector3.ext <;>
    simp [RationalVector3.OppositeSideArm, RationalVector3.vadd,
      RationalVector3.vsmul, CartesianPoint3.displacement,
      PlanarDifluoroetheneExample.leftEndpoint, PlanarDifluoroetheneExample.rightEndpoint,
      PlanarDifluoroetheneExample.rightFirst, PlanarDifluoroetheneExample.rightSecond]

theorem difluoro_reverse_rightArm :
    RationalVector3.OppositeSideArm
      (CartesianPoint3.displacement PlanarDifluoroetheneExample.leftEndpoint
        PlanarDifluoroetheneExample.leftFirst)
      (CartesianPoint3.displacement PlanarDifluoroetheneExample.leftEndpoint
        PlanarDifluoroetheneExample.leftSecond)
      (CartesianPoint3.displacement PlanarDifluoroetheneExample.rightEndpoint
        PlanarDifluoroetheneExample.leftEndpoint) 1 0 := by
  apply RationalVector3.ext <;>
    simp [RationalVector3.OppositeSideArm, RationalVector3.vadd,
      RationalVector3.vsmul, CartesianPoint3.displacement,
      PlanarDifluoroetheneExample.leftEndpoint, PlanarDifluoroetheneExample.rightEndpoint,
      PlanarDifluoroetheneExample.leftFirst, PlanarDifluoroetheneExample.leftSecond]

theorem difluoro_reverse_ready :
    difluoroInput.LocalizedRule3AxisCoordinateGeometryReady f1 f0 f3 f5 f2 f4 := by
  refine ⟨PlanarDifluoroetheneExample.rightEndpoint,
    PlanarDifluoroetheneExample.leftEndpoint,
    PlanarDifluoroetheneExample.rightFirst,
    PlanarDifluoroetheneExample.rightSecond,
    PlanarDifluoroetheneExample.leftFirst,
    PlanarDifluoroetheneExample.leftSecond, 1, 0, 1, 0,
    difluoro_point_one, difluoro_point_zero, difluoro_point_three,
    difluoro_point_five, difluoro_point_two, difluoro_point_four,
    by norm_num, by norm_num,
    difluoro_reverse_reference.1, difluoro_reverse_reference.2,
    difluoro_reverse_leftArm, difluoro_reverse_rightArm⟩

/-- **Every actual ordinary axis of the certified difluoroethene source is coordinate-ready, at
every carrier fuel.** -/
theorem difluoro_ordinary_domain (carrierFuel : Nat) :
    ∀ (occurrence : difluoroInput.LocalizedCIPOccurrence carrierFuel)
      (topology : difluoroInput.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
      (leftFirst leftSecond rightFirst rightSecond : difluoroInput.Atom),
      difluoroInput.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame occurrence topology →
      difluoroInput.localizedRule3ExplicitSubstituents topology.left topology.right =
          [leftFirst, leftSecond] →
      difluoroInput.localizedRule3ExplicitSubstituents topology.right topology.left =
          [rightFirst, rightSecond] →
      difluoroInput.LocalizedRule3AxisCoordinateGeometryReady topology.left topology.right
        leftFirst leftSecond rightFirst rightSecond := by
  intro occurrence topology leftFirst leftSecond rightFirst rightSecond
    declarative leftCandidates rightCandidates
  have bondEq : difluoroInput.moleculeGraph.bond topology.left topology.right = 2 :=
    declarative.2.2.2.1
  rcases difluoro_bond_two_characterization topology.left topology.right bondEq with
    ⟨leftZero, rightOne⟩ | ⟨leftOne, rightZero⟩
  · have leftEq : topology.left = f0 := Fin.ext leftZero
    have rightEq : topology.right = f1 := Fin.ext rightOne
    rw [leftEq, rightEq] at leftCandidates rightCandidates ⊢
    rw [difluoro_substituents_zero_one] at leftCandidates
    rw [difluoro_substituents_one_zero] at rightCandidates
    simp only [List.cons.injEq, List.nil_eq, and_true] at leftCandidates rightCandidates
    obtain ⟨leftFirstEq, leftSecondEq⟩ := leftCandidates
    obtain ⟨rightFirstEq, rightSecondEq⟩ := rightCandidates
    subst leftFirst
    subst leftSecond
    subst rightFirst
    subst rightSecond
    exact difluoro_forward_ready
  · have leftEq : topology.left = f1 := Fin.ext leftOne
    have rightEq : topology.right = f0 := Fin.ext rightZero
    rw [leftEq, rightEq] at leftCandidates rightCandidates ⊢
    rw [difluoro_substituents_one_zero] at leftCandidates
    rw [difluoro_substituents_zero_one] at rightCandidates
    simp only [List.cons.injEq, List.nil_eq, and_true] at leftCandidates rightCandidates
    obtain ⟨leftFirstEq, leftSecondEq⟩ := leftCandidates
    obtain ⟨rightFirstEq, rightSecondEq⟩ := rightCandidates
    subst leftFirst
    subst leftSecond
    subst rightFirst
    subst rightSecond
    exact difluoro_reverse_ready

/-- The odd branch of the difluoroethene domain is vacuous.  The initial right cursor is outward
from its carrier parent, so its unique order-two continuation would have to be the parent carbon,
which is already in the stored branch history. -/
theorem difluoro_no_odd_frame (carrierFuel : Nat)
    (occurrence : difluoroInput.LocalizedCIPOccurrence carrierFuel)
    (frame : difluoroInput.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (derived :
      difluoroInput.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence frame) :
    False := by
  rcases derived with ⟨physicalDecl, _terminal, walkDecl, _reverse, _rightPartner,
    _rightCursor, countLt, _countOdd⟩
  rcases physicalDecl with ⟨_real, occurrenceCurrent, occurrenceParent, bondLR,
    parentDecl, _leftCurrent, _leftPrevious, rightOccurrence, rightPrevious⟩
  have startCurrent :
      frame.initial.rightCursor.occurrence.1.node.current? = some frame.initial.right := by
    rw [rightOccurrence]
    exact occurrenceCurrent
  have startParent :
      frame.initial.rightCursor.occurrence.1.node.parent? = some frame.initial.left := by
    rw [rightOccurrence]
    exact occurrenceParent
  have startDerived :
      difluoroInput.DeclarativeLocalizedOccurrence carrierFuel
        frame.initial.rightCursor.occurrence.1 :=
    (difluoroInput.mem_localizedOccurrences_iff carrierFuel
      frame.initial.rightCursor.occurrence.1).mp
      frame.initial.rightCursor.occurrence.2
  have startHead : frame.initial.rightCursor.occurrence.1.node.history.head? =
      frame.initial.rightCursor.occurrence.1.node.current? :=
    difluoroInput.declarativeLocalizedOccurrence_history_head_eq_current startDerived
  have leftParentIn :
      frame.initial.leftCursor.occurrence.1 ∈
        difluoroInput.localizedCarrierParentFrames (fuel := carrierFuel)
          frame.initial.rightCursor.occurrence.1 := by
    rw [rightOccurrence]
    exact parentDecl
  have parentShape :
      frame.initial.leftCursor.occurrence.1.address.length + 1 =
          frame.initial.rightCursor.occurrence.1.address.length ∧
        frame.initial.leftCursor.occurrence.1.address =
          frame.initial.rightCursor.occurrence.1.address.dropLast := by
    simp only [CertifiedLocalizedCIPInput.localizedCarrierParentFrames,
      List.mem_filter] at leftParentIn
    rcases leftParentIn with ⟨_carrier, conditions⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at conditions
    exact ⟨conditions.1.2, conditions.2⟩
  have outwardStart : ∃ slot,
      frame.initial.rightCursor.occurrence.1.address =
        frame.initial.leftCursor.occurrence.1.address ++ [slot] :=
    exists_eq_append_singleton_of_eq_dropLast parentShape.1 parentShape.2
  rcases declarativeCumulatedAxisWalk_terminal_or_step difluoroInput walkDecl with
    terminalWalk | ⟨next, tail, stepWalk, topology⟩
  · exfalso
    unfold LocalizedRule3OddCumuleneEndpointCursorFrame.doubleBondCount at countLt
    rw [terminalWalk] at countLt
    have impossible : ¬ (1 < ([frame.initial.rightCursor] : List
        (difluoroInput.LocalizedRerootCursor carrierFuel)).length) := by simp
    exact impossible countLt
  · obtain ⟨current, nextAtom, cursorCurrent, nextCurrent, bondNext, fresh, historyEq,
      _outwardNext⟩ :=
      linearStep_fresh difluoroInput frame.initial.rightCursor next
        frame.initial.leftCursor.occurrence rightPrevious outwardStart topology
    have currentEq : current = frame.initial.right := by
      rw [startCurrent] at cursorCurrent
      exact (Option.some.inj cursorCurrent).symm
    subst current
    have nextEqLeft : nextAtom = frame.initial.left := by
      apply Fin.ext
      rcases difluoro_bond_two_characterization frame.initial.left frame.initial.right
        bondLR with ⟨leftZero, rightOne⟩ | ⟨leftOne, rightZero⟩ <;>
        rcases difluoro_bond_two_characterization frame.initial.right nextAtom
          bondNext with ⟨rightZero, nextOne⟩ | ⟨rightOne, nextZero⟩ <;>
        simp_all
    have historyShape : ∃ tail, frame.initial.rightCursor.occurrence.1.node.history =
        frame.initial.right :: frame.initial.left :: tail := by
      have headObserved :
          frame.initial.rightCursor.occurrence.1.node.history.head? =
            some frame.initial.right := startHead.trans startCurrent
      obtain ⟨rest, historyRest⟩ := List.head?_eq_some_iff.mp headObserved
      cases rest with
      | nil =>
          simp [OfficialCIPNode.parent?, historyRest] at startParent
      | cons second tail =>
          have parentComputed :
              frame.initial.rightCursor.occurrence.1.node.parent? = some second := by
            unfold OfficialCIPNode.parent?
            rw [historyRest]
          have secondEq : second = frame.initial.left := by
            rw [parentComputed] at startParent
            exact Option.some.inj startParent
          subst second
          exact ⟨tail, historyRest⟩
    obtain ⟨historyTail, historyRest⟩ := historyShape
    have leftMem : frame.initial.left ∈
        frame.initial.rightCursor.occurrence.1.node.history := by
      rw [historyRest]
      simp
    exact fresh (by simpa [nextEqLeft] using leftMem)

/-- The ordinary branch of the odd-cumulene domain is vacuous at every carrier fuel: the actual
candidate lists never both have length two. -/
theorem odd_ordinary_domain (carrierFuel : Nat) :
    ∀ (occurrence : oddInput.LocalizedCIPOccurrence carrierFuel)
      (topology : oddInput.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
      (leftFirst leftSecond rightFirst rightSecond : oddInput.Atom),
      oddInput.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame occurrence topology →
      oddInput.localizedRule3ExplicitSubstituents topology.left topology.right =
          [leftFirst, leftSecond] →
      oddInput.localizedRule3ExplicitSubstituents topology.right topology.left =
          [rightFirst, rightSecond] →
      oddInput.LocalizedRule3AxisCoordinateGeometryReady topology.left topology.right
        leftFirst leftSecond rightFirst rightSecond := by
  intro occurrence topology leftFirst leftSecond rightFirst rightSecond
    declarative leftCandidates rightCandidates
  have bondEq : oddInput.moleculeGraph.bond topology.left topology.right = 2 :=
    declarative.2.2.2.1
  have bothTwo :
      (oddInput.localizedRule3ExplicitSubstituents topology.left topology.right).length = 2 ∧
        (oddInput.localizedRule3ExplicitSubstituents topology.right topology.left).length = 2 :=
    ⟨by rw [leftCandidates]; rfl, by rw [rightCandidates]; rfl⟩
  rcases odd_no_ordinary_double_candidate_axis topology.left topology.right bondEq with
    notTwo | notTwo
  · exact absurd bothTwo.1 notTwo
  · exact absurd bothTwo.2 notTwo

/-! ## Actual six-coordinate readiness of the four real odd-cumulene axes

The certified odd fixture has two physical cumulated units `0=1=2=3` and `4=5=6=7`.  Only the
oriented terminal-start frames `0→3`, `3→0`, `4→7`, and `7→4` have an odd complete walk, and their
actual certified coordinates are in the plane `z = 0` with the two substituents on opposite sides of
the axis.  The four exact readiness facts below are read from the source points. -/

theorem odd_ready_zero_three :
    oddInput.LocalizedRule3AxisCoordinateGeometryReady o0 o3 o8 o9 o4 o12 := by
  refine ⟨q0, q3, q8, q9, q4, q12, 1, 0, 1, 0,
    odd_point_zero, odd_point_three, odd_point_eight, odd_point_nine,
    odd_point_four, odd_point_twelve, by norm_num, by norm_num,
    ?_, ?_, ?_, ?_⟩
  · norm_num [CartesianPoint3.rule3Coplanarity, CartesianPoint3.displacement,
      RationalVector3.dot, RationalVector3.cross, q0, q3, q8, q4]
  · norm_num [CartesianPoint3.rule3SideProduct, CartesianPoint3.displacement,
      RationalVector3.dot, RationalVector3.cross, q0, q3, q8, q4]
  · apply RationalVector3.ext <;>
      simp [RationalVector3.OppositeSideArm, RationalVector3.vadd,
        RationalVector3.vsmul, CartesianPoint3.displacement, q0, q3, q8, q9]
  · apply RationalVector3.ext <;>
      simp [RationalVector3.OppositeSideArm, RationalVector3.vadd,
        RationalVector3.vsmul, CartesianPoint3.displacement, q0, q3, q4, q12]

theorem odd_ready_three_zero :
    oddInput.LocalizedRule3AxisCoordinateGeometryReady o3 o0 o4 o12 o8 o9 := by
  refine ⟨q3, q0, q4, q12, q8, q9, 1, 0, 1, 0,
    odd_point_three, odd_point_zero, odd_point_four, odd_point_twelve,
    odd_point_eight, odd_point_nine, by norm_num, by norm_num,
    ?_, ?_, ?_, ?_⟩
  · norm_num [CartesianPoint3.rule3Coplanarity, CartesianPoint3.displacement,
      RationalVector3.dot, RationalVector3.cross, q3, q0, q4, q8]
  · norm_num [CartesianPoint3.rule3SideProduct, CartesianPoint3.displacement,
      RationalVector3.dot, RationalVector3.cross, q3, q0, q4, q8]
  · apply RationalVector3.ext <;>
      simp [RationalVector3.OppositeSideArm, RationalVector3.vadd,
        RationalVector3.vsmul, CartesianPoint3.displacement, q3, q0, q4, q12]
  · apply RationalVector3.ext <;>
      simp [RationalVector3.OppositeSideArm, RationalVector3.vadd,
        RationalVector3.vsmul, CartesianPoint3.displacement, q3, q0, q8, q9]

theorem odd_ready_four_seven :
    oddInput.LocalizedRule3AxisCoordinateGeometryReady o4 o7 o3 o13 o10 o11 := by
  refine ⟨q4, q7, q3, q13, q10, q11, 1, 0, 1, 0,
    odd_point_four, odd_point_seven, odd_point_three, odd_point_thirteen,
    odd_point_ten, odd_point_eleven, by norm_num, by norm_num,
    ?_, ?_, ?_, ?_⟩
  · norm_num [CartesianPoint3.rule3Coplanarity, CartesianPoint3.displacement,
      RationalVector3.dot, RationalVector3.cross, q4, q7, q3, q10]
  · norm_num [CartesianPoint3.rule3SideProduct, CartesianPoint3.displacement,
      RationalVector3.dot, RationalVector3.cross, q4, q7, q3, q10]
  · apply RationalVector3.ext <;>
      simp [RationalVector3.OppositeSideArm, RationalVector3.vadd,
        RationalVector3.vsmul, CartesianPoint3.displacement, q4, q7, q3, q13]
    norm_num
  · apply RationalVector3.ext <;>
      simp [RationalVector3.OppositeSideArm, RationalVector3.vadd,
        RationalVector3.vsmul, CartesianPoint3.displacement, q4, q7, q10, q11]
    norm_num

theorem odd_ready_seven_four :
    oddInput.LocalizedRule3AxisCoordinateGeometryReady o7 o4 o10 o11 o3 o13 := by
  refine ⟨q7, q4, q10, q11, q3, q13, 1, 0, 1, 0,
    odd_point_seven, odd_point_four, odd_point_ten, odd_point_eleven,
    odd_point_three, odd_point_thirteen, by norm_num, by norm_num,
    ?_, ?_, ?_, ?_⟩
  · norm_num [CartesianPoint3.rule3Coplanarity, CartesianPoint3.displacement,
      RationalVector3.dot, RationalVector3.cross, q7, q4, q10, q3]
  · norm_num [CartesianPoint3.rule3SideProduct, CartesianPoint3.displacement,
      RationalVector3.dot, RationalVector3.cross, q7, q4, q10, q3]
  · apply RationalVector3.ext <;>
      simp [RationalVector3.OppositeSideArm, RationalVector3.vadd,
        RationalVector3.vsmul, CartesianPoint3.displacement, q7, q4, q10, q11]
    norm_num
  · apply RationalVector3.ext <;>
      simp [RationalVector3.OppositeSideArm, RationalVector3.vadd,
        RationalVector3.vsmul, CartesianPoint3.displacement, q7, q4, q3, q13]
    norm_num

/-! ## Fixed actual carrier depth for the odd fixture -/

/-- The legitimate fixed carrier depth `atomCount + 1` of the odd fixture. -/
def oddCarrierFuel : Nat := 15

/-- The production cumulated traversal fuel at the fixed carrier depth. -/
def oddTraversalFuel : Nat :=
  oddInput.localizedRule3CumulatedTraversalFuel oddCarrierFuel

/-! ## Exhaustive order-two neighbours of the cumulated chain

The eight single-double-bond atoms of the two cumulated units have the expected actual
order-two neighbour sets.  These are read from the certified adjacency relation and are used to
classify every declarative odd walk of the fixture. -/

theorem odd_bond_two_zero (x : oddInput.Atom)
    (bond : oddInput.moleculeGraph.bond o0 x = 2) : x = o1 := by
  rcases odd_bond_two_characterization o0 x bond with
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Fin.ext (by simpa using hb)
  all_goals (simp only [o0] at ha; omega)

theorem odd_bond_two_one (x : oddInput.Atom)
    (bond : oddInput.moleculeGraph.bond o1 x = 2) : x = o0 ∨ x = o2 := by
  rcases odd_bond_two_characterization o1 x bond with
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exfalso; simp only [o1] at ha; omega
  · exact Or.inl (Fin.ext (by simpa using hb))
  · exact Or.inr (Fin.ext (by simpa using hb))
  all_goals (simp only [o1] at ha; omega)

theorem odd_bond_two_two (x : oddInput.Atom)
    (bond : oddInput.moleculeGraph.bond o2 x = 2) : x = o1 ∨ x = o3 := by
  rcases odd_bond_two_characterization o2 x bond with
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exfalso; simp only [o2] at ha; omega
  · exfalso; simp only [o2] at ha; omega
  · exfalso; simp only [o2] at ha; omega
  · exact Or.inl (Fin.ext (by simpa using hb))
  · exact Or.inr (Fin.ext (by simpa using hb))
  all_goals (simp only [o2] at ha; omega)

theorem odd_bond_two_three (x : oddInput.Atom)
    (bond : oddInput.moleculeGraph.bond o3 x = 2) : x = o2 := by
  rcases odd_bond_two_characterization o3 x bond with
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exfalso; simp only [o3] at ha; omega
  · exfalso; simp only [o3] at ha; omega
  · exfalso; simp only [o3] at ha; omega
  · exfalso; simp only [o3] at ha; omega
  · exfalso; simp only [o3] at ha; omega
  · exact Fin.ext (by simpa using hb)
  all_goals (simp only [o3] at ha; omega)

theorem odd_bond_two_four (x : oddInput.Atom)
    (bond : oddInput.moleculeGraph.bond o4 x = 2) : x = o5 := by
  rcases odd_bond_two_characterization o4 x bond with
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exfalso; simp only [o4] at ha; omega
  · exfalso; simp only [o4] at ha; omega
  · exfalso; simp only [o4] at ha; omega
  · exfalso; simp only [o4] at ha; omega
  · exfalso; simp only [o4] at ha; omega
  · exfalso; simp only [o4] at ha; omega
  · exact Fin.ext (by simpa using hb)
  all_goals (simp only [o4] at ha; omega)

theorem odd_bond_two_five (x : oddInput.Atom)
    (bond : oddInput.moleculeGraph.bond o5 x = 2) : x = o4 ∨ x = o6 := by
  rcases odd_bond_two_characterization o5 x bond with
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exfalso; simp only [o5] at ha; omega
  · exfalso; simp only [o5] at ha; omega
  · exfalso; simp only [o5] at ha; omega
  · exfalso; simp only [o5] at ha; omega
  · exfalso; simp only [o5] at ha; omega
  · exfalso; simp only [o5] at ha; omega
  · exfalso; simp only [o5] at ha; omega
  · exact Or.inl (Fin.ext (by simpa using hb))
  · exact Or.inr (Fin.ext (by simpa using hb))
  all_goals (simp only [o5] at ha; omega)

theorem odd_bond_two_six (x : oddInput.Atom)
    (bond : oddInput.moleculeGraph.bond o6 x = 2) : x = o5 ∨ x = o7 := by
  rcases odd_bond_two_characterization o6 x bond with
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exfalso; simp only [o6] at ha; omega
  · exfalso; simp only [o6] at ha; omega
  · exfalso; simp only [o6] at ha; omega
  · exfalso; simp only [o6] at ha; omega
  · exfalso; simp only [o6] at ha; omega
  · exfalso; simp only [o6] at ha; omega
  · exfalso; simp only [o6] at ha; omega
  · exfalso; simp only [o6] at ha; omega
  · exfalso; simp only [o6] at ha; omega
  · exact Or.inl (Fin.ext (by simpa using hb))
  · exact Or.inr (Fin.ext (by simpa using hb))
  all_goals (simp only [o6] at ha; omega)

theorem odd_bond_two_seven (x : oddInput.Atom)
    (bond : oddInput.moleculeGraph.bond o7 x = 2) : x = o6 := by
  rcases odd_bond_two_characterization o7 x bond with
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exfalso; simp only [o7] at ha; omega
  · exfalso; simp only [o7] at ha; omega
  · exfalso; simp only [o7] at ha; omega
  · exfalso; simp only [o7] at ha; omega
  · exfalso; simp only [o7] at ha; omega
  · exfalso; simp only [o7] at ha; omega
  · exfalso; simp only [o7] at ha; omega
  · exfalso; simp only [o7] at ha; omega
  · exfalso; simp only [o7] at ha; omega
  · exfalso; simp only [o7] at ha; omega
  · exfalso; simp only [o7] at ha; omega
  · exact Fin.ext (by simpa using hb)

/-! ## Forcing the shape of a declarative odd walk

Because the starting right cursor is outward from its carrier parent, each linear step of a
declarative cumulated walk is an outward immediate official child: its atom is fresh for the
stored branch history and its history is the new atom consed onto the old history.  Combined
with the exhaustive order-two neighbour sets above, this determines the shape of every odd walk
of the fixture. -/

theorem declarativeWalk_step_data
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {walk : List (input.LocalizedRerootCursor carrierFuel)}
    (walkDecl : input.DeclarativeLocalizedRule3CumulatedAxisWalk cursor walk)
    (lengthLt : 1 < walk.length)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (outward : ∃ slot, cursor.occurrence.1.address = previous.1.address ++ [slot]) :
    ∃ (next : input.LocalizedRerootCursor carrierFuel)
      (rest : List (input.LocalizedRerootCursor carrierFuel))
      (current nextAtom : input.Atom),
      walk = cursor :: rest ∧
        input.DeclarativeLocalizedRule3CumulatedAxisWalk next rest ∧
        rest.length + 1 = walk.length ∧
        cursor.occurrence.1.node.current? = some current ∧
        next.occurrence.1.node.current? = some nextAtom ∧
        input.moleculeGraph.bond current nextAtom = 2 ∧
        nextAtom ∉ cursor.occurrence.1.node.history ∧
        next.occurrence.1.node.history =
          nextAtom :: cursor.occurrence.1.node.history ∧
        next.previous? = some cursor.occurrence ∧
        (∃ slot, next.occurrence.1.address =
          cursor.occurrence.1.address ++ [slot]) := by
  cases walkDecl with
  | terminal _ =>
      exfalso
      have impossible : ¬ (1 < ([cursor] : List
          (input.LocalizedRerootCursor carrierFuel)).length) := by simp
      exact impossible lengthLt
  | step topology restWalk =>
      obtain ⟨current, nextAtom, cursorCurrent, nextCurrent, bondNext, fresh, historyEq,
        outwardNext⟩ :=
        linearStep_fresh input cursor _ previous previousEq outward topology
      exact ⟨_, _, current, nextAtom, rfl, restWalk, rfl, cursorCurrent, nextCurrent,
        bondNext, fresh, historyEq,
        input.executableLocalizedRerootChildren_previous cursor _
          (declarativeLinearStep_edge input topology), outwardNext⟩

theorem declarativeWalk_terminal_of_no_fresh_double
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {walk : List (input.LocalizedRerootCursor carrierFuel)}
    (walkDecl : input.DeclarativeLocalizedRule3CumulatedAxisWalk cursor walk)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (outward : ∃ slot, cursor.occurrence.1.address = previous.1.address ++ [slot])
    (current : input.Atom)
    (currentEq : cursor.occurrence.1.node.current? = some current)
    (closed : ∀ x, input.moleculeGraph.bond current x = 2 →
      x ∈ cursor.occurrence.1.node.history) :
    walk = [cursor] := by
  cases walkDecl with
  | terminal _ => rfl
  | step topology restWalk =>
      exfalso
      obtain ⟨observedCurrent, nextAtom, cursorCurrent, _nextCurrent, bondNext, fresh,
        _historyEq, _outwardNext⟩ :=
        linearStep_fresh input cursor _ previous previousEq outward topology
      have currentEq' : observedCurrent = current := by
        rw [currentEq] at cursorCurrent
        exact (Option.some.inj cursorCurrent).symm
      rw [currentEq'] at bondNext
      exact fresh (closed nextAtom bondNext)

theorem declarativeWalk_impossible_of_start_leaf
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {walk : List (input.LocalizedRerootCursor carrierFuel)}
    (walkDecl : input.DeclarativeLocalizedRule3CumulatedAxisWalk cursor walk)
    (lengthLt : 1 < walk.length)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (outward : ∃ slot, cursor.occurrence.1.address = previous.1.address ++ [slot])
    (a b : input.Atom)
    (currentEq : cursor.occurrence.1.node.current? = some b)
    (aMem : a ∈ cursor.occurrence.1.node.history)
    (dead : ∀ x, input.moleculeGraph.bond b x = 2 → x = a) : False := by
  obtain ⟨_next, _rest, current, nextAtom, _walkEq, _restWalk, _restLen,
    cursorCurrent, _nextCurrent, bondNext, fresh, _historyEq, _nextPrev,
    _outwardNext⟩ :=
    declarativeWalk_step_data input walkDecl lengthLt previous previousEq outward
  have currentEq' : current = b := by
    rw [currentEq] at cursorCurrent
    exact (Option.some.inj cursorCurrent).symm
  rw [currentEq'] at bondNext
  rw [dead nextAtom bondNext] at fresh
  exact fresh aMem

theorem declarativeWalk_two_step_impossible
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {walk : List (input.LocalizedRerootCursor carrierFuel)}
    (walkDecl : input.DeclarativeLocalizedRule3CumulatedAxisWalk cursor walk)
    (lengthLt : 1 < walk.length)
    (oddLength : Odd walk.length)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (outward : ∃ slot, cursor.occurrence.1.address = previous.1.address ++ [slot])
    (a b c : input.Atom)
    (currentEq : cursor.occurrence.1.node.current? = some b)
    (aMem : a ∈ cursor.occurrence.1.node.history)
    (bMem : b ∈ cursor.occurrence.1.node.history)
    (bOptions : ∀ x, input.moleculeGraph.bond b x = 2 → x = a ∨ x = c)
    (cOptions : ∀ x, input.moleculeGraph.bond c x = 2 → x = b) : False := by
  obtain ⟨next1, rest1, current1, atom1, _walkEq1, restWalk1, restLen1,
    cursorCurrent1, nextCurrent1, bond1, fresh1, hist1, nextPrev1, out1⟩ :=
    declarativeWalk_step_data input walkDecl lengthLt previous previousEq outward
  have current1Eq : current1 = b := by
    rw [currentEq] at cursorCurrent1
    exact (Option.some.inj cursorCurrent1).symm
  rw [current1Eq] at bond1
  have atom1Eq : atom1 = c := by
    rcases bOptions atom1 bond1 with h | h
    · rw [h] at fresh1
      exact absurd aMem fresh1
    · exact h
  rw [atom1Eq] at nextCurrent1 hist1
  have walkLenGe3 : 2 < walk.length := by
    rcases oddLength with ⟨k, hk⟩
    omega
  have restLt : 1 < rest1.length := by omega
  obtain ⟨next2, _rest2, current2, atom2, _walkEq2, _restWalk2, _restLen2,
    nextCurrent2, next2Current, bond2, fresh2, hist2, _nextPrev2, _out2⟩ :=
    declarativeWalk_step_data input restWalk1 restLt cursor.occurrence nextPrev1 out1
  have current2Eq : current2 = c := by
    rw [nextCurrent1] at nextCurrent2
    exact (Option.some.inj nextCurrent2).symm
  rw [current2Eq] at bond2
  have atom2Eq : atom2 = b := cOptions atom2 bond2
  rw [atom2Eq] at fresh2
  have bInNext1 : b ∈ next1.occurrence.1.node.history := by
    rw [hist1]
    exact List.mem_cons_of_mem _ bMem
  exact fresh2 bInNext1

theorem declarativeWalk_forced_three
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {walk : List (input.LocalizedRerootCursor carrierFuel)}
    (walkDecl : input.DeclarativeLocalizedRule3CumulatedAxisWalk cursor walk)
    (lengthLt : 1 < walk.length)
    (oddLength : Odd walk.length)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (outward : ∃ slot, cursor.occurrence.1.address = previous.1.address ++ [slot])
    (a b c d : input.Atom)
    (currentEq : cursor.occurrence.1.node.current? = some b)
    (aMem : a ∈ cursor.occurrence.1.node.history)
    (bMem : b ∈ cursor.occurrence.1.node.history)
    (bOptions : ∀ x, input.moleculeGraph.bond b x = 2 → x = a ∨ x = c)
    (cOptions : ∀ x, input.moleculeGraph.bond c x = 2 → x = b ∨ x = d)
    (dOptions : ∀ x, input.moleculeGraph.bond d x = 2 → x = c) :
    ∃ (middle far : input.LocalizedRerootCursor carrierFuel),
      walk = [cursor, middle, far] ∧
        middle.occurrence.1.node.current? = some c ∧
        far.occurrence.1.node.current? = some d ∧
        middle.previous? = some cursor.occurrence ∧
        far.previous? = some middle.occurrence := by
  obtain ⟨next1, rest1, current1, atom1, walkEq1, restWalk1, restLen1,
    cursorCurrent1, nextCurrent1, bond1, fresh1, hist1, nextPrev1, out1⟩ :=
    declarativeWalk_step_data input walkDecl lengthLt previous previousEq outward
  have current1Eq : current1 = b := by
    rw [currentEq] at cursorCurrent1
    exact (Option.some.inj cursorCurrent1).symm
  rw [current1Eq] at bond1
  have atom1Eq : atom1 = c := by
    rcases bOptions atom1 bond1 with h | h
    · rw [h] at fresh1
      exact absurd aMem fresh1
    · exact h
  rw [atom1Eq] at nextCurrent1 hist1
  have walkLenGe3 : 2 < walk.length := by
    rcases oddLength with ⟨k, hk⟩
    omega
  have restLt : 1 < rest1.length := by omega
  obtain ⟨next2, rest2, current2, atom2, walkEq2, restWalk2, _restLen2,
    nextCurrent2, next2Current, bond2, fresh2, hist2, nextPrev2, out2⟩ :=
    declarativeWalk_step_data input restWalk1 restLt cursor.occurrence nextPrev1 out1
  have current2Eq : current2 = c := by
    rw [nextCurrent1] at nextCurrent2
    exact (Option.some.inj nextCurrent2).symm
  rw [current2Eq] at bond2
  have atom2Eq : atom2 = d := by
    rcases cOptions atom2 bond2 with h | h
    · exfalso
      apply fresh2
      rw [h, hist1]
      exact List.mem_cons_of_mem _ bMem
    · exact h
  rw [atom2Eq] at next2Current hist2
  have rest2Singleton : rest2 = [next2] :=
    declarativeWalk_terminal_of_no_fresh_double input restWalk2 next1.occurrence
      nextPrev2 out2 d next2Current
      (by
        intro x hx
        rw [dOptions x hx, hist2, hist1]
        simp)
  refine ⟨next1, next2, ?_, nextCurrent1, next2Current, nextPrev1, nextPrev2⟩
  rw [walkEq1, walkEq2, rest2Singleton]

/-- **The actual odd-cumulene coordinate geometry domain at the fixed legitimate carrier depth.**

Every declarative ordinary physical frame is impossible because every order-two edge of the
fixture has a singleton candidate list at one end.  Every declarative odd-cumulene endpoint frame
is forced by the actual graph into one of the four genuine terminal-to-terminal walks
`0→3`, `3→0`, `4→7`, `7→4`; the candidate lists are then the certified substituent lists, and the
four exact readiness theorems above close the branch. -/
theorem odd_domain_fixed :
    oddInput.LocalizedRule3AxisCoordinateGeometryDomain oddCarrierFuel := by
  refine ⟨odd_ordinary_domain oddCarrierFuel, ?_⟩
  intro occurrence topology leftFirst leftSecond rightFirst rightSecond declarative
    leftCandidates rightCandidates
  rcases declarative with ⟨physical, _terminal, walkDecl, reverseIdentity, rightPartnerEq,
    rightEq, countLt, countOdd⟩
  rcases physical with ⟨_real, occurrenceCurrent, occurrenceParent, bondLR, parentDecl,
    _leftCurrent, _leftPrevious, rightOccurrence, rightPrevious⟩
  have startCurrent :
      topology.initial.rightCursor.occurrence.1.node.current? =
        some topology.initial.right := by
    rw [rightOccurrence]
    exact occurrenceCurrent
  have startParent :
      topology.initial.rightCursor.occurrence.1.node.parent? =
        some topology.initial.left := by
    rw [rightOccurrence]
    exact occurrenceParent
  have startDerived :
      oddInput.DeclarativeLocalizedOccurrence oddCarrierFuel
        topology.initial.rightCursor.occurrence.1 :=
    (oddInput.mem_localizedOccurrences_iff oddCarrierFuel
      topology.initial.rightCursor.occurrence.1).mp
      topology.initial.rightCursor.occurrence.2
  have startHead :
      topology.initial.rightCursor.occurrence.1.node.history.head? =
        topology.initial.rightCursor.occurrence.1.node.current? :=
    oddInput.declarativeLocalizedOccurrence_history_head_eq_current startDerived
  have leftParentIn :
      topology.initial.leftCursor.occurrence.1 ∈
        oddInput.localizedCarrierParentFrames (fuel := oddCarrierFuel) occurrence.1 :=
    parentDecl
  have parentShape :
      topology.initial.leftCursor.occurrence.1.address.length + 1 =
          occurrence.1.address.length ∧
        topology.initial.leftCursor.occurrence.1.address =
          occurrence.1.address.dropLast := by
    simp only [CertifiedLocalizedCIPInput.localizedCarrierParentFrames,
      List.mem_filter] at leftParentIn
    rcases leftParentIn with ⟨_carrier, conditions⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at conditions
    exact ⟨conditions.1.2, conditions.2⟩
  have outwardStart : ∃ slot,
      topology.initial.rightCursor.occurrence.1.address =
        topology.initial.leftCursor.occurrence.1.address ++ [slot] := by
    rw [rightOccurrence]
    exact exists_eq_append_singleton_of_eq_dropLast parentShape.1 parentShape.2
  have historyShape : ∃ tail,
      topology.initial.rightCursor.occurrence.1.node.history =
        topology.initial.right :: topology.initial.left :: tail := by
    have headObserved :
        topology.initial.rightCursor.occurrence.1.node.history.head? =
          some topology.initial.right := startHead.trans startCurrent
    obtain ⟨rest, historyRest⟩ := List.head?_eq_some_iff.mp headObserved
    cases rest with
    | nil =>
        simp [OfficialCIPNode.parent?, historyRest] at startParent
    | cons second tail =>
        have parentComputed :
            topology.initial.rightCursor.occurrence.1.node.parent? = some second := by
          unfold OfficialCIPNode.parent?
          rw [historyRest]
        have secondEq : second = topology.initial.left := by
          rw [parentComputed] at startParent
          exact Option.some.inj startParent
        subst second
        exact ⟨tail, historyRest⟩
  obtain ⟨_historyTail, historyRest⟩ := historyShape
  have leftMem : topology.initial.left ∈
      topology.initial.rightCursor.occurrence.1.node.history := by
    rw [historyRest]
    simp
  have rightMem : topology.initial.right ∈
      topology.initial.rightCursor.occurrence.1.node.history := by
    rw [historyRest]
    simp
  have countLt' : 1 < topology.rightward.length := by
    simpa [LocalizedRule3OddCumuleneEndpointCursorFrame.doubleBondCount] using countLt
  have countOdd' : Odd topology.rightward.length := by
    simpa [LocalizedRule3OddCumuleneEndpointCursorFrame.doubleBondCount] using countOdd
  rcases odd_bond_two_characterization topology.initial.left topology.initial.right bondLR with
    ⟨hL0, hR1⟩ | ⟨hL1, hR0⟩ | ⟨hL1, hR2⟩ | ⟨hL2, hR1⟩ | ⟨hL2, hR3⟩ | ⟨hL3, hR2⟩ |
    ⟨hL4, hR5⟩ | ⟨hL5, hR4⟩ | ⟨hL5, hR6⟩ | ⟨hL6, hR5⟩ | ⟨hL6, hR7⟩ | ⟨hL7, hR6⟩
  · -- 0 → 3
    have hleft : topology.initial.left = o0 := Fin.ext hL0
    have hright : topology.initial.right = o1 := Fin.ext hR1
    rw [hleft] at leftMem
    rw [hright] at startCurrent rightMem
    obtain ⟨middle, far, walkShape, middleCurrent, farCurrent, middlePrev, farPrev⟩ :=
      declarativeWalk_forced_three oddInput walkDecl countLt' countOdd'
        topology.initial.leftCursor.occurrence rightPrevious outwardStart
        o0 o1 o2 o3 startCurrent leftMem rightMem
        odd_bond_two_one odd_bond_two_two odd_bond_two_three
    obtain ⟨rest, reverseEq⟩ := reverseIdentity
    have walkReverse : topology.rightward.reverse =
        [far, middle, topology.initial.rightCursor] := by
      rw [walkShape]
      simp
    rw [walkReverse] at reverseEq
    injection reverseEq with farEq middleEq
    injection middleEq with middleEq' _restEq
    have farIsRight : topology.right = o3 := by
      have observed := rightEq
      rw [← farEq] at observed
      rw [farCurrent] at observed
      exact (Option.some.inj observed).symm
    have partnerIsTwo : topology.rightPartner = o2 := by
      have observed := rightPartnerEq
      rw [← middleEq'] at observed
      rw [middleCurrent] at observed
      exact (Option.some.inj observed).symm
    have leftListEq : [leftFirst, leftSecond] = [o8, o9] := by
      rw [← leftCandidates, hleft, hright]
      exact odd_substituents_zero_one
    have rightListEq : [rightFirst, rightSecond] = [o4, o12] := by
      rw [← rightCandidates, farIsRight, partnerIsTwo]
      exact odd_substituents_three_two
    simp only [List.cons.injEq, List.nil_eq, and_true] at leftListEq rightListEq
    obtain ⟨leftFirstEq, leftSecondEq⟩ := leftListEq
    obtain ⟨rightFirstEq, rightSecondEq⟩ := rightListEq
    rw [hleft, farIsRight, leftFirstEq, leftSecondEq, rightFirstEq, rightSecondEq]
    exact odd_ready_zero_three
  · -- 1 → 0 : the start atom has a single order-two neighbour, already in the history
    have hleft : topology.initial.left = o1 := Fin.ext hL1
    have hright : topology.initial.right = o0 := Fin.ext hR0
    rw [hleft] at leftMem
    rw [hright] at startCurrent
    exfalso
    exact declarativeWalk_impossible_of_start_leaf oddInput walkDecl countLt'
      topology.initial.leftCursor.occurrence rightPrevious outwardStart
      o1 o0 startCurrent leftMem odd_bond_two_zero
  · -- 1 → 2 : the only continuation from 2 is back to the parent 1
    have hleft : topology.initial.left = o1 := Fin.ext hL1
    have hright : topology.initial.right = o2 := Fin.ext hR2
    rw [hleft] at leftMem
    rw [hright] at startCurrent rightMem
    exfalso
    exact declarativeWalk_two_step_impossible oddInput walkDecl countLt' countOdd'
      topology.initial.leftCursor.occurrence rightPrevious outwardStart
      o1 o2 o3 startCurrent leftMem rightMem odd_bond_two_two odd_bond_two_three
  · -- 2 → 1
    have hleft : topology.initial.left = o2 := Fin.ext hL2
    have hright : topology.initial.right = o1 := Fin.ext hR1
    rw [hleft] at leftMem
    rw [hright] at startCurrent rightMem
    exfalso
    exact declarativeWalk_two_step_impossible oddInput walkDecl countLt' countOdd'
      topology.initial.leftCursor.occurrence rightPrevious outwardStart
      o2 o1 o0 startCurrent leftMem rightMem
      (fun x hx => Or.symm (odd_bond_two_one x hx)) odd_bond_two_zero
  · -- 2 → 3 : the start atom has a single order-two neighbour, already in the history
    have hleft : topology.initial.left = o2 := Fin.ext hL2
    have hright : topology.initial.right = o3 := Fin.ext hR3
    rw [hleft] at leftMem
    rw [hright] at startCurrent
    exfalso
    exact declarativeWalk_impossible_of_start_leaf oddInput walkDecl countLt'
      topology.initial.leftCursor.occurrence rightPrevious outwardStart
      o2 o3 startCurrent leftMem odd_bond_two_three
  · -- 3 → 0
    have hleft : topology.initial.left = o3 := Fin.ext hL3
    have hright : topology.initial.right = o2 := Fin.ext hR2
    rw [hleft] at leftMem
    rw [hright] at startCurrent rightMem
    obtain ⟨middle, far, walkShape, middleCurrent, farCurrent, middlePrev, farPrev⟩ :=
      declarativeWalk_forced_three oddInput walkDecl countLt' countOdd'
        topology.initial.leftCursor.occurrence rightPrevious outwardStart
        o3 o2 o1 o0 startCurrent leftMem rightMem
        (fun x hx => Or.symm (odd_bond_two_two x hx))
        (fun x hx => Or.symm (odd_bond_two_one x hx)) odd_bond_two_zero
    obtain ⟨rest, reverseEq⟩ := reverseIdentity
    have walkReverse : topology.rightward.reverse =
        [far, middle, topology.initial.rightCursor] := by
      rw [walkShape]
      simp
    rw [walkReverse] at reverseEq
    injection reverseEq with farEq middleEq
    injection middleEq with middleEq' _restEq
    have farIsRight : topology.right = o0 := by
      have observed := rightEq
      rw [← farEq] at observed
      rw [farCurrent] at observed
      exact (Option.some.inj observed).symm
    have partnerIsOne : topology.rightPartner = o1 := by
      have observed := rightPartnerEq
      rw [← middleEq'] at observed
      rw [middleCurrent] at observed
      exact (Option.some.inj observed).symm
    have leftListEq : [leftFirst, leftSecond] = [o4, o12] := by
      rw [← leftCandidates, hleft, hright]
      exact odd_substituents_three_two
    have rightListEq : [rightFirst, rightSecond] = [o8, o9] := by
      rw [← rightCandidates, farIsRight, partnerIsOne]
      exact odd_substituents_zero_one
    simp only [List.cons.injEq, List.nil_eq, and_true] at leftListEq rightListEq
    obtain ⟨leftFirstEq, leftSecondEq⟩ := leftListEq
    obtain ⟨rightFirstEq, rightSecondEq⟩ := rightListEq
    rw [hleft, farIsRight, leftFirstEq, leftSecondEq, rightFirstEq, rightSecondEq]
    exact odd_ready_three_zero
  · -- 4 → 5
    have hleft : topology.initial.left = o4 := Fin.ext hL4
    have hright : topology.initial.right = o5 := Fin.ext hR5
    rw [hleft] at leftMem
    rw [hright] at startCurrent rightMem
    obtain ⟨middle, far, walkShape, middleCurrent, farCurrent, middlePrev, farPrev⟩ :=
      declarativeWalk_forced_three oddInput walkDecl countLt' countOdd'
        topology.initial.leftCursor.occurrence rightPrevious outwardStart
        o4 o5 o6 o7 startCurrent leftMem rightMem
        odd_bond_two_five odd_bond_two_six odd_bond_two_seven
    obtain ⟨rest, reverseEq⟩ := reverseIdentity
    have walkReverse : topology.rightward.reverse =
        [far, middle, topology.initial.rightCursor] := by
      rw [walkShape]
      simp
    rw [walkReverse] at reverseEq
    injection reverseEq with farEq middleEq
    injection middleEq with middleEq' _restEq
    have farIsRight : topology.right = o7 := by
      have observed := rightEq
      rw [← farEq] at observed
      rw [farCurrent] at observed
      exact (Option.some.inj observed).symm
    have partnerIsSix : topology.rightPartner = o6 := by
      have observed := rightPartnerEq
      rw [← middleEq'] at observed
      rw [middleCurrent] at observed
      exact (Option.some.inj observed).symm
    have leftListEq : [leftFirst, leftSecond] = [o3, o13] := by
      rw [← leftCandidates, hleft, hright]
      exact odd_substituents_four_five
    have rightListEq : [rightFirst, rightSecond] = [o10, o11] := by
      rw [← rightCandidates, farIsRight, partnerIsSix]
      exact odd_substituents_seven_six
    simp only [List.cons.injEq, List.nil_eq, and_true] at leftListEq rightListEq
    obtain ⟨leftFirstEq, leftSecondEq⟩ := leftListEq
    obtain ⟨rightFirstEq, rightSecondEq⟩ := rightListEq
    rw [hleft, farIsRight, leftFirstEq, leftSecondEq, rightFirstEq, rightSecondEq]
    exact odd_ready_four_seven
  · -- 5 → 4 : the start atom has a single order-two neighbour, already in the history
    have hleft : topology.initial.left = o5 := Fin.ext hL5
    have hright : topology.initial.right = o4 := Fin.ext hR4
    rw [hleft] at leftMem
    rw [hright] at startCurrent
    exfalso
    exact declarativeWalk_impossible_of_start_leaf oddInput walkDecl countLt'
      topology.initial.leftCursor.occurrence rightPrevious outwardStart
      o5 o4 startCurrent leftMem odd_bond_two_four
  · -- 5 → 6
    have hleft : topology.initial.left = o5 := Fin.ext hL5
    have hright : topology.initial.right = o6 := Fin.ext hR6
    rw [hleft] at leftMem
    rw [hright] at startCurrent rightMem
    exfalso
    exact declarativeWalk_two_step_impossible oddInput walkDecl countLt' countOdd'
      topology.initial.leftCursor.occurrence rightPrevious outwardStart
      o5 o6 o7 startCurrent leftMem rightMem odd_bond_two_six odd_bond_two_seven
  · -- 6 → 5
    have hleft : topology.initial.left = o6 := Fin.ext hL6
    have hright : topology.initial.right = o5 := Fin.ext hR5
    rw [hleft] at leftMem
    rw [hright] at startCurrent rightMem
    exfalso
    exact declarativeWalk_two_step_impossible oddInput walkDecl countLt' countOdd'
      topology.initial.leftCursor.occurrence rightPrevious outwardStart
      o6 o5 o4 startCurrent leftMem rightMem
      (fun x hx => Or.symm (odd_bond_two_five x hx)) odd_bond_two_four
  · -- 6 → 7 : the start atom has a single order-two neighbour, already in the history
    have hleft : topology.initial.left = o6 := Fin.ext hL6
    have hright : topology.initial.right = o7 := Fin.ext hR7
    rw [hleft] at leftMem
    rw [hright] at startCurrent
    exfalso
    exact declarativeWalk_impossible_of_start_leaf oddInput walkDecl countLt'
      topology.initial.leftCursor.occurrence rightPrevious outwardStart
      o6 o7 startCurrent leftMem odd_bond_two_seven
  · -- 7 → 4
    have hleft : topology.initial.left = o7 := Fin.ext hL7
    have hright : topology.initial.right = o6 := Fin.ext hR6
    rw [hleft] at leftMem
    rw [hright] at startCurrent rightMem
    obtain ⟨middle, far, walkShape, middleCurrent, farCurrent, middlePrev, farPrev⟩ :=
      declarativeWalk_forced_three oddInput walkDecl countLt' countOdd'
        topology.initial.leftCursor.occurrence rightPrevious outwardStart
        o7 o6 o5 o4 startCurrent leftMem rightMem
        (fun x hx => Or.symm (odd_bond_two_six x hx))
        (fun x hx => Or.symm (odd_bond_two_five x hx)) odd_bond_two_four
    obtain ⟨rest, reverseEq⟩ := reverseIdentity
    have walkReverse : topology.rightward.reverse =
        [far, middle, topology.initial.rightCursor] := by
      rw [walkShape]
      simp
    rw [walkReverse] at reverseEq
    injection reverseEq with farEq middleEq
    injection middleEq with middleEq' _restEq
    have farIsRight : topology.right = o4 := by
      have observed := rightEq
      rw [← farEq] at observed
      rw [farCurrent] at observed
      exact (Option.some.inj observed).symm
    have partnerIsFive : topology.rightPartner = o5 := by
      have observed := rightPartnerEq
      rw [← middleEq'] at observed
      rw [middleCurrent] at observed
      exact (Option.some.inj observed).symm
    have leftListEq : [leftFirst, leftSecond] = [o10, o11] := by
      rw [← leftCandidates, hleft, hright]
      exact odd_substituents_seven_six
    have rightListEq : [rightFirst, rightSecond] = [o3, o13] := by
      rw [← rightCandidates, farIsRight, partnerIsFive]
      exact odd_substituents_four_five
    simp only [List.cons.injEq, List.nil_eq, and_true] at leftListEq rightListEq
    obtain ⟨leftFirstEq, leftSecondEq⟩ := leftListEq
    obtain ⟨rightFirstEq, rightSecondEq⟩ := rightListEq
    rw [hleft, farIsRight, leftFirstEq, leftSecondEq, rightFirstEq, rightSecondEq]
    exact odd_ready_seven_four

/-- The difluoroethene domain at every carrier fuel, combining the actual ordinary-axis
exhaustion with the structural odd-branch vacuity. -/
theorem difluoro_domain_all :
    difluoroInput.LocalizedRule3AxisCoordinateGeometryDomainAll := by
  intro carrierFuel
  refine ⟨difluoro_ordinary_domain carrierFuel, ?_⟩
  intro occurrence topology leftFirst leftSecond rightFirst rightSecond declarative
    _leftCandidates _rightCandidates
  exact (difluoro_no_odd_frame carrierFuel occurrence topology declarative).elim

/-- The difluoroethene domain at the fixed depth `atomCount + 1`, as a consequence of the all-fuel
statement. -/
theorem difluoro_domain_fixed :
    difluoroInput.LocalizedRule3AxisCoordinateGeometryDomain 7 :=
  difluoro_domain_all 7



theorem difluoro_conditional_geometry_domain_all (carrierFuel : Nat) :
    difluoroInput.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll carrierFuel :=
  difluoroInput.localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_axisCoordinateGeometryAll
    difluoro_domain_all carrierFuel

theorem odd_conditional_geometry_domain_fixed :
    oddInput.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll oddCarrierFuel :=
  oddInput.localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_axisCoordinateGeometry
    oddCarrierFuel odd_domain_fixed

end SourceAxisGeometryWitnesses

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoroSource
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoroCertified
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoroInput
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.oddSource
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.oddCertified
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.oddInput
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_atomCount
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_atomCount
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.f0
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.f1
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.f2
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.f3
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.f4
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.f5
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.o0
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.o1
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.o2
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.o3
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.o4
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.o5
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.o6
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.o7
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.o8
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.o9
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.o10
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.o11
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.o12
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.o13
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.q0
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.q1
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.q2
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.q3
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.q4
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.q5
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.q6
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.q7
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.q8
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.q9
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.q10
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.q11
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.q12
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.q13
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_point_zero
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_point_one
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_point_two
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_point_three
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_point_four
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_point_five
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_point_zero
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_point_one
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_point_two
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_point_three
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_point_four
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_point_five
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_point_six
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_point_seven
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_point_eight
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_point_nine
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_point_ten
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_point_eleven
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_point_twelve
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_point_thirteen
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_adj_iff
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_adj_iff
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_neighbor_finset_zero
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_neighbor_finset_one
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_neighbor_finset_zero
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_neighbor_finset_one
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_neighbor_finset_two
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_neighbor_finset_three
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_neighbor_finset_four
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_neighbor_finset_five
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_neighbor_finset_six
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_neighbor_finset_seven
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_substituents_zero_one
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_substituents_one_zero
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_substituents_zero_one
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_substituents_one_zero
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_substituents_one_two
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_substituents_two_one
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_substituents_two_three
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_substituents_three_two
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_substituents_four_five
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_substituents_five_four
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_substituents_five_six
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_substituents_six_five
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_substituents_six_seven
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_substituents_seven_six
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_bond_two_characterization
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_bond_two_characterization
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_no_ordinary_double_candidate_axis
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.oddDeclarativeFrame_rightCursor_valid
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.oddEndpointWalk_length_le_traversalFuel
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.localizedRule3OddCumuleneEndpointCursorFrame?_eq_some_of_declarative
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_some_of_declarative
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_some_at_traversalFuel_of_declarative
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.linearStep_fresh
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.declarativeCumulatedAxisWalk_terminal_or_step
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_forward_ready
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_reverse_reference
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_reverse_leftArm
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_reverse_rightArm
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_reverse_ready
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_ordinary_domain
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_no_odd_frame
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_ordinary_domain
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_ready_zero_three
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_ready_three_zero
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_ready_four_seven
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_ready_seven_four
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.oddCarrierFuel
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.oddTraversalFuel
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_bond_two_zero
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_bond_two_one
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_bond_two_two
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_bond_two_three
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_bond_two_four
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_bond_two_five
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_bond_two_six
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_bond_two_seven
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.declarativeWalk_step_data
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.declarativeWalk_terminal_of_no_fresh_double
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.declarativeWalk_impossible_of_start_leaf
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.declarativeWalk_two_step_impossible
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.declarativeWalk_forced_three
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_domain_fixed
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_domain_all
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_domain_fixed
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.difluoro_conditional_geometry_domain_all
assert_kernel_only TetraStereo.OneCenter.SourceAxisGeometryWitnesses.odd_conditional_geometry_domain_fixed
