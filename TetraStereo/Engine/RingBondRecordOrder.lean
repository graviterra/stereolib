import TetraStereo.Engine.RingRawRenumbering
import TetraStereo.Engine.RingGraphReport

/-! Reordering the bond records of two admitted inputs preserves their literal report
for the same numbered atoms. No isomorphism search or equality of local decisions is assumed. -/

set_option autoImplicit false

namespace TetraStereo.Engine.RingBondRecordOrder

open OneCenter
open LocalizedChemicalRing (Input)
open RingRawRenumbering (Renumbering)

/-- A bond-table permutation preserves the symmetric order of every atom pair,
even before admission. The directed fold takes a maximum of matching entries. -/
theorem bondOrder {m n : RawMolecule} (perm : m.bonds.Perm n.bonds) (a b : Nat) :
    m.bondOrder a b = n.bondOrder a b := by
  have directed (u v : Nat) : m.directedBondOrder u v = n.directedBondOrder u v := by
    unfold RawMolecule.directedBondOrder
    apply perm.foldl_eq'
    intro x hx y hy z
    by_cases first : x.directedConnects u v <;> by_cases second : y.directedConnects u v <;>
      simp [first, second, max_assoc, max_left_comm, max_comm]
  simp [RawMolecule.bondOrder, directed]

structure Presentation (i j : Input) : Prop where
  atoms : i.molecule.atoms = j.molecule.atoms
  bonds : i.molecule.bonds.Perm j.molecule.bonds
  positions : i.spatial.positions = j.spatial.positions

variable {i j : Input}

theorem atomCount (p : Presentation i j) :
    i.certified.certified.input.molecule.atomCount = j.certified.certified.input.molecule.atomCount := by
  rw [i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1,
      j.molecule.toSemanticMolecule?_atomCount _ j.agreement.1]
  exact congrArg List.length p.atoms

def identityRenumbering (p : Presentation i j) : Renumbering i j where
  atoms := finCongr (atomCount p)
  records a := by change j.molecule.atoms[a.val]? = i.molecule.atoms[a.val]?; rw [p.atoms]
  bonds a b := (bondOrder p.bonds a.val b.val).symm
  positions a := by change j.spatial.positions[a.val]? = i.spatial.positions[a.val]?; rw [p.positions]

/-- Literal equality of the public grouped reports, including row order, refusals,
and both geometry readings. Every selected atom retains its numerical identifier. -/
theorem grouped (p : Presentation i j) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) :
    RingGroupedReport.forAtoms? j (atoms.map (Fin.cast (atomCount p))) =
      RingGroupedReport.forAtoms? i atoms := by
  let r := identityRenumbering p
  have same : RingRawRenumbering.renameRow r = id := by
    funext row
    rcases row with ⟨a, v⟩
    simp [RingRawRenumbering.renameRow, r, identityRenumbering]
  have h := RingRawRenumbering.report r coords atoms
  rw [same] at h
  simpa using h

/-- The complete public inventory also agrees in its original order. Both
inventories are sorted by atom number and this presentation fixes every number. -/
theorem full (p : Presentation i j) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    RingGroupedReport.report? j = RingGroupedReport.report? i := by
  have sorted (k : Input) : (RingGroupedReport.centres k).Pairwise (· ≤ ·) := by
    have listed : RingGroupedReport.centres k = k.certified.tetrahedralCenterSet.sort (· ≤ ·) := by
      simp [RingGroupedReport.centres, CertifiedLocalizedCIPInput.canonicalTetrahedralCenters,
        List.map_map, Function.comp_def]
    rw [listed]
    exact Finset.pairwise_sort ..
  have ordered : ((RingGroupedReport.centres i).map (Fin.cast (atomCount p))).Pairwise (· ≤ ·) :=
    List.pairwise_map.mpr (sorted i)
  have inventory := List.Perm.eq_of_pairwise' ordered (sorted j)
    (RingRawRenumbering.centres_perm (identityRenumbering p))
  unfold RingGroupedReport.report?
  rw [← inventory]
  exact grouped p coords _

/-- The graph evaluator that enumerates bonded paths inherits the same representation
invariance. Coordinate admission on the second presentation follows by transport. -/
theorem cached (p : Presentation i j) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) :
    RingGraphReport.cachedReport j (atoms.map (Fin.cast (atomCount p))) =
      RingGraphReport.cachedReport i atoms := by
  have coords' := RingRawRenumbering.coordinates (identityRenumbering p) coords
  rw [RingGraphReport.cached_exact j coords', RingGraphReport.report_exact j coords',
      RingGraphReport.cached_exact i coords, RingGraphReport.report_exact i coords]
  exact grouped p coords atoms

end TetraStereo.Engine.RingBondRecordOrder

assert_kernel_only TetraStereo.Engine.RingBondRecordOrder.bondOrder
assert_kernel_only TetraStereo.Engine.RingBondRecordOrder.grouped
assert_kernel_only TetraStereo.Engine.RingBondRecordOrder.full
assert_kernel_only TetraStereo.Engine.RingBondRecordOrder.cached
