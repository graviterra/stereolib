import TetraStereo.Engine.RingRawRenumbering
import TetraStereo.Engine.RingBridgeheadNitrogen

set_option autoImplicit false

namespace TetraStereo.Engine.RingBridgeheadNitrogen

open OneCenter
open LocalizedChemicalRing (Input)
open RingRawRenumbering (AtomMap)

variable {i j : Input}

/-- Admission identifies certified atom indices with the finite raw atom table. -/
def rawAtomEquiv (i : Input) : i.certified.Atom ≃ Fin i.molecule.atomCount :=
  finCongr (i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1)

@[simp] theorem rawAtomEquiv_val (i : Input) (a : i.certified.Atom) :
    (rawAtomEquiv i a).val = a.val := rfl

@[simp] theorem rawAtomEquiv_symm_val (i : Input) (a : Fin i.molecule.atomCount) :
    ((rawAtomEquiv i).symm a).val = a.val := rfl

/-- A molecular correspondence induces a bijection on raw finite atom indices. -/
def rawAtoms (r : AtomMap i j) : Fin i.molecule.atomCount ≃ Fin j.molecule.atomCount :=
  ((rawAtomEquiv i).symm.trans r.atoms).trans (rawAtomEquiv j)

@[simp] theorem rawAtoms_certified (r : AtomMap i j) (a : i.certified.Atom) :
    rawAtoms r (rawAtomEquiv i a) = rawAtomEquiv j (r.atoms a) := by
  simp [rawAtoms]

theorem rawAtoms_bonds (r : AtomMap i j) (a b : Fin i.molecule.atomCount) :
    j.molecule.bondOrder (rawAtoms r a).val (rawAtoms r b).val =
      i.molecule.bondOrder a.val b.val := by
  exact r.bonds ((rawAtomEquiv i).symm a) ((rawAtomEquiv i).symm b)

/-- The raw-index test agrees with the same finite graph on certified atoms. -/
theorem constrained_eq_test (i : Input) (a : i.certified.Atom) :
    constrained i a = test
      (fun (u v : i.certified.Atom) => decide (0 < i.molecule.bondOrder u.val v.val)) a := by
  have bound : a.val < i.molecule.atomCount := by
    rw [← i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1]
    exact a.isLt
  unfold constrained constrainedRaw
  rw [dif_pos bound]
  exact test_equiv (rawAtomEquiv i) _ _ (fun _ _ => rfl) a

/-- Short theta paths and the resulting nitrogen constraint are independent of
atom numbering. Only the molecular adjacency correspondence is used. -/
theorem constrained_atomMap (r : AtomMap i j) (a : i.certified.Atom) :
    constrained j (r.atoms a) = constrained i a := by
  rw [constrained_eq_test, constrained_eq_test]
  exact test_equiv r.atoms _ _ (fun u v => by rw [r.bonds]) a

end TetraStereo.Engine.RingBridgeheadNitrogen
assert_kernel_only TetraStereo.Engine.RingBridgeheadNitrogen.constrained_atomMap
