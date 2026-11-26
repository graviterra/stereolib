import TetraStereo.Engine.RingOxaziridineNitrogen
import TetraStereo.Engine.RingBridgeheadNitrogenTransport

set_option autoImplicit false
namespace TetraStereo.Engine.RingOxaziridineNitrogen
open OneCenter
open LocalizedChemicalRing (Input)
open RingRawRenumbering (AtomMap)
open RingBridgeheadNitrogen (rawAtomEquiv rawAtoms)
variable {i j : Input}

theorem atomIs_atomMap (r : AtomMap i j) (a : i.certified.Atom) (z : Element) :
    atomIs j.molecule (r.atoms a).val z = atomIs i.molecule a.val z := by
  let selected (record : RingRawRenumbering.MolecularRecord) :=
    record.element == z && record.charge == 0 && !record.aromatic
  have projected (v : Option AtomSpec) :
      v.any (fun atom => atom.element == z && atom.charge == 0 && !atom.aromatic) =
        (v.map RingRawRenumbering.molecularRecord).any selected := by cases v <;> rfl
  simp only [atomIs,projected,r.records]

theorem constrained_eq_test (i : Input) (a : i.certified.Atom) :
    constrained i a = test (fun (u : i.certified.Atom) z => atomIs i.molecule u.val z)
      (fun u v => i.molecule.bondOrder u.val v.val) a := by
  have bound : a.val < i.molecule.atomCount := by
    rw [← i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1]
    exact a.isLt
  unfold constrained constrainedRaw
  rw [dif_pos bound]
  exact test_equiv (rawAtomEquiv i) _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) a

theorem constrained_atomMap (r : AtomMap i j) (a : i.certified.Atom) :
    constrained j (r.atoms a) = constrained i a := by
  rw [constrained_eq_test,constrained_eq_test]
  exact test_equiv r.atoms _ _ _ _ (atomIs_atomMap r) r.bonds a
end TetraStereo.Engine.RingOxaziridineNitrogen

namespace TetraStereo.Engine.RingPyramidalNitrogen
open LocalizedChemicalRing (Input)
open RingRawRenumbering (AtomMap)
theorem constrained_atomMap {i j : Input} (r : AtomMap i j) (a : i.certified.Atom) :
    constrained j (r.atoms a) = constrained i a := by
  change (RingOxaziridineNitrogen.constrained j (r.atoms a) ||
      RingBridgeheadNitrogen.constrained j (r.atoms a)) =
    (RingOxaziridineNitrogen.constrained i a || RingBridgeheadNitrogen.constrained i a)
  rw [RingOxaziridineNitrogen.constrained_atomMap r a,RingBridgeheadNitrogen.constrained_atomMap r a]
end TetraStereo.Engine.RingPyramidalNitrogen
assert_kernel_only TetraStereo.Engine.RingOxaziridineNitrogen.constrained_atomMap
assert_kernel_only TetraStereo.Engine.RingPyramidalNitrogen.constrained_atomMap
