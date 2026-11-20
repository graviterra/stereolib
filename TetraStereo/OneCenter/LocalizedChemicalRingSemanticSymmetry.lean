import TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneralPhysical
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Actual relabel covariance from the molecular constitution

The callbacks need the physical neighbor multiset and its possible lone-pair phantom.
The phantom test uses only the element and the number of written neighbors. Those data
follow from intake agreement and a molecular graph automorphism, without equality of
the complete parser atom records (which also contain hydrogen and depiction metadata).
No reader, comparison, label, descriptor, or coordinate agreement is assumed here.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingSemanticSymmetry

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingActualCovariance
open LocalizedMarkedDetectedFrames (written_perm_incident)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedChemicalRingCompletenessGeneralPhysical (relabelOf_bijective neighbors_relabel)

private theorem element_atomicNumber_injective : Function.Injective Element.atomicNumber := by
  intro a b same
  cases a <;> cases b <;> simp_all [Element.atomicNumber]

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (e : input.detectedMultiCenterMolecule.Aut)

include agreement in
/-- The actual raw elements agree under the graph automorphism. Other parser metadata
need not agree and is not reconstructed from the semantic molecular graph. -/
theorem elements_relabel (x : Nat) (bound : x < mol.atomCount) :
    (mol.atomAt? (relabelOf input (e : Equiv.Perm input.Atom) x)).map AtomSpec.element =
      (mol.atomAt? x).map AtomSpec.element := by
  let i : Fin mol.atomCount := ⟨x, bound⟩
  let j : Fin mol.atomCount :=
    ⟨relabelOf input (e : Equiv.Perm input.Atom) x,
      relabelOf_lt mol input agreement (e : Equiv.Perm input.Atom) x bound⟩
  have lookup (k : Fin mol.atomCount) : mol.atomAt? k.val = some (mol.atoms.get k) := by
    exact listGet?_eq_some_get mol.atoms k
  have zi := (intakeAtomDataCorresponds mol input agreement i).1
  have zj := (intakeAtomDataCorresponds mol input agreement j).1
  have image : localizedIndexOf mol input agreement j =
      (e : Equiv.Perm input.Atom) (localizedIndexOf mol input agreement i) := by
    apply Fin.ext
    exact relabelOf_val input (e : Equiv.Perm input.Atom) (localizedIndexOf mol input agreement i)
  let graphAut : input.moleculeGraph.Aut :=
    ⟨(e : Equiv.Perm input.Atom),
      MultiCenterMolecule.Aut.mem_molAut (m := input.detectedMultiCenterMolecule) e⟩
  have preserved := MoleculeGraph.Aut.atomZ_eq (m := input.moleculeGraph) graphAut
    (localizedIndexOf mol input agreement i)
  have number : (mol.atoms.get j).element.atomicNumber =
      (mol.atoms.get i).element.atomicNumber :=
    zj.symm.trans ((congrArg input.moleculeGraph.atomZ image).trans (preserved.trans zi))
  have element := element_atomicNumber_injective number
  change (mol.atomAt? j.val).map AtomSpec.element = (mol.atomAt? i.val).map AtomSpec.element
  rw [lookup j, lookup i, Option.map_some, Option.map_some, element]

include agreement admissible supported in
/-- The written physical neighbor lists agree up to the actual atom relabelling. -/
theorem written_neighbors_relabel (x : Nat) (bound : x < mol.atomCount) :
    (mol.writtenNeighbors (relabelOf input (e : Equiv.Perm input.Atom) x)).Perm
      ((mol.writtenNeighbors x).map (relabelOf input (e : Equiv.Perm input.Atom))) := by
  have before := written_perm_incident mol admissible.1.1 admissible.1.2 admissible.2 ⟨x, bound⟩
  have after := written_perm_incident mol admissible.1.1 admissible.1.2 admissible.2
    ⟨_, relabelOf_lt mol input agreement (e : Equiv.Perm input.Atom) x bound⟩
  exact after.trans ((neighbors_relabel input mol agreement admissible supported e x).trans
    (before.map _).symm)

private theorem active_from_element (x : Nat) :
    lonePairActive mol x =
      ((((mol.atomAt? x).map AtomSpec.element).map RawMolecule.centreElementUsesLonePair).getD false &&
        ((mol.writtenNeighbors x).length == 3)) := by
  unfold lonePairActive
  cases mol.atomAt? x <;> rfl

include agreement admissible supported in
/-- Lone-pair activation follows from the source element and degree, not from equality
of isotope, hydrogen-policy, or tetrahedral-depiction fields of the raw atom records. -/
theorem lonePairActive_relabel (x : Nat) (bound : x < mol.atomCount) :
    lonePairActive mol (relabelOf input (e : Equiv.Perm input.Atom) x) = lonePairActive mol x := by
  have length := (written_neighbors_relabel input mol agreement admissible supported e x bound).length_eq
  rw [List.length_map] at length
  rw [active_from_element, active_from_element,
    elements_relabel input mol agreement e x bound, length]

include agreement admissible supported in
/-- Physical ligands, including an active phantom, transport without preserving the
parser's position convention for that phantom. Only the required permutation is concluded. -/
theorem ligands_relabel (x : Nat) (bound : x < mol.atomCount) :
    (mol.ligandsWithLonePair (relabelOf input (e : Equiv.Perm input.Atom) x)).Perm
      ((mol.ligandsWithLonePair x).map (relabelOf input (e : Equiv.Perm input.Atom))) := by
  have active := lonePairActive_relabel input mol agreement admissible supported e x bound
  have neighbors := written_neighbors_relabel input mol agreement admissible supported e x bound
  have phantom : relabelOf input (e : Equiv.Perm input.Atom) mol.atomCount = mol.atomCount :=
    relabelOf_outside input _ _ (by rw [count mol input agreement])
  refine (ligands_perm_shape mol _).trans ?_
  refine List.Perm.trans ?_ ((ligands_perm_shape mol x).map _).symm
  rw [List.map_append, active]
  refine List.Perm.append (List.Perm.of_eq ?_) neighbors
  cases lonePairActive mol x <;> simp [phantom]

include agreement admissible supported in
/-- The structural expansion symmetry is supplied by the actual molecular graph. -/
theorem structuralSymmetry_of_aut :
    StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom)) where
  bijective := relabelOf_bijective input _
  inRange := fun x bound => relabelOf_lt mol input agreement _ x bound
  outside := fun x bound => relabelOf_outside input _ x (by rw [count mol input agreement]; exact bound)
  bonds := bondOrder_relabel mol input agreement admissible supported e
  ligands := ligands_relabel input mol agreement admissible supported e

include agreement admissible supported single in
/-- Actual retained sparse callbacks are covariant under every molecular automorphism,
with no premise that complete raw atom records are preserved. -/
theorem actual_covariant :
    Covariant mol (sparseOperations input mol) (relabelOf input (e : Equiv.Perm input.Atom)) :=
  sparseOperations_covariant input mol agreement admissible supported single
    ⟨(e : Equiv.Perm input.Atom),
      MultiCenterMolecule.Aut.mem_molAut (m := input.detectedMultiCenterMolecule) e⟩
    (structuralSymmetry_of_aut input mol agreement admissible supported e)

end TetraStereo.OneCenter.LocalizedChemicalRingSemanticSymmetry

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSemanticSymmetry.elements_relabel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSemanticSymmetry.written_neighbors_relabel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSemanticSymmetry.lonePairActive_relabel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSemanticSymmetry.ligands_relabel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSemanticSymmetry.structuralSymmetry_of_aut
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSemanticSymmetry.actual_covariant
