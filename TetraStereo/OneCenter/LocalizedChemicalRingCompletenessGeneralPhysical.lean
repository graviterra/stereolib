import TetraStereo.OneCenter.LocalizedChemicalRingActualCovariance
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Actual recursion covariance under arbitrary molecular automorphisms

The raw relabelling of any molecular automorphism is bijective. Consequently the actual
retained and sparse operations transport under rotations as well as involutions. This removes
the involution restriction from the physical orbit argument; it does not assert that a
physically distinguishable centre has distinct marked keys.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneralPhysical
open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingActualCovariance
open LocalizedMarkedDetectedFrames (written_perm_incident)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)

variable (input : CertifiedLocalizedCIPInput)

theorem relabelOf_inverse (e : Equiv.Perm input.Atom) (x : Nat) :
    relabelOf input e.symm (relabelOf input e x) = x := by
  by_cases bound : x < input.certified.input.molecule.atomCount
  · change relabelOf input e.symm (relabelOf input e (⟨x, bound⟩ : input.Atom).val) = x
    rw [relabelOf_val, relabelOf_val, e.symm_apply_apply]
  · rw [relabelOf_outside input e x (Nat.not_lt.mp bound),
      relabelOf_outside input e.symm x (Nat.not_lt.mp bound)]

theorem relabelOf_bijective (e : Equiv.Perm input.Atom) :
    Function.Bijective (relabelOf input e) := by
  constructor
  · exact Function.LeftInverse.injective (relabelOf_inverse input e)
  · intro x
    exact ⟨relabelOf input e.symm x, relabelOf_inverse input e.symm x⟩

variable (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (e : input.detectedMultiCenterMolecule.Aut)

include agreement admissible supported in
theorem neighbors_relabel (x : Nat) :
    (mol.canonicalIncidentNeighbors (relabelOf input (e : Equiv.Perm input.Atom) x)).Perm
      ((mol.canonicalIncidentNeighbors x).map (relabelOf input (e : Equiv.Perm input.Atom))) := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have bij := relabelOf_bijective input (e : Equiv.Perm input.Atom)
  rw [List.perm_ext_iff_of_nodup (mol.canonicalIncidentNeighbors_nodup _ unique)
    ((mol.canonicalIncidentNeighbors_nodup _ unique).map bij.1)]
  intro y
  rw [mol.mem_canonicalIncidentNeighbors_iff _ wellFormed, List.mem_map]
  constructor
  · intro positive
    obtain ⟨z, rfl⟩ := bij.2 y
    refine ⟨z, ?_, rfl⟩
    rw [mol.mem_canonicalIncidentNeighbors_iff _ wellFormed]
    rwa [bondOrder_relabel mol input agreement admissible supported e] at positive
  · rintro ⟨z, member, rfl⟩
    rw [mol.mem_canonicalIncidentNeighbors_iff _ wellFormed] at member
    rw [bondOrder_relabel mol input agreement admissible supported e]
    exact member

variable (atomsPres : ∀ x, x < mol.atomCount →
    mol.atomAt? (relabelOf input (e : Equiv.Perm input.Atom) x) = mol.atomAt? x)

include agreement admissible supported atomsPres in
/-- No order-two assumption is imposed on the molecular automorphism. -/
theorem structuralSymmetry_of_aut :
    StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom)) where
  bijective := relabelOf_bijective input _
  inRange := fun x hx => relabelOf_lt mol input agreement _ x hx
  outside := fun x hx => relabelOf_outside input _ x (by rw [count mol input agreement]; exact hx)
  bonds := bondOrder_relabel mol input agreement admissible supported e
  ligands := by
    intro x hx
    have w := written_perm_incident mol admissible.1.1 admissible.1.2 admissible.2 ⟨x, hx⟩
    have w' := written_perm_incident mol admissible.1.1 admissible.1.2 admissible.2
      ⟨_, relabelOf_lt mol input agreement (e : Equiv.Perm input.Atom) x hx⟩
    have nb := neighbors_relabel input mol agreement admissible supported e x
    have lengthEq : (mol.writtenNeighbors (relabelOf input (e : Equiv.Perm input.Atom) x)).length =
        (mol.writtenNeighbors x).length := by
      rw [w'.length_eq, nb.length_eq, List.length_map, w.length_eq]
    have active : lonePairActive mol (relabelOf input (e : Equiv.Perm input.Atom) x) =
        lonePairActive mol x := by
      unfold lonePairActive
      rw [atomsPres x hx, lengthEq]
    have phantom : relabelOf input (e : Equiv.Perm input.Atom) mol.atomCount = mol.atomCount :=
      relabelOf_outside input _ _ (by rw [count mol input agreement])
    refine (ligands_perm_shape mol _).trans ?_
    refine List.Perm.trans ?_ ((ligands_perm_shape mol x).map _).symm
    rw [List.map_append, active]
    refine List.Perm.append (List.Perm.of_eq ?_) (w'.trans (nb.trans (w.map _).symm))
    cases lonePairActive mol x <;> simp [phantom]

include agreement admissible supported single atomsPres in
/-- The actual callbacks satisfy covariance for every molecular automorphism, including rotations. -/
theorem actual_covariant :
    Covariant mol (sparseOperations input mol) (relabelOf input (e : Equiv.Perm input.Atom)) :=
  sparseOperations_covariant input mol agreement admissible supported single
    ⟨(e : Equiv.Perm input.Atom),
      MultiCenterMolecule.Aut.mem_molAut (m := input.detectedMultiCenterMolecule) e⟩
    (structuralSymmetry_of_aut input mol agreement admissible supported e atomsPres)

end TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneralPhysical

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneralPhysical.relabelOf_inverse
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneralPhysical.relabelOf_bijective
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneralPhysical.structuralSymmetry_of_aut
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneralPhysical.actual_covariant
