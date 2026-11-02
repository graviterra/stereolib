import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalAuthorityObservationFoundation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Physical certificates for the relational P-93 C70 superimposed observation. -/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

theorem iupacP93CanonicalFullereneC70SuperimposedCenter74PhysicalValid :
    (P93AuthorityPhysicalUnit.atomCenter 74).ValidFor
      iupacP93CanonicalFullereneRelationalAuthorityPhysicalPolicy
      iupacP93CanonicalFullereneC70SuperimposedAuthoritySource := by
  apply p93AuthorityAtomCenterValid_of_rawNeighbors
    iupacP93CanonicalFullereneC70SuperimposedMolecule
    iupacP93CanonicalFullereneC70SuperimposedRelationalInput.cage.carrier
    iupacP93CanonicalFullereneC70SuperimposedAuthoritySource
    iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.2
    74 [73, 75, 78]
  · decide
  · decide
  · decide
  · decide
  · intro neighbor neighborPresent
    simp only [List.mem_cons, List.not_mem_nil, or_false] at neighborPresent
    rcases neighborPresent with rfl | rfl | rfl
    · exact ⟨{ source := 73, target := 74, kind := .single }, by decide,
        Or.inr ⟨rfl, rfl⟩, by decide, by decide⟩
    · exact ⟨{ source := 74, target := 75, kind := .single }, by decide,
        Or.inl ⟨rfl, rfl⟩, by decide, by decide⟩
    · exact ⟨{ source := 74, target := 78, kind := .single }, by decide,
        Or.inl ⟨rfl, rfl⟩, by decide, by decide⟩

theorem iupacP93CanonicalFullereneC70SuperimposedCenter87PhysicalValid :
    (P93AuthorityPhysicalUnit.atomCenter 87).ValidFor
      iupacP93CanonicalFullereneRelationalAuthorityPhysicalPolicy
      iupacP93CanonicalFullereneC70SuperimposedAuthoritySource := by
  apply p93AuthorityAtomCenterValid_of_rawNeighbors
    iupacP93CanonicalFullereneC70SuperimposedMolecule
    iupacP93CanonicalFullereneC70SuperimposedRelationalInput.cage.carrier
    iupacP93CanonicalFullereneC70SuperimposedAuthoritySource
    iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.2
    87 [86, 88, 91]
  · decide
  · decide
  · decide
  · decide
  · intro neighbor neighborPresent
    simp only [List.mem_cons, List.not_mem_nil, or_false] at neighborPresent
    rcases neighborPresent with rfl | rfl | rfl
    · exact ⟨{ source := 86, target := 87, kind := .single }, by decide,
        Or.inr ⟨rfl, rfl⟩, by decide, by decide⟩
    · exact ⟨{ source := 87, target := 88, kind := .single }, by decide,
        Or.inl ⟨rfl, rfl⟩, by decide, by decide⟩
    · exact ⟨{ source := 87, target := 91, kind := .single }, by decide,
        Or.inl ⟨rfl, rfl⟩, by decide, by decide⟩

theorem iupacP93CanonicalFullereneC70SuperimposedSecondInternalBondOrder
    (left right : Fin
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.externalAtoms.length) :
    iupacP93CanonicalFullereneC70SuperimposedAssembly.compileExtension.assemble.bondOrder
        (97 + left) (97 + right) =
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.localMolecule.bondOrder
        left right := by
  simpa [molecularFullereneAddendExternalOffset,
    molecularFullereneAddendPrefixAtomCount,
    iupacP93CanonicalFullereneC70SuperimposedAssembly,
    compileIUPACP93PrintedFullereneAddendAssembly,
    iupacP93CanonicalFullereneC70SuperimposedPlacements] using
    iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddend_internalBondOrder
      iupacP93CanonicalFullereneC70Core_wellFormed 1
      iupacP93CanonicalFullereneC70SuperimposedSecondPlacement.toPlaced rfl left right

theorem iupacP93CanonicalFullereneC70SuperimposedSecondBondOrders :
    iupacP93CanonicalFullereneC70SuperimposedMolecule.bondOrder 100 101 = 1 ∧
    iupacP93CanonicalFullereneC70SuperimposedMolecule.bondOrder 101 102 = 1 ∧
    iupacP93CanonicalFullereneC70SuperimposedMolecule.bondOrder 101 105 = 1 ∧
    iupacP93CanonicalFullereneC70SuperimposedMolecule.bondOrder 113 114 = 1 ∧
    iupacP93CanonicalFullereneC70SuperimposedMolecule.bondOrder 114 115 = 1 ∧
    iupacP93CanonicalFullereneC70SuperimposedMolecule.bondOrder 114 118 = 1 := by
  exact ⟨
    by simpa [iupacP93CanonicalFullereneC70SuperimposedMolecule,
      MolecularFullereneLocalAddendTemplate.localMolecule,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylBonds,
      RawMolecule.bondOrder, RawMolecule.directedBondOrder, RawBond.directedConnects] using
        iupacP93CanonicalFullereneC70SuperimposedSecondInternalBondOrder
          ⟨3, by decide⟩ ⟨4, by decide⟩,
    by simpa [iupacP93CanonicalFullereneC70SuperimposedMolecule,
      MolecularFullereneLocalAddendTemplate.localMolecule,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylBonds,
      RawMolecule.bondOrder, RawMolecule.directedBondOrder, RawBond.directedConnects] using
        iupacP93CanonicalFullereneC70SuperimposedSecondInternalBondOrder
          ⟨4, by decide⟩ ⟨5, by decide⟩,
    by simpa [iupacP93CanonicalFullereneC70SuperimposedMolecule,
      MolecularFullereneLocalAddendTemplate.localMolecule,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylBonds,
      RawMolecule.bondOrder, RawMolecule.directedBondOrder, RawBond.directedConnects] using
        iupacP93CanonicalFullereneC70SuperimposedSecondInternalBondOrder
          ⟨4, by decide⟩ ⟨8, by decide⟩,
    by simpa [iupacP93CanonicalFullereneC70SuperimposedMolecule,
      MolecularFullereneLocalAddendTemplate.localMolecule,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylBonds,
      RawMolecule.bondOrder, RawMolecule.directedBondOrder, RawBond.directedConnects] using
        iupacP93CanonicalFullereneC70SuperimposedSecondInternalBondOrder
          ⟨16, by decide⟩ ⟨17, by decide⟩,
    by simpa [iupacP93CanonicalFullereneC70SuperimposedMolecule,
      MolecularFullereneLocalAddendTemplate.localMolecule,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylBonds,
      RawMolecule.bondOrder, RawMolecule.directedBondOrder, RawBond.directedConnects] using
        iupacP93CanonicalFullereneC70SuperimposedSecondInternalBondOrder
          ⟨17, by decide⟩ ⟨18, by decide⟩,
    by simpa [iupacP93CanonicalFullereneC70SuperimposedMolecule,
      MolecularFullereneLocalAddendTemplate.localMolecule,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylBonds,
      RawMolecule.bondOrder, RawMolecule.directedBondOrder, RawBond.directedConnects] using
        iupacP93CanonicalFullereneC70SuperimposedSecondInternalBondOrder
          ⟨17, by decide⟩ ⟨21, by decide⟩⟩

theorem iupacP93CanonicalFullereneC70SuperimposedCenter101PhysicalValid :
    (P93AuthorityPhysicalUnit.atomCenter 101).ValidFor
      iupacP93CanonicalFullereneRelationalAuthorityPhysicalPolicy
      iupacP93CanonicalFullereneC70SuperimposedAuthoritySource := by
  apply p93AuthorityAtomCenterValid_of_rawNeighbors
    iupacP93CanonicalFullereneC70SuperimposedMolecule
    iupacP93CanonicalFullereneC70SuperimposedRelationalInput.cage.carrier
    iupacP93CanonicalFullereneC70SuperimposedAuthoritySource
    iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.2
    101 [100, 102, 105]
  · decide
  · decide
  · decide
  · decide
  · intro neighbor neighborPresent
    simp only [List.mem_cons, List.not_mem_nil, or_false] at neighborPresent
    rcases neighborPresent with rfl | rfl | rfl
    · apply rawBond_exact_of_bondOrder_positive <;> try decide
      rw [iupacP93CanonicalFullereneC70SuperimposedMolecule.bondOrder_symm]
      simp [iupacP93CanonicalFullereneC70SuperimposedSecondBondOrders.1]
    · apply rawBond_exact_of_bondOrder_positive <;> try decide
      simp [iupacP93CanonicalFullereneC70SuperimposedSecondBondOrders.2.1]
    · apply rawBond_exact_of_bondOrder_positive <;> try decide
      simp [iupacP93CanonicalFullereneC70SuperimposedSecondBondOrders.2.2.1]

theorem iupacP93CanonicalFullereneC70SuperimposedCenter114PhysicalValid :
    (P93AuthorityPhysicalUnit.atomCenter 114).ValidFor
      iupacP93CanonicalFullereneRelationalAuthorityPhysicalPolicy
      iupacP93CanonicalFullereneC70SuperimposedAuthoritySource := by
  apply p93AuthorityAtomCenterValid_of_rawNeighbors
    iupacP93CanonicalFullereneC70SuperimposedMolecule
    iupacP93CanonicalFullereneC70SuperimposedRelationalInput.cage.carrier
    iupacP93CanonicalFullereneC70SuperimposedAuthoritySource
    iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.2
    114 [113, 115, 118]
  · decide
  · decide
  · decide
  · decide
  · intro neighbor neighborPresent
    simp only [List.mem_cons, List.not_mem_nil, or_false] at neighborPresent
    rcases neighborPresent with rfl | rfl | rfl
    · apply rawBond_exact_of_bondOrder_positive <;> try decide
      rw [iupacP93CanonicalFullereneC70SuperimposedMolecule.bondOrder_symm]
      simp [iupacP93CanonicalFullereneC70SuperimposedSecondBondOrders.2.2.2.1]
    · apply rawBond_exact_of_bondOrder_positive <;> try decide
      simp [iupacP93CanonicalFullereneC70SuperimposedSecondBondOrders.2.2.2.2.1]
    · apply rawBond_exact_of_bondOrder_positive <;> try decide
      simp [iupacP93CanonicalFullereneC70SuperimposedSecondBondOrders.2.2.2.2.2]


end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
