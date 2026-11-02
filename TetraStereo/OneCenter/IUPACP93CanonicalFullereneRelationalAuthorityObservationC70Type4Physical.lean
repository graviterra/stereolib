import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalAuthorityObservationFoundation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Physical certificates for the relational P-93 C70 type-4 observation. -/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

theorem iupacP93CanonicalFullereneC70Type4Center74PhysicalValid :
    (P93AuthorityPhysicalUnit.atomCenter 74).ValidFor
      iupacP93CanonicalFullereneRelationalAuthorityPhysicalPolicy
      iupacP93CanonicalFullereneC70Type4AuthoritySource := by
  apply p93AuthorityAtomCenterValid_of_rawNeighbors
    iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
    iupacP93CanonicalFullereneC70Type4RelationalInput.cage.carrier
    iupacP93CanonicalFullereneC70Type4AuthoritySource
    iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.1
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

theorem iupacP93CanonicalFullereneC70Type4Center87PhysicalValid :
    (P93AuthorityPhysicalUnit.atomCenter 87).ValidFor
      iupacP93CanonicalFullereneRelationalAuthorityPhysicalPolicy
      iupacP93CanonicalFullereneC70Type4AuthoritySource := by
  apply p93AuthorityAtomCenterValid_of_rawNeighbors
    iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
    iupacP93CanonicalFullereneC70Type4RelationalInput.cage.carrier
    iupacP93CanonicalFullereneC70Type4AuthoritySource
    iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.1
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

theorem iupacP93CanonicalFullereneC70Type4SecondInternalBondOrder
    (left right : Fin
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.externalAtoms.length) :
    iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble.bondOrder
        (97 + left) (97 + right) =
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.localMolecule.bondOrder
        left right := by
  simpa [molecularFullereneAddendExternalOffset,
    molecularFullereneAddendPrefixAtomCount,
    iupacP93CanonicalFullereneC70Type4Assembly,
    compileIUPACP93PrintedFullereneAddendAssembly,
    iupacP93CanonicalFullereneC70Type4Placements] using
    iupacP93CanonicalFullereneC70Type4Assembly.compiledAddend_internalBondOrder
      iupacP93CanonicalFullereneC70Core_wellFormed 1
      iupacP93CanonicalFullereneC70Type4SecondPlacement.toPlaced rfl left right

theorem iupacP93CanonicalFullereneC70Type4SecondBondOrders :
    iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble.bondOrder 100 101 = 1 ∧
    iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble.bondOrder 101 102 = 1 ∧
    iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble.bondOrder 101 105 = 1 ∧
    iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble.bondOrder 113 114 = 1 ∧
    iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble.bondOrder 114 115 = 1 ∧
    iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble.bondOrder 114 118 = 1 := by
  exact ⟨
    by simpa [MolecularFullereneLocalAddendTemplate.localMolecule,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylBonds,
      RawMolecule.bondOrder, RawMolecule.directedBondOrder, RawBond.directedConnects] using
        iupacP93CanonicalFullereneC70Type4SecondInternalBondOrder ⟨3, by decide⟩ ⟨4, by decide⟩,
    by simpa [MolecularFullereneLocalAddendTemplate.localMolecule,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylBonds,
      RawMolecule.bondOrder, RawMolecule.directedBondOrder, RawBond.directedConnects] using
        iupacP93CanonicalFullereneC70Type4SecondInternalBondOrder ⟨4, by decide⟩ ⟨5, by decide⟩,
    by simpa [MolecularFullereneLocalAddendTemplate.localMolecule,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylBonds,
      RawMolecule.bondOrder, RawMolecule.directedBondOrder, RawBond.directedConnects] using
        iupacP93CanonicalFullereneC70Type4SecondInternalBondOrder ⟨4, by decide⟩ ⟨8, by decide⟩,
    by simpa [MolecularFullereneLocalAddendTemplate.localMolecule,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylBonds,
      RawMolecule.bondOrder, RawMolecule.directedBondOrder, RawBond.directedConnects] using
        iupacP93CanonicalFullereneC70Type4SecondInternalBondOrder ⟨16, by decide⟩ ⟨17, by decide⟩,
    by simpa [MolecularFullereneLocalAddendTemplate.localMolecule,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylBonds,
      RawMolecule.bondOrder, RawMolecule.directedBondOrder, RawBond.directedConnects] using
        iupacP93CanonicalFullereneC70Type4SecondInternalBondOrder ⟨17, by decide⟩ ⟨18, by decide⟩,
    by simpa [MolecularFullereneLocalAddendTemplate.localMolecule,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate,
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylBonds,
      RawMolecule.bondOrder, RawMolecule.directedBondOrder, RawBond.directedConnects] using
        iupacP93CanonicalFullereneC70Type4SecondInternalBondOrder ⟨17, by decide⟩ ⟨21, by decide⟩⟩

theorem iupacP93CanonicalFullereneC70Type4Center101PhysicalValid :
    (P93AuthorityPhysicalUnit.atomCenter 101).ValidFor
      iupacP93CanonicalFullereneRelationalAuthorityPhysicalPolicy
      iupacP93CanonicalFullereneC70Type4AuthoritySource := by
  apply p93AuthorityAtomCenterValid_of_rawNeighbors
    iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
    iupacP93CanonicalFullereneC70Type4RelationalInput.cage.carrier
    iupacP93CanonicalFullereneC70Type4AuthoritySource
    iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.1
    101 [100, 102, 105]
  · decide
  · decide
  · decide
  · decide
  · intro neighbor neighborPresent
    simp only [List.mem_cons, List.not_mem_nil, or_false] at neighborPresent
    rcases neighborPresent with rfl | rfl | rfl
    · apply rawBond_exact_of_bondOrder_positive <;> try decide
      rw [iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble.bondOrder_symm]
      simp [iupacP93CanonicalFullereneC70Type4SecondBondOrders.1]
    · apply rawBond_exact_of_bondOrder_positive <;> try decide
      simp [iupacP93CanonicalFullereneC70Type4SecondBondOrders.2.1]
    · apply rawBond_exact_of_bondOrder_positive <;> try decide
      simp [iupacP93CanonicalFullereneC70Type4SecondBondOrders.2.2.1]

theorem iupacP93CanonicalFullereneC70Type4Center114PhysicalValid :
    (P93AuthorityPhysicalUnit.atomCenter 114).ValidFor
      iupacP93CanonicalFullereneRelationalAuthorityPhysicalPolicy
      iupacP93CanonicalFullereneC70Type4AuthoritySource := by
  apply p93AuthorityAtomCenterValid_of_rawNeighbors
    iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
    iupacP93CanonicalFullereneC70Type4RelationalInput.cage.carrier
    iupacP93CanonicalFullereneC70Type4AuthoritySource
    iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.1
    114 [113, 115, 118]
  · decide
  · decide
  · decide
  · decide
  · intro neighbor neighborPresent
    simp only [List.mem_cons, List.not_mem_nil, or_false] at neighborPresent
    rcases neighborPresent with rfl | rfl | rfl
    · apply rawBond_exact_of_bondOrder_positive <;> try decide
      rw [iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble.bondOrder_symm]
      simp [iupacP93CanonicalFullereneC70Type4SecondBondOrders.2.2.2.1]
    · apply rawBond_exact_of_bondOrder_positive <;> try decide
      simp [iupacP93CanonicalFullereneC70Type4SecondBondOrders.2.2.2.2.1]
    · apply rawBond_exact_of_bondOrder_positive <;> try decide
      simp [iupacP93CanonicalFullereneC70Type4SecondBondOrders.2.2.2.2.2]


end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
