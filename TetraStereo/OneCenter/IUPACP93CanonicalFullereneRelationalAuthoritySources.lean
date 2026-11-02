import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalSourceInputs

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# Canonical authoritative inputs for the five relational fullerene rows

Each source is the successful value of the exact carrier-relative topology adapter.  Internal
cage bonds are represented as unspecified covalent adjacency; every non-cage bond, atom, parser
configuration, and optional spatial projection is retained exactly.  These are frozen values,
not parameters supplied by a caller.
-/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

def iupacP93CanonicalFullereneC76Type1AuthoritySource? :
    Option AuthoritativeChemicalInput :=
  iupacP93CanonicalFullereneC76Type1Molecule
    |>.toMolecularFullereneTopologyAuthoritativeInput?
      iupacP93CanonicalFullereneC76Type1RelationalInput.cage.carrier none

def iupacP93CanonicalFullereneC60Type2AuthoritySource? :
    Option AuthoritativeChemicalInput :=
  iupacP93CanonicalFullereneC60Type2Molecule
    |>.toMolecularFullereneTopologyAuthoritativeInput?
      iupacP93CanonicalFullereneC60Type2RelationalInput.cage.carrier none

def iupacP93CanonicalFullereneC60Type3AuthoritySource? :
    Option AuthoritativeChemicalInput :=
  iupacP93CanonicalFullereneC60Type3Molecule
    |>.toMolecularFullereneTopologyAuthoritativeInput?
      iupacP93CanonicalFullereneC60Type3RelationalInput.cage.carrier none

def iupacP93CanonicalFullereneC70Type4AuthoritySource? :
    Option AuthoritativeChemicalInput :=
  iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
    |>.toMolecularFullereneTopologyAuthoritativeInput?
      iupacP93CanonicalFullereneC70Type4RelationalInput.cage.carrier none

def iupacP93CanonicalFullereneC70SuperimposedAuthoritySource? :
    Option AuthoritativeChemicalInput :=
  iupacP93CanonicalFullereneC70SuperimposedMolecule
    |>.toMolecularFullereneTopologyAuthoritativeInput?
      iupacP93CanonicalFullereneC70SuperimposedRelationalInput.cage.carrier none

theorem iupacP93CanonicalFullereneAuthoritySources_all_isSome :
    iupacP93CanonicalFullereneC76Type1AuthoritySource?.isSome = true ∧
    iupacP93CanonicalFullereneC60Type2AuthoritySource?.isSome = true ∧
    iupacP93CanonicalFullereneC60Type3AuthoritySource?.isSome = true ∧
    iupacP93CanonicalFullereneC70Type4AuthoritySource?.isSome = true ∧
    iupacP93CanonicalFullereneC70SuperimposedAuthoritySource?.isSome = true := by
  decide

def iupacP93CanonicalFullereneC76Type1AuthoritySource : AuthoritativeChemicalInput :=
  iupacP93CanonicalFullereneC76Type1AuthoritySource?.get
    iupacP93CanonicalFullereneAuthoritySources_all_isSome.1

def iupacP93CanonicalFullereneC60Type2AuthoritySource : AuthoritativeChemicalInput :=
  iupacP93CanonicalFullereneC60Type2AuthoritySource?.get
    iupacP93CanonicalFullereneAuthoritySources_all_isSome.2.1

def iupacP93CanonicalFullereneC60Type3AuthoritySource : AuthoritativeChemicalInput :=
  iupacP93CanonicalFullereneC60Type3AuthoritySource?.get
    iupacP93CanonicalFullereneAuthoritySources_all_isSome.2.2.1

def iupacP93CanonicalFullereneC70Type4AuthoritySource : AuthoritativeChemicalInput :=
  iupacP93CanonicalFullereneC70Type4AuthoritySource?.get
    iupacP93CanonicalFullereneAuthoritySources_all_isSome.2.2.2.1

def iupacP93CanonicalFullereneC70SuperimposedAuthoritySource :
    AuthoritativeChemicalInput :=
  iupacP93CanonicalFullereneC70SuperimposedAuthoritySource?.get
    iupacP93CanonicalFullereneAuthoritySources_all_isSome.2.2.2.2

theorem iupacP93CanonicalFullereneC76Type1AuthoritySource_exact :
    iupacP93CanonicalFullereneC76Type1AuthoritySource? =
      some iupacP93CanonicalFullereneC76Type1AuthoritySource := by
  simp [iupacP93CanonicalFullereneC76Type1AuthoritySource]

theorem iupacP93CanonicalFullereneC60Type2AuthoritySource_exact :
    iupacP93CanonicalFullereneC60Type2AuthoritySource? =
      some iupacP93CanonicalFullereneC60Type2AuthoritySource := by
  simp [iupacP93CanonicalFullereneC60Type2AuthoritySource]

theorem iupacP93CanonicalFullereneC60Type3AuthoritySource_exact :
    iupacP93CanonicalFullereneC60Type3AuthoritySource? =
      some iupacP93CanonicalFullereneC60Type3AuthoritySource := by
  simp [iupacP93CanonicalFullereneC60Type3AuthoritySource]

theorem iupacP93CanonicalFullereneC70Type4AuthoritySource_exact :
    iupacP93CanonicalFullereneC70Type4AuthoritySource? =
      some iupacP93CanonicalFullereneC70Type4AuthoritySource := by
  simp [iupacP93CanonicalFullereneC70Type4AuthoritySource]

theorem iupacP93CanonicalFullereneC70SuperimposedAuthoritySource_exact :
    iupacP93CanonicalFullereneC70SuperimposedAuthoritySource? =
      some iupacP93CanonicalFullereneC70SuperimposedAuthoritySource := by
  simp [iupacP93CanonicalFullereneC70SuperimposedAuthoritySource]

theorem iupacP93CanonicalFullereneAuthoritySources_all_agree :
    iupacP93CanonicalFullereneC76Type1Molecule.MolecularFullereneTopologyRepresentationAgreement
        iupacP93CanonicalFullereneC76Type1RelationalInput.cage.carrier none
        iupacP93CanonicalFullereneC76Type1AuthoritySource ∧
    iupacP93CanonicalFullereneC60Type2Molecule.MolecularFullereneTopologyRepresentationAgreement
        iupacP93CanonicalFullereneC60Type2RelationalInput.cage.carrier none
        iupacP93CanonicalFullereneC60Type2AuthoritySource ∧
    iupacP93CanonicalFullereneC60Type3Molecule.MolecularFullereneTopologyRepresentationAgreement
        iupacP93CanonicalFullereneC60Type3RelationalInput.cage.carrier none
        iupacP93CanonicalFullereneC60Type3AuthoritySource ∧
    (iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
        |>.MolecularFullereneTopologyRepresentationAgreement
          iupacP93CanonicalFullereneC70Type4RelationalInput.cage.carrier none
          iupacP93CanonicalFullereneC70Type4AuthoritySource) ∧
    (iupacP93CanonicalFullereneC70SuperimposedMolecule
        |>.MolecularFullereneTopologyRepresentationAgreement
          iupacP93CanonicalFullereneC70SuperimposedRelationalInput.cage.carrier none
          iupacP93CanonicalFullereneC70SuperimposedAuthoritySource) := by
  exact ⟨
    iupacP93CanonicalFullereneC76Type1Molecule
      |>.toMolecularFullereneTopologyAuthoritativeInput?_exact _ none _
        iupacP93CanonicalFullereneC76Type1AuthoritySource_exact,
    iupacP93CanonicalFullereneC60Type2Molecule
      |>.toMolecularFullereneTopologyAuthoritativeInput?_exact _ none _
        iupacP93CanonicalFullereneC60Type2AuthoritySource_exact,
    iupacP93CanonicalFullereneC60Type3Molecule
      |>.toMolecularFullereneTopologyAuthoritativeInput?_exact _ none _
        iupacP93CanonicalFullereneC60Type3AuthoritySource_exact,
    iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
      |>.toMolecularFullereneTopologyAuthoritativeInput?_exact _ none _
        iupacP93CanonicalFullereneC70Type4AuthoritySource_exact,
    iupacP93CanonicalFullereneC70SuperimposedMolecule
      |>.toMolecularFullereneTopologyAuthoritativeInput?_exact _ none _
        iupacP93CanonicalFullereneC70SuperimposedAuthoritySource_exact⟩

theorem iupacP93CanonicalFullereneAuthoritySources_all_structurallyWellFormed :
    iupacP93CanonicalFullereneC76Type1AuthoritySource.StructurallyWellFormed ∧
    iupacP93CanonicalFullereneC60Type2AuthoritySource.StructurallyWellFormed ∧
    iupacP93CanonicalFullereneC60Type3AuthoritySource.StructurallyWellFormed ∧
    iupacP93CanonicalFullereneC70Type4AuthoritySource.StructurallyWellFormed ∧
    iupacP93CanonicalFullereneC70SuperimposedAuthoritySource.StructurallyWellFormed := by
  exact ⟨
    iupacP93CanonicalFullereneC76Type1Molecule
      |>.toMolecularFullereneTopologyAuthoritativeInput?_structurallyWellFormed _ none _
        iupacP93CanonicalFullereneC76Type1AuthoritySource_exact
        (iupacP93CanonicalFullereneC76Type1Assembly.assembleWellFormed
          iupacP93CanonicalFullereneC76Core_wellFormed) (by simp),
    iupacP93CanonicalFullereneC60Type2Molecule
      |>.toMolecularFullereneTopologyAuthoritativeInput?_structurallyWellFormed _ none _
        iupacP93CanonicalFullereneC60Type2AuthoritySource_exact
        (iupacP93CanonicalFullereneC60Type2Assembly.assembleWellFormed
          iupacP93CanonicalFullereneC60Core_wellFormed) (by simp),
    iupacP93CanonicalFullereneC60Type3Molecule
      |>.toMolecularFullereneTopologyAuthoritativeInput?_structurallyWellFormed _ none _
        iupacP93CanonicalFullereneC60Type3AuthoritySource_exact
        (iupacP93CanonicalFullereneC60Type3Assembly.assembleWellFormed
          iupacP93CanonicalFullereneC60Core_wellFormed) (by simp),
    iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
      |>.toMolecularFullereneTopologyAuthoritativeInput?_structurallyWellFormed _ none _
        iupacP93CanonicalFullereneC70Type4AuthoritySource_exact
        (iupacP93CanonicalFullereneC70Type4Assembly.assembleWellFormed
          iupacP93CanonicalFullereneC70Core_wellFormed) (by simp),
    iupacP93CanonicalFullereneC70SuperimposedMolecule
      |>.toMolecularFullereneTopologyAuthoritativeInput?_structurallyWellFormed _ none _
        iupacP93CanonicalFullereneC70SuperimposedAuthoritySource_exact
        (iupacP93CanonicalFullereneC70SuperimposedAssembly.assembleWellFormed
          iupacP93CanonicalFullereneC70Core_wellFormed) (by simp)⟩

end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
