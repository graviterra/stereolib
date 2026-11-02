import TetraStereo.OneCenter.AuthoritativeChemicalInput

set_option autoImplicit false

namespace TetraStereo.Examples.AuthoritativeChemicalInput

open OneCenter

theorem every_current_atomic_number_is_representable :
    ∀ atomicNumber, 0 < atomicNumber → atomicNumber ≤ 118 →
      (PeriodicElement.ofAtomicNumber? atomicNumber).isSome = true := by
  intro atomicNumber positive bounded
  exact PeriodicElement.ofAtomicNumber?_isSome atomicNumber |>.mpr ⟨positive, bounded⟩

theorem atomic_number_zero_and_119_are_rejected :
    (PeriodicElement.ofAtomicNumber? 0).isNone = true ∧
      (PeriodicElement.ofAtomicNumber? 119).isNone = true := by
  decide

private def ordinary : RawMolecule where
  atoms :=
    [ { element := .C, tetrahedral? := some .clockwise },
      { element := .F }, { element := .Cl }, { element := .Br } ]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 3, kind := .down } ]

theorem parser_molecule_embeds_with_configuration_evidence :
    (ordinary.toAuthoritativeChemicalInput?).isSome = true := by
  decide

private def unknown : RawMolecule where
  atoms := [{ element := .wildcard }]
  bonds := []

theorem wildcard_identity_cannot_cross_authority_boundary :
    unknown.toAuthoritativeChemicalInput? = none := by
  decide

private def multicenter : AuthoritativeChemicalInput :=
  let hydrogen := (PeriodicElement.ofAtomicNumber? 1).get (by decide)
  let boron := (PeriodicElement.ofAtomicNumber? 5).get (by decide)
  { molecule :=
      { atoms :=
          [ { element := boron }, { element := hydrogen }, { element := hydrogen },
            { element := boron } ]
        interactions :=
          [{ participants := [0, 1, 3], kind := .multicenter 2 },
           { participants := [0, 2, 3], kind := .multicenter 2 }] }
    spatial? := some
      { positions :=
          [ { x := -1, y := 0, z := 0 }, { x := 0, y := 1, z := 0 },
            { x := 0, y := -1, z := 0 }, { x := 1, y := 0, z := 0 } ] } }

theorem multicenter_geometry_is_structurally_admitted :
    multicenter.structurallyWellFormed? = true := by
  decide

end TetraStereo.Examples.AuthoritativeChemicalInput
