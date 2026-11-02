import TetraStereo.OneCenter.CIPAuthoritativeBranchComparator

set_option autoImplicit false

namespace TetraStereo.Examples.AuthoritativeBranchComparator

open OneCenter

private def atom (element : Element) : AtomSpec :=
  { element := element, explicitHydrogens? := some 0 }

/-! Two ligand roots each have four real children. Their first child spheres tie (`C,C,C,C`), and
the first difference is one level deeper (`Br > Cl`). The tetravalent three-child fast path must
refuse this input; the bonding-number-six authoritative path must retain and decide it. -/
private def wideBranchMolecule : RawMolecule where
  atoms :=
    [ atom .C, atom .C, atom .C, atom .C, atom .C, atom .C, atom .Br,
      atom .C, atom .C, atom .C, atom .C, atom .C, atom .Cl ]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 1, target := 2, kind := .single },
      { source := 1, target := 3, kind := .single },
      { source := 1, target := 4, kind := .single },
      { source := 1, target := 5, kind := .single },
      { source := 2, target := 6, kind := .single },
      { source := 0, target := 7, kind := .single },
      { source := 7, target := 8, kind := .single },
      { source := 7, target := 9, kind := .single },
      { source := 7, target := 10, kind := .single },
      { source := 7, target := 11, kind := .single },
      { source := 8, target := 12, kind := .single } ]

theorem three_child_fast_path_refuses_wide_branch :
    wideBranchMolecule.compareBranches? 32 0 1 7 = none := by
  decide

theorem bonding_number_six_path_retains_deeper_Br_over_Cl :
    wideBranchMolecule.compareBranchesAuthoritative? 0 1 7 = some Ordering.gt := by
  decide

/-! A chorded fourteen-member localized mancude component has fifteen resonance edges.  It is not
a structurally simple cycle, so it exercises the complete finite maximum-matching family and
obtains the exact carbon label `(6 + 6 + 6) / 3 = 6` on both executable paths. -/
private def largeMancudeMolecule : RawMolecule where
  atoms := List.replicate 14 (atom .C)
  bonds :=
    [ { source := 0, target := 1, kind := .double },
      { source := 1, target := 2, kind := .single },
      { source := 2, target := 3, kind := .double },
      { source := 3, target := 4, kind := .single },
      { source := 4, target := 5, kind := .double },
      { source := 5, target := 6, kind := .single },
      { source := 6, target := 7, kind := .double },
      { source := 7, target := 8, kind := .single },
      { source := 8, target := 9, kind := .double },
      { source := 9, target := 10, kind := .single },
      { source := 10, target := 11, kind := .double },
      { source := 11, target := 12, kind := .single },
      { source := 12, target := 13, kind := .double },
      { source := 13, target := 0, kind := .single },
      { source := 0, target := 7, kind := .single } ]

theorem production_rule1a_averages_all_maximum_matchings :
    largeMancudeMolecule.generalMancudeRule1aLabel? 0 1 =
      some { numerator := 18, denominator := 3 } := by
  decide

theorem authoritative_rule1a_averages_all_maximum_matchings :
    largeMancudeMolecule.generalMancudeRule1aLabelAuthoritative? 0 1 =
      some { numerator := 18, denominator := 3 } := by
  decide

end TetraStereo.Examples.AuthoritativeBranchComparator
