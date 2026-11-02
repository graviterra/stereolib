import TetraStereo.OneCenter.CIPAuthoritativeOccurrenceComparator

set_option autoImplicit false

namespace TetraStereo.Examples.AuthoritativeOccurrenceComparator

open OneCenter

private def atom (element : Element) : AtomSpec :=
  { element := element, explicitHydrogens? := some 0 }

/-! Each compared root has four real child occurrences.  The first child sphere ties and the
decision is one level deeper (`Br > Cl`).  This exercises the re-rooted occurrence comparator used
by descriptor-bearing cyclic ligands, not merely the molecular-root comparator. -/
private def molecule : RawMolecule where
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

private def left : CanonicalRerootCursor := { node := RawMolecule.canonicalRoot 0 1 }
private def right : CanonicalRerootCursor := { node := RawMolecule.canonicalRoot 0 7 }

theorem three_child_occurrence_path_refuses :
    compareCursorBranchAt molecule (molecule.atomCount + 1) .rule2 left right = none := by
  decide

theorem authoritative_occurrence_path_reaches_deeper_priority :
    compareCursorBranchAtAuthoritative? molecule (molecule.atomCount + 1) .rule2 left right =
      some Ordering.gt := by
  decide

theorem authoritative_rules_1a_through_5_retain_constitutional_decision :
    compareOccurrenceBranchesAuthoritative? molecule [] (molecule.atomCount + 1) left right =
      some { ordering := Ordering.gt } := by
  decide

end TetraStereo.Examples.AuthoritativeOccurrenceComparator
