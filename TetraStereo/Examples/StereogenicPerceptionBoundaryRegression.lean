import TetraStereo.OneCenter.CIPStereogenicPerceptionConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter.BlueBookP92.Perception

/-- A descriptor-independent sufficient condition for an ordinary tetrahedral stereogenic center:
a supported atom has four single-bond neighbors whose first-sphere atomic numbers are all
different.  No `@`/`@@` annotation occurs in this chemical predicate. -/
def FirstSphereDistinctTetrahedralCenter (mol : RawMolecule) (center : Nat) : Prop :=
  ∃ spec ligands,
    mol.atomAt? center = some spec ∧
      RawMolecule.centreElementSupported spec.element = true ∧
      mol.writtenNeighbors center = ligands ∧
      ligands.length = 4 ∧
      (∀ ligand, ligand ∈ ligands → mol.bondOrder center ligand = 1) ∧
      (ligands.map mol.atomZAt).Nodup

end TetraStereo.OneCenter.BlueBookP92.Perception

namespace TetraStereo.Examples.StereogenicPerceptionBoundaryRegression

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery

/-- Constitutionally stereogenic bromochlorofluoromethane with an explicit hydrogen but no
configuration annotation. -/
private def unannotatedCHBrClF : RawMolecule where
  atoms :=
    [ AtomSpec.aliphatic Element.C,
      AtomSpec.aliphatic Element.Br,
      AtomSpec.aliphatic Element.Cl,
      AtomSpec.aliphatic Element.F,
      AtomSpec.aliphatic Element.H ]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single },
      { source := 0, target := 4, kind := .single } ]

private def normalized := normalizeRawMolecule unannotatedCHBrClF

private def expanded := normalized.parsed.withExplicitHydrogens

private def fuel := analysisFuel expanded

private def descriptorState := discoverRawDescriptors normalized expanded fuel

theorem constitutionally_stereogenic_without_annotation :
    BlueBookP92.Perception.FirstSphereDistinctTetrahedralCenter unannotatedCHBrClF 0 := by
  refine ⟨AtomSpec.aliphatic Element.C, [1, 2, 3, 4], ?_⟩
  decide

theorem production_final_unit_absent :
    ¬∃ root : Root unannotatedCHBrClF,
      centerAtom root = (⟨0, by decide⟩ : Fin unannotatedCHBrClF.atomCount) := by
  decide

/-- Therefore the occurrence-level descriptor-root carrier remains annotation-gated.  This no
longer implies that public chemical perception is annotation-gated. -/
theorem unrestricted_occurrence_root_completeness_is_false :
    ¬(∀ (mol : RawMolecule) (center : Fin mol.atomCount),
      BlueBookP92.Perception.FirstSphereDistinctTetrahedralCenter mol center.val →
        ∃ root : Root mol, centerAtom root = center) := by
  intro complete
  exact production_final_unit_absent
    (complete unannotatedCHBrClF ⟨0, by decide⟩
      constitutionally_stereogenic_without_annotation)

theorem production_perceives_unannotated_center_as_stereogenic :
    tetrahedralStereogenicity normalized expanded descriptorState fuel 0 =
        TetrahedralStereogenicity.stereogenic := by
  decide

/-- The chemist-facing analyzer now perceives the same unannotated stereogenic unit and reports
that its configuration was not specified. -/
theorem analyzeNormalized_reports_unannotated_stereogenic_center :
    analyzeNormalized normalized =
      [{ unit := StereoUnit.tetrahedral 0
         outcome := StereoOutcome.refused StereoRefusal.notSpecified }] := by
  decide

/-! ## Three-coordinate heteroatoms require geometry evidence -/

/-- `N`-ethyl-`N`-methylacetamide.  Its nitrogen has three constitutionally distinct atom
substituents, so blindly adding a lone-pair phantom would create four rankable positions even
though connectivity has not established a trigonal-pyramidal configuration. -/
private def unannotatedTertiaryAmide : RawMolecule where
  atoms :=
    [ AtomSpec.aliphatic Element.C,
      AtomSpec.aliphatic Element.C,
      AtomSpec.aliphatic Element.O,
      AtomSpec.aliphatic Element.N,
      AtomSpec.aliphatic Element.C,
      AtomSpec.aliphatic Element.C,
      AtomSpec.aliphatic Element.C ]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 1, target := 2, kind := .double },
      { source := 1, target := 3, kind := .single },
      { source := 3, target := 4, kind := .single },
      { source := 3, target := 5, kind := .single },
      { source := 5, target := 6, kind := .single } ]
  neighborOrder := [[1], [0, 2, 3], [1], [1, 4, 5], [3], [3, 6], [5]]

private def amideNormalized := normalizeRawMolecule unannotatedTertiaryAmide

private def amideExpanded := amideNormalized.parsed.withExplicitHydrogens

/-- The old construction really would have manufactured a fourth position at amide nitrogen 3. -/
theorem amide_lone_pair_phantom_would_make_four_positions :
    (amideExpanded.ligandsWithLonePair 3).length = 4 := by
  decide

/-- The corrected production boundary refuses to infer a tetrahedral frame from those three atom
neighbours. -/
theorem amide_has_no_connectivity_only_tetrahedral_frame :
    connectivityOnlyTetrahedralLigands? amideNormalized amideExpanded 3 = none := by
  decide

/-- The independent applicability predicate reaches the same conclusion. -/
theorem amide_is_outside_independent_connectivity_only_frame :
    ¬BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame
      amideNormalized amideExpanded 3 := by
  intro frame
  have production :=
    (connectivityOnlyTetrahedralLigands?_isSome_iff_independentFrame
      amideNormalized amideExpanded 3).2 frame
  simp [amide_has_no_connectivity_only_tetrahedral_frame] at production

/-- Consequently the chemist-facing connectivity-only pass reports no fictitious amide-nitrogen
stereogenic unit. -/
theorem analyzer_does_not_report_unannotated_tertiary_amide_nitrogen :
    analyzeNormalized amideNormalized = [] := by
  decide

end TetraStereo.Examples.StereogenicPerceptionBoundaryRegression
