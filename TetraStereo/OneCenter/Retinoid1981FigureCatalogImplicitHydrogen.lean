import TetraStereo.OneCenter.Retinoid1981StereoparentTableImplicitHydrogen
import TetraStereo.KernelOnly

set_option autoImplicit false













namespace TetraStereo.OneCenter
namespace Retinoid1981
namespace FigureCatalogImplicitHydrogen

open FigureAuthorityInput
open StereoparentTableImplicitHydrogen

def sourceSpecificFigureMolecularFormulas :
    List (SourceAudit.ImageArtifact × SourceSpecificVariant × MolecularFormula) :=
  sourceSpecificAuthorityInputCandidates.filterMap fun entry => do
    let formula ← molecularFormula? entry.candidate.graph
    pure (entry.candidate.artifact, entry.variant, formula)

@[simp] theorem source_specific_figure_molecular_formulas_exact :
    sourceSpecificFigureMolecularFormulas =
      [ (.stereoparentSkeleton, .literalFigureGraph, ⟨20, 30, 0, 0, 0⟩)
      , (.glucuronideSubstituent, .retinoylGlucuronide, ⟨26, 36, 0, 8, 0⟩)
      , (.didehydroretinol, .literalFigureGraph, ⟨20, 28, 0, 1, 0⟩)
      , (.alphaVitaminA, .literalFigureGraph, ⟨20, 30, 0, 1, 0⟩)
      , (.epoxyDihydroretinol, .literalFigureGraph, ⟨20, 30, 0, 2, 0⟩)
      , (.fluororetinoate, .literalFigureGraph, ⟨22, 31, 0, 2, 1⟩)
      , (.secoRetinol, .literalFigureGraph, ⟨20, 30, 0, 1, 0⟩)
      , (.motretinideEtretinate, .motretinide, ⟨23, 31, 1, 2, 0⟩)
      , (.motretinideEtretinate, .etretinate, ⟨23, 30, 0, 3, 0⟩)
      , (.acetylDinorRetinoicAcid, .literalFigureGraph, ⟨20, 26, 0, 3, 0⟩)
      , (.anhydroVitaminA, .literalFigureGraph, ⟨20, 28, 0, 0, 0⟩)
      , (.retroRetinylAcetate, .literalFigureGraph, ⟨22, 32, 0, 2, 0⟩)
      , (.hydroxyAcetoxyRetinol, .literalFigureGraph, ⟨20, 30, 0, 2, 0⟩)
      , (.hydroxyAcetoxyRetinol, .literalFigureGraph, ⟨22, 32, 0, 3, 0⟩)
      , (.cisRetinoidExamples, .literalFigureGraph, ⟨20, 30, 0, 1, 0⟩)
      , (.cisRetinoidExamples, .literalFigureGraph, ⟨20, 28, 0, 2, 0⟩)
      , (.retroRetinalOxime, .literalFigureGraph, ⟨20, 29, 1, 1, 0⟩) ] := by
  decide

structure CompletedSourceSpecificFigureImplicitHydrogen where
  candidate : SourceSpecificAuthorityInputCandidate
  implicitHydrogens : List Nat
  formula : MolecularFormula
  implicitHydrogensExact :
    implicitHydrogenCounts? candidate.candidate.graph = some implicitHydrogens
  formulaExact :
    formula = formulaFromImplicitHydrogens candidate.candidate.graph implicitHydrogens
  atomCoverageExact :
    implicitHydrogens.length = candidate.candidate.graph.nodes.length
  heavyAtomCountExact :
    formula.heavyAtomCount = candidate.candidate.graph.nodes.length

def completeFigureImplicitHydrogens?
    (candidate : SourceSpecificAuthorityInputCandidate) :
    Option CompletedSourceSpecificFigureImplicitHydrogen :=
  match observed : implicitHydrogenCounts? candidate.candidate.graph with
  | none => none
  | some implicitHydrogens =>
      let formula := formulaFromImplicitHydrogens candidate.candidate.graph implicitHydrogens
      if atomCoverageExact :
          implicitHydrogens.length = candidate.candidate.graph.nodes.length then
        if heavyAtomCountExact :
            formula.heavyAtomCount = candidate.candidate.graph.nodes.length then
          some
            { candidate := candidate
              implicitHydrogens := implicitHydrogens
              formula := formula
              implicitHydrogensExact := observed
              formulaExact := rfl
              atomCoverageExact := atomCoverageExact
              heavyAtomCountExact := heavyAtomCountExact }
        else none
      else none

def completedSourceSpecificFigureImplicitHydrogens :
    List CompletedSourceSpecificFigureImplicitHydrogen :=
  sourceSpecificAuthorityInputCandidates.filterMap
    completeFigureImplicitHydrogens?

def unresolvedSourceSpecificFigureImplicitHydrogens :
    List SourceSpecificAuthorityInputCandidate :=
  sourceSpecificAuthorityInputCandidates.filter fun candidate =>
    (completeFigureImplicitHydrogens? candidate).isNone

@[simp] theorem completed_source_specific_figure_implicit_hydrogen_count :
    completedSourceSpecificFigureImplicitHydrogens.length = 17 := by
  decide

@[simp] theorem unresolved_source_specific_figure_implicit_hydrogens_empty :
    unresolvedSourceSpecificFigureImplicitHydrogens = [] := by
  decide

@[simp] theorem completed_hydrogen_count_covers_every_figure_atom
    (entry : CompletedSourceSpecificFigureImplicitHydrogen) :
    entry.implicitHydrogens.length = entry.candidate.candidate.graph.nodes.length :=
  entry.atomCoverageExact

@[simp] theorem completed_figure_formula_heavy_atom_count_exact
    (entry : CompletedSourceSpecificFigureImplicitHydrogen) :
    entry.formula.heavyAtomCount = entry.candidate.candidate.graph.nodes.length :=
  entry.heavyAtomCountExact

end FigureCatalogImplicitHydrogen
end Retinoid1981
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureCatalogImplicitHydrogen.source_specific_figure_molecular_formulas_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureCatalogImplicitHydrogen.completed_source_specific_figure_implicit_hydrogen_count
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureCatalogImplicitHydrogen.unresolved_source_specific_figure_implicit_hydrogens_empty
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureCatalogImplicitHydrogen.completed_hydrogen_count_covers_every_figure_atom
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureCatalogImplicitHydrogen.completed_figure_formula_heavy_atom_count_exact
