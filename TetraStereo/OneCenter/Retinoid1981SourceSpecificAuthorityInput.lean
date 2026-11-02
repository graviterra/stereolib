import TetraStereo.OneCenter.Retinoid1981CertifiedAuthorityInput
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Source-specific Retinoid 1981 authority inputs

Two figure graphs in the frozen transcription deliberately contain a generic `R` continuation.
The recommendation itself resolves those continuations: structure (10) combines A2a and A2b as
1-O-retinoyl-beta-D-glucopyranuronic acid, while A46a names separate `R=NHC2H5` (motretinide)
and `R=OC2H5` (etretinate) compounds.

This module performs exactly those three constitutional heavy-atom expansions. It retains the
generic figure graphs as literal image-transcription evidence, but replaces them in a distinct
source-specific authority-input catalog. Structural certification still does not assert implicit
hydrogens, drawing coordinates, stereochemical drawing fidelity, or independent human sign-off.
-/

namespace TetraStereo.OneCenter
namespace Retinoid1981
namespace FigureAuthorityInput

open FigureGraphTranscription

private def sourceCarbon (atomId : Nat) : AtomNode :=
  ⟨atomId, .carbon⟩

private def sourceNitrogen (atomId : Nat) : AtomNode :=
  ⟨atomId, .nitrogen⟩

private def sourceOxygen (atomId : Nat) : AtomNode :=
  ⟨atomId, .oxygen⟩

/-! ## Structure (10): A2a plus A2b -/

/-- The exact A2b-node embedding into the combined structure (10) graph. A2b's carbonyl carbon
is retinoid C-15 and its generic continuation is the already present retinoid C-14. -/
def retinoylGlucuronideSourceNodeMap : List (Nat × Nat) :=
  [ (1, 21), (2, 22), (3, 23), (4, 24), (5, 25), (6, 26)
  , (7, 27), (8, 28), (9, 29), (10, 30), (11, 31), (12, 32)
  , (13, 33), (14, 15), (15, 34), (16, 14) ]

@[simp] theorem retinoyl_glucuronide_source_node_map_exact :
    retinoylGlucuronideSourceNodeMap =
      [ (1, 21), (2, 22), (3, 23), (4, 24), (5, 25), (6, 26)
      , (7, 27), (8, 28), (9, 29), (10, 30), (11, 31), (12, 32)
      , (13, 33), (14, 15), (15, 34), (16, 14) ] := by
  rfl

private def sourceNodeTarget? : List (Nat × Nat) → Nat → Option Nat
  | [], _source => none
  | (source, target) :: remaining, requested =>
      if source = requested then some target
      else sourceNodeTarget? remaining requested

private def mapRetinoylGlucuronideSourceBond? (bond : GraphBond) : Option GraphBond := do
  let mappedLow ← sourceNodeTarget? retinoylGlucuronideSourceNodeMap bond.low
  let mappedHigh ← sourceNodeTarget? retinoylGlucuronideSourceNodeMap bond.high
  if mappedLow < mappedHigh then
    some ⟨mappedLow, mappedHigh, bond.order⟩
  else
    some ⟨mappedHigh, mappedLow, bond.order⟩

/-- Constitutional heavy-atom graph of structure (10),
1-O-retinoyl-beta-D-glucopyranuronic acid. The retinoid C-15 atom supplies the A2b carbonyl
carbon, so only the other fourteen A2b heavy atoms are added to the A2a skeleton. -/
def retinoylGlucuronideGraph : HeavyAtomGraph :=
  compileEdits stereoparentSkeletonGraph
    [ .addNode (sourceCarbon 21)
    , .addNode (sourceCarbon 22)
    , .addNode (sourceCarbon 23)
    , .addNode (sourceCarbon 24)
    , .addNode (sourceCarbon 25)
    , .addNode (sourceOxygen 26)
    , .addNode (sourceCarbon 27)
    , .addNode (sourceOxygen 28)
    , .addNode (sourceOxygen 29)
    , .addNode (sourceOxygen 30)
    , .addNode (sourceOxygen 31)
    , .addNode (sourceOxygen 32)
    , .addNode (sourceOxygen 33)
    , .addNode (sourceOxygen 34)
    , .addBond ⟨21, 22, .single⟩
    , .addBond ⟨22, 23, .single⟩
    , .addBond ⟨23, 24, .single⟩
    , .addBond ⟨24, 25, .single⟩
    , .addBond ⟨25, 26, .single⟩
    , .addBond ⟨21, 26, .single⟩
    , .addBond ⟨25, 27, .single⟩
    , .addBond ⟨27, 28, .double⟩
    , .addBond ⟨27, 29, .single⟩
    , .addBond ⟨22, 30, .single⟩
    , .addBond ⟨23, 31, .single⟩
    , .addBond ⟨24, 32, .single⟩
    , .addBond ⟨21, 33, .single⟩
    , .addBond ⟨15, 33, .single⟩
    , .addBond ⟨15, 34, .double⟩ ]

@[simp] theorem retinoyl_glucuronide_counts :
    retinoylGlucuronideGraph.nodes.length = 34 ∧
      retinoylGlucuronideGraph.bonds.length = 35 := by
  decide

/-- All sixteen A2b bonds survive the node embedding, including the carbonyl-C--retinoid-C14
bond already present as C14--C15 in A2a. -/
def retinoylGlucuronideMappedSourceBonds : List GraphBond :=
  glucuronideSubstituentGraph.bonds.filterMap
    mapRetinoylGlucuronideSourceBond?

@[simp] theorem retinoyl_glucuronide_source_bonds_embedded :
    retinoylGlucuronideMappedSourceBonds.length = 16 ∧
      retinoylGlucuronideMappedSourceBonds.all
        retinoylGlucuronideGraph.bonds.contains = true := by
  decide

/-! ## A46a: its two named R-group compounds -/

/-- A46a with `R=NHC2H5`: motretinide. Node 24 becomes nitrogen and nodes 26--27 are
the printed ethyl group. The N-H hydrogen remains implicit, as in the source drawing. -/
def motretinideGraph : HeavyAtomGraph :=
  compileEdits motretinideEtretinateGraph
    [ .removeNode 24
    , .addNode (sourceNitrogen 24)
    , .addNode (sourceCarbon 26)
    , .addNode (sourceCarbon 27)
    , .addBond ⟨15, 24, .single⟩
    , .addBond ⟨24, 26, .single⟩
    , .addBond ⟨26, 27, .single⟩ ]

/-- A46a with `R=OC2H5`: etretinate. Node 24 becomes oxygen and nodes 26--27 are
the printed ethyl group. -/
def etretinateGraph : HeavyAtomGraph :=
  compileEdits motretinideEtretinateGraph
    [ .removeNode 24
    , .addNode (sourceOxygen 24)
    , .addNode (sourceCarbon 26)
    , .addNode (sourceCarbon 27)
    , .addBond ⟨15, 24, .single⟩
    , .addBond ⟨24, 26, .single⟩
    , .addBond ⟨26, 27, .single⟩ ]

@[simp] theorem motretinide_counts :
    motretinideGraph.nodes.length = 26 ∧ motretinideGraph.bonds.length = 26 := by
  decide

@[simp] theorem etretinate_counts :
    etretinateGraph.nodes.length = 26 ∧ etretinateGraph.bonds.length = 26 := by
  decide

private def selectedA46aSubstituentAtoms (graph : HeavyAtomGraph) :
    List (Nat × AtomElement) :=
  (graph.nodes.filter fun node =>
    node.locant == 24 || node.locant == 26 || node.locant == 27).map fun node =>
      (node.locant, node.element)

def motretinideSubstituentAtoms : List (Nat × AtomElement) :=
  selectedA46aSubstituentAtoms motretinideGraph

def etretinateSubstituentAtoms : List (Nat × AtomElement) :=
  selectedA46aSubstituentAtoms etretinateGraph

@[simp] theorem motretinide_substituent_atoms_exact :
    motretinideSubstituentAtoms =
      [ (24, .nitrogen), (26, .carbon), (27, .carbon) ] := by
  decide

@[simp] theorem etretinate_substituent_atoms_exact :
    etretinateSubstituentAtoms =
      [ (24, .oxygen), (26, .carbon), (27, .carbon) ] := by
  decide

theorem source_specific_expansion_graphs_wellFormed :
    retinoylGlucuronideGraph.WellFormed ∧
      motretinideGraph.WellFormed ∧ etretinateGraph.WellFormed := by
  have glucuronide : retinoylGlucuronideGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have motretinide : motretinideGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have etretinate : etretinateGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  exact ⟨glucuronide, motretinide, etretinate⟩

/-! ## Fully concrete source-specific catalog -/

inductive SourceSpecificVariant where
  | literalFigureGraph
  | retinoylGlucuronide
  | motretinide
  | etretinate
  deriving DecidableEq, Repr

structure SourceSpecificAuthorityInputCandidate where
  variant : SourceSpecificVariant
  candidate : AuthorityInputCandidate
  deriving DecidableEq, Repr

private def expandSourceSpecificCandidate (candidate : AuthorityInputCandidate) :
    List SourceSpecificAuthorityInputCandidate :=
  match candidate.artifact with
  | .glucuronideSubstituent =>
      [ ⟨.retinoylGlucuronide,
          ⟨.glucuronideSubstituent, retinoylGlucuronideGraph⟩⟩ ]
  | .motretinideEtretinate =>
      [ ⟨.motretinide, ⟨.motretinideEtretinate, motretinideGraph⟩⟩
      , ⟨.etretinate, ⟨.motretinideEtretinate, etretinateGraph⟩⟩ ]
  | _ => [⟨.literalFigureGraph, candidate⟩]

/-- The sixteen literal graph occurrences become seventeen source-specific compounds because
A46a denotes two separately named products. -/
def sourceSpecificAuthorityInputCandidates :
    List SourceSpecificAuthorityInputCandidate :=
  authorityInputCandidates.flatMap expandSourceSpecificCandidate

@[simp] theorem source_specific_authority_input_candidate_count :
    sourceSpecificAuthorityInputCandidates.length = 17 := by
  decide

def sourceSpecificCompoundVariants : List SourceSpecificVariant :=
  sourceSpecificAuthorityInputCandidates.filterMap fun entry =>
    match entry.variant with
    | .literalFigureGraph => none
    | sourceSpecific => some sourceSpecific

@[simp] theorem source_specific_compound_variants_exact :
    sourceSpecificCompoundVariants =
      [ .retinoylGlucuronide, .motretinide, .etretinate ] := by
  decide

@[simp] theorem source_specific_candidates_have_no_generic_atoms :
    sourceSpecificAuthorityInputCandidates.all
      (fun entry => entry.candidate.graph.nodes.all
        (fun node => node.element != .genericSubstituent)) = true := by
  decide

structure CertifiedSourceSpecificAuthorityInput where
  candidate : SourceSpecificAuthorityInputCandidate
  certified : CertifiedGraphAuthorityInput
  candidateExact : certified.candidate = candidate.candidate

def SourceSpecificAuthorityInputCandidate.certify?
    (candidate : SourceSpecificAuthorityInputCandidate) :
    Option CertifiedSourceSpecificAuthorityInput := do
  let certified ← candidate.candidate.certify?
  if candidateExact : certified.candidate = candidate.candidate then
    some { candidate := candidate, certified := certified, candidateExact := candidateExact }
  else none

def certifiedSourceSpecificAuthorityInputs :
    List CertifiedSourceSpecificAuthorityInput :=
  sourceSpecificAuthorityInputCandidates.filterMap
    SourceSpecificAuthorityInputCandidate.certify?

def unresolvedSourceSpecificAuthorityInputs :
    List SourceSpecificAuthorityInputCandidate :=
  sourceSpecificAuthorityInputCandidates.filter fun candidate =>
    candidate.certify?.isNone

@[simp] theorem certified_source_specific_authority_input_count :
    certifiedSourceSpecificAuthorityInputs.length = 17 := by
  decide

@[simp] theorem unresolved_source_specific_authority_inputs_empty :
    unresolvedSourceSpecificAuthorityInputs = [] := by
  decide

theorem every_source_specific_authority_input_structurally_wellFormed
    (entry : CertifiedSourceSpecificAuthorityInput) :
    entry.certified.certified.input.StructurallyWellFormed :=
  entry.certified.certified.structurallyWellFormed

end FigureAuthorityInput
end Retinoid1981
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.retinoyl_glucuronide_source_node_map_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.retinoyl_glucuronide_source_bonds_embedded
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.motretinide_substituent_atoms_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.etretinate_substituent_atoms_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.source_specific_expansion_graphs_wellFormed
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.source_specific_compound_variants_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.source_specific_candidates_have_no_generic_atoms
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.unresolved_source_specific_authority_inputs_empty
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.certified_source_specific_authority_input_count
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.every_source_specific_authority_input_structurally_wellFormed
