import TetraStereo.OneCenter.Retinoid1981SourceAuditLedger
import TetraStereo.OneCenter.Retinoid1981SourceSpecificAuthorityInput
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter
namespace Retinoid1981
namespace StereoparentTableAuthorityInput

open FigureGraphTranscription
open FigureAuthorityInput
open SourceAudit.Ledger

private def tableCarbon (atomId : Nat) : AtomNode :=
  ⟨atomId, .carbon⟩

private def tableNitrogen (atomId : Nat) : AtomNode :=
  ⟨atomId, .nitrogen⟩

private def tableOxygen (atomId : Nat) : AtomNode :=
  ⟨atomId, .oxygen⟩

/-! ## Terminal-group graph implementations -/

/-- Structure (2), `R=CHO`: retinal. -/
def retinalGraph : HeavyAtomGraph :=
  compileEdits stereoparentSkeletonGraph
    [ .addNode (tableOxygen 21)
    , .addBond ⟨15, 21, .double⟩ ]

/-- Structure (3), `R=CO2H`: retinoic acid. This is defined under its Ret-2 identity rather
than reusing the topology-equivalent 13-cis example from A52a. -/
def retinoicAcidGraph : HeavyAtomGraph :=
  compileEdits stereoparentSkeletonGraph
    [ .addNode (tableOxygen 21)
    , .addNode (tableOxygen 22)
    , .addBond ⟨15, 21, .double⟩
    , .addBond ⟨15, 22, .single⟩ ]

/-- Structure (5), `R=CH2OCOCH3`: retinyl acetate. -/
def retinylAcetateGraph : HeavyAtomGraph :=
  compileEdits stereoparentSkeletonGraph
    [ .addNode (tableOxygen 21)
    , .addNode (tableCarbon 22)
    , .addNode (tableOxygen 23)
    , .addNode (tableCarbon 24)
    , .addBond ⟨15, 21, .single⟩
    , .addBond ⟨21, 22, .single⟩
    , .addBond ⟨22, 23, .double⟩
    , .addBond ⟨22, 24, .single⟩ ]

/-- Structure (6), `R=CH2NH2`: retinylamine. -/
def retinylamineGraph : HeavyAtomGraph :=
  compileEdits stereoparentSkeletonGraph
    [ .addNode (tableNitrogen 21)
    , .addBond ⟨15, 21, .single⟩ ]

/-- Structure (7), `R=CH=NOH`: retinal oxime. -/
def retinalOximeGraph : HeavyAtomGraph :=
  compileEdits stereoparentSkeletonGraph
    [ .addNode (tableNitrogen 21)
    , .addNode (tableOxygen 22)
    , .addBond ⟨15, 21, .double⟩
    , .addBond ⟨21, 22, .single⟩ ]

/-- Structure (8), `R=CH=N[CH2]4CHNH2CO2H`: N6-retinylidene-L-lysine.
Nodes 22--25 are the four methylene carbons, node 26 is the alpha carbon, node 27 the alpha
nitrogen, and nodes 28--30 the carboxyl group. The L-center geometry is outside this
constitutional graph and remains a separate stereochemical-fidelity obligation. -/
def lysylIminomethylGraph : HeavyAtomGraph :=
  compileEdits stereoparentSkeletonGraph
    [ .addNode (tableNitrogen 21)
    , .addNode (tableCarbon 22)
    , .addNode (tableCarbon 23)
    , .addNode (tableCarbon 24)
    , .addNode (tableCarbon 25)
    , .addNode (tableCarbon 26)
    , .addNode (tableNitrogen 27)
    , .addNode (tableCarbon 28)
    , .addNode (tableOxygen 29)
    , .addNode (tableOxygen 30)
    , .addBond ⟨15, 21, .double⟩
    , .addBond ⟨21, 22, .single⟩
    , .addBond ⟨22, 23, .single⟩
    , .addBond ⟨23, 24, .single⟩
    , .addBond ⟨24, 25, .single⟩
    , .addBond ⟨25, 26, .single⟩
    , .addBond ⟨26, 27, .single⟩
    , .addBond ⟨26, 28, .single⟩
    , .addBond ⟨28, 29, .double⟩
    , .addBond ⟨28, 30, .single⟩ ]

/-- Structure (9), `R=CO2C2H5`: ethyl retinoate. -/
def ethylRetinoateGraph : HeavyAtomGraph :=
  compileEdits stereoparentSkeletonGraph
    [ .addNode (tableOxygen 21)
    , .addNode (tableOxygen 22)
    , .addNode (tableCarbon 23)
    , .addNode (tableCarbon 24)
    , .addBond ⟨15, 21, .double⟩
    , .addBond ⟨15, 22, .single⟩
    , .addBond ⟨22, 23, .single⟩
    , .addBond ⟨23, 24, .single⟩ ]

/-- Total compiler for the ten Ret-2 terminal groups. Existing figure graphs are reused where
they already express the exact constitutional topology. -/
def graphForTerminalGroup : TerminalGroup → HeavyAtomGraph
  | .hydroxymethyl => retinolGraph
  | .formyl => retinalGraph
  | .carboxyl => retinoicAcidGraph
  | .methyl => stereoparentSkeletonGraph
  | .acetoxymethyl => retinylAcetateGraph
  | .aminomethyl => retinylamineGraph
  | .hydroxyiminomethyl => retinalOximeGraph
  | .lysylIminomethyl => lysylIminomethylGraph
  | .ethoxycarbonyl => ethylRetinoateGraph
  | .betaDGlucopyranuronateEster => retinoylGlucuronideGraph

structure StereoparentTableGraphEntry where
  row : StereoparentSubstituentRow
  graph : HeavyAtomGraph
  deriving DecidableEq, Repr

/-- Exact source-order graph batch derived from the frozen ten-row ledger. -/
def stereoparentTableGraphEntries : List StereoparentTableGraphEntry :=
  stereoparentSubstituentRows.map fun row =>
    ⟨row, graphForTerminalGroup row.terminalGroup⟩

@[simp] theorem stereoparent_table_graph_entry_count :
    stereoparentTableGraphEntries.length = 10 := by
  decide

@[simp] theorem stereoparent_table_structure_numbers_exact :
    stereoparentTableGraphEntries.map (fun entry => entry.row.structureNumber) =
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  decide

@[simp] theorem stereoparent_table_terminal_groups_exact :
    stereoparentTableGraphEntries.map (fun entry => entry.row.terminalGroup) =
      TerminalGroup.all := by
  decide

def stereoparentTableGraphCounts : List (Nat × Nat) :=
  stereoparentTableGraphEntries.map fun entry =>
    (entry.graph.nodes.length, entry.graph.bonds.length)

@[simp] theorem stereoparent_table_graph_counts_exact :
    stereoparentTableGraphCounts =
      [ (21, 21), (21, 21), (22, 22), (20, 20), (24, 24)
      , (21, 21), (22, 22), (30, 30), (24, 24), (34, 35) ] := by
  decide

def lysylIminomethylAddedAtoms : List (Nat × AtomElement) :=
  (lysylIminomethylGraph.nodes.drop 20).map fun node =>
    (node.locant, node.element)

@[simp] theorem lysyl_iminomethyl_added_atoms_exact :
    lysylIminomethylAddedAtoms =
      [ (21, .nitrogen)
      , (22, .carbon)
      , (23, .carbon)
      , (24, .carbon)
      , (25, .carbon)
      , (26, .carbon)
      , (27, .nitrogen)
      , (28, .carbon)
      , (29, .oxygen)
      , (30, .oxygen) ] := by
  decide

@[simp] theorem stereoparent_table_graphs_have_no_generic_atoms :
    stereoparentTableGraphEntries.all
      (fun entry => entry.graph.nodes.all
        (fun node => node.element != .genericSubstituent)) = true := by
  decide

theorem stereoparent_table_graphs_all_wellFormed :
    stereoparentTableGraphEntries.Forall
      (fun entry => entry.graph.WellFormed) := by
  have retinol : retinolGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have retinal : retinalGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have retinoicAcid : retinoicAcidGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have deoxyretinol : stereoparentSkeletonGraph.WellFormed :=
    stereoparentSkeleton_wellFormed
  have retinylAcetate : retinylAcetateGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have retinylamine : retinylamineGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have retinalOxime : retinalOximeGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have lysyl : lysylIminomethylGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have ethylRetinoate : ethylRetinoateGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have glucuronide : retinoylGlucuronideGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  simpa [stereoparentTableGraphEntries, stereoparentSubstituentRows,
    graphForTerminalGroup] using
      And.intro retinol
        (And.intro retinal
          (And.intro retinoicAcid
            (And.intro deoxyretinol
              (And.intro retinylAcetate
                (And.intro retinylamine
                  (And.intro retinalOxime
                    (And.intro lysyl
                      (And.intro ethylRetinoate glucuronide))))))))

/-! ## Structural authority-input certification -/

structure CertifiedStereoparentTableAuthorityInput where
  candidate : StereoparentTableGraphEntry
  certified : CertifiedAuthoritativeChemicalInput
  atomCountExact :
    certified.input.molecule.atoms.length = candidate.graph.nodes.length
  interactionCountExact :
    certified.input.molecule.interactions.length = candidate.graph.bonds.length

def StereoparentTableGraphEntry.certify?
    (candidate : StereoparentTableGraphEntry) :
    Option CertifiedStereoparentTableAuthorityInput := do
  let input ← heavyAtomGraphToAuthoritativeChemicalInput? candidate.graph
  let certified ← input.certify?
  if atomCountExact :
      certified.input.molecule.atoms.length = candidate.graph.nodes.length then
    if interactionCountExact :
        certified.input.molecule.interactions.length = candidate.graph.bonds.length then
      some
        { candidate := candidate
          certified := certified
          atomCountExact := atomCountExact
          interactionCountExact := interactionCountExact }
    else none
  else none

def certifiedStereoparentTableAuthorityInputs :
    List CertifiedStereoparentTableAuthorityInput :=
  stereoparentTableGraphEntries.filterMap StereoparentTableGraphEntry.certify?

def unresolvedStereoparentTableAuthorityInputs :
    List StereoparentTableGraphEntry :=
  stereoparentTableGraphEntries.filter fun candidate =>
    candidate.certify?.isNone

@[simp] theorem certified_stereoparent_table_authority_input_count :
    certifiedStereoparentTableAuthorityInputs.length = 10 := by
  decide

@[simp] theorem unresolved_stereoparent_table_authority_inputs_empty :
    unresolvedStereoparentTableAuthorityInputs = [] := by
  decide

theorem every_stereoparent_table_authority_input_structurally_wellFormed
    (entry : CertifiedStereoparentTableAuthorityInput) :
    entry.certified.input.StructurallyWellFormed :=
  entry.certified.structurallyWellFormed

end StereoparentTableAuthorityInput
end Retinoid1981
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTableAuthorityInput.stereoparent_table_structure_numbers_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTableAuthorityInput.stereoparent_table_terminal_groups_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTableAuthorityInput.stereoparent_table_graph_counts_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTableAuthorityInput.lysyl_iminomethyl_added_atoms_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTableAuthorityInput.stereoparent_table_graphs_have_no_generic_atoms
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTableAuthorityInput.stereoparent_table_graphs_all_wellFormed
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTableAuthorityInput.certified_stereoparent_table_authority_input_count
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTableAuthorityInput.unresolved_stereoparent_table_authority_inputs_empty
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTableAuthorityInput.every_stereoparent_table_authority_input_structurally_wellFormed
