import TetraStereo.OneCenter.CIPP93NoncarbonTetrahedralNormalization
import TetraStereo.OneCenter.CIPP93TrigonalPyramidalIntegration
import TetraStereo.OneCenter.CIPAuthoritativeBranchComparator
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace TetraStereo.OneCenter
namespace BlueBookP93.ChalcogenOxoPublicFidelity

open BlueBookP93.NoncarbonTetrahedra.Production

/-!
# P-93.2 chalcogen oxo public fidelity (successor)

P-93.2.4 (Blue Book 2013, frozen P-9 artifact) directs that a conventionally written `P=O`
bond in phosphates, phosphonates, and related compounds is one ligand edge and that alternative
formal-charge placement is ignored.  P-93.2.5 directs that sulfates, sulfonates, and related
anions are treated in the same way as phosphate anions; the frozen production family
`ChalcogenOxoFamily` includes `selenate`, `selenonate`, `tellurate`, and `telluronate`, and the
authority carrier's `UsesPhosphateConfigurationTreatment` is the P-93.2.5 transfer of the
P-93.2.4 treatment.

Two implementation facts were at issue for a four-neighbour Se or Te centre.

* `CIPP93NoncarbonTetrahedralNormalization.oxoCenterElement` includes `Se` and `Te`, so the
  executable P-93.2 quotient lowers every Se/Te oxo edge to a single edge.
* `BranchSphereKey.isTrigonalPyramidalOxidoRootEdge` is restricted to `P` and `S`, so the ordinary
  `analyzeSmiles` pipeline does not suppress a written `Se=O`/`Te=O` root multiple bond.

The predecessor production order applied the P-93.2 quotient before implicit-hydrogen completion.
For a literal unbracketed oxo oxygen (`=O`) that left the oxygen with bond-order sum one, so
`withExplicitHydrogens` filled it to oxygen's standard valence two and created one hydrogen that
did not exist in the written molecule.  The bracket spelling `[O]` carries the exact policy
`some 0` and had no such artifact.

The production normalizer has since been repaired: `normalizeRawMoleculeP93` now freezes each
source atom's written OpenSMILES hydrogen count before the P-93.2 quotient (equivalently,
hydrogen completion is fixed from the source graph, and the quotient then cannot protonate an oxo
oxygen).  **This successor module is written against that repaired production definition.**  On
the repaired public path the literal Se and Te candidates are refused as non-stereogenic: with no
spurious hydrogen the two `16O` ligands are constitutionally identical, which is exactly what the
predecessor module had proved only for its local candidate fidelity path.

The predecessor order is retained here only under explicit `legacy` names
(`legacyNormalize`, `legacyResult`, `legacyCertified?`, `analyzeSmilesP93Legacy`) and the theorems
about it carry a `legacy` marker.  Those theorems record what the predecessor production actually
returned; they are historical observations and are never labelled as the current public path.

Everything below is executable and kernel checked.  The principal concrete fixtures are the
literal Se and Te spellings, the bracket-oxygen controls, and the exact public assignment lists
(not merely `isOk`).

The exact public assignment lists are proved through the factored intermediate snapshots at the
end of this file.  Each parse, certification, descriptor-state, analyzer-segment, and entry-point
stage is an exact equality with its own `decide` proof; the public list theorems rewrite through
those stages instead of forcing one monolithic reduction of the whole analyzer.
-/

/-! ## Sources -/


def seOxoSource : String := "[Se@](=O)(=[18O])([O-])(C)"

/-- Tellurium analogue of `seOxoSource`. -/
def teOxoSource : String := "[Te@](=O)(=[18O])([O-])(C)"

/-- The same Se candidate with every oxygen written as a bracket atom. -/
def seOxoBracketSource : String := "[Se@](=[O])(=[18O])([O-])(C)"

/-- Tellurium analogue of `seOxoBracketSource`. -/
def teOxoBracketSource : String := "[Te@](=[O])(=[18O])([O-])(C)"

/-! ## Executable ingestion: the actual public P-93.2 path

After the fidelity repair, `normalizeRawMoleculeP93` consumes the source graph with its written
hydrogen policy frozen, applies the P-93.2 effective-graph quotient, and then runs the ordinary
chemistry normalizer.  The definitions below therefore delegate directly to production; no local
model of the order is used for the public path. -/

/-- Parsed molecule, if the source is accepted. -/
abbrev parsedSource (source : String) : Option RawMolecule :=
  (parseOpenSMILES source).toOption

/-- Exact parse state of a source.  The explicit fallback is used only in the unreachable
parse-error branch of `parse_eq_ok_snapshot`. -/
abbrev parsedSnapshot (source : String) : RawMolecule :=
  (parseOpenSMILES source).toOption.getD { atoms := [], bonds := [] }

/-- Production P-93.2 normalization snapshot of a source, exactly the normalization consumed by
`analyzeSmilesP93`.  This successor module is written against the repaired production definition,
which freezes written source hydrogen counts before the effective-graph quotient. -/
abbrev p93ResultOf (source : String) : ChemistryNormalizationResult :=
  normalizeRawMoleculeP93 (parsedSnapshot source)

/-- The actual public P-93.2 normalization result of a source, when it parses. -/
abbrev p93Result (source : String) : Option ChemistryNormalizationResult :=
  (parsedSource source).map fun mol => normalizeRawMoleculeP93 mol

/-- The expanded graph of the actual public P-93.2 path, i.e. exactly the graph the analyzer
ranks. -/
abbrev p93Expanded (source : String) : Option RawMolecule :=
  (p93Result source).map fun result => result.parsed.withExplicitHydrogens

/-- Plain production normalization followed by hydrogen materialization, i.e. the ordinary
(non-P-93.2) `analyzeSmiles` path. -/
abbrev plainExpanded (source : String) : Option RawMolecule :=
  (parsedSource source).map fun mol =>
    (normalizeRawMolecule mol).parsed.withExplicitHydrogens

/-! ## The predecessor order, retained explicitly as legacy

The definitions in this section reproduce the predecessor production order: apply the P-93.2
quotient to the written graph first, without freezing the source hydrogen policy, and only then
complete hydrogens.  They exist solely so that the predecessor observations can be stated
honestly under explicit `legacy` names.  They are not the public path. -/

/-- Predecessor P-93.2 order: the effective-graph quotient applied to the source graph, without a
source-hydrogen freeze. -/
def legacyNormalize (mol : RawMolecule) : RawMolecule :=
  normalize mol

/-- Normalization result of the predecessor order. -/
def legacyResult (mol : RawMolecule) : ChemistryNormalizationResult :=
  normalizeRawMolecule (legacyNormalize mol)

/-- Executable certification of the predecessor order. -/
def legacyCertified? (mol : RawMolecule) : Option CertifiedChemistryNormalizationResult :=
  (legacyResult mol).certify?

/-- Predecessor normalization result of a source, when it parses. -/
abbrev legacyResult? (source : String) : Option ChemistryNormalizationResult :=
  (parsedSource source).map legacyResult

/-- Predecessor normalization snapshot of a source. -/
abbrev legacyResultOf (source : String) : ChemistryNormalizationResult :=
  legacyResult (parsedSnapshot source)

/-- Expanded graph of the predecessor order. -/
abbrev legacyExpanded (source : String) : Option RawMolecule :=
  (parsedSource source).map fun mol => (legacyResult mol).parsed.withExplicitHydrogens

/-- Predecessor public-shaped entry point.  It mirrors the current `analyzeSmilesP93` exactly but
consumes the explicitly named predecessor order.  It is retained only to state what the
predecessor production actually returned; it is not an authority-facing entry point. -/
def analyzeSmilesP93Legacy (input : String) : Except ParserError (List StereoAssignment) := do
  let mol ← parseOpenSMILES input
  match legacyCertified? mol with
  | none =>
      Except.error
        "legacy-P-93-normalized molecule failed structural, valence, or Rule-2 mass admission"
  | some certified =>
      if !certified.result.expandedStereochemicalAdmissible? then
        Except.error "hydrogen-expanded legacy P-93 molecule failed stereochemical admission"
      else
        Except.ok (analyzeNormalized certified.result)

/-! ## Source admission and the oxo-centre boundary -/

theorem seOxoSource_parses : (parseOpenSMILES seOxoSource).isOk = true := by decide

theorem teOxoSource_parses : (parseOpenSMILES teOxoSource).isOk = true := by decide

theorem seOxoBracketSource_parses :
    (parseOpenSMILES seOxoBracketSource).isOk = true := by decide

theorem teOxoBracketSource_parses :
    (parseOpenSMILES teOxoBracketSource).isOk = true := by decide

/-- The literal Se input passes every admission predicate used by the public entry points. -/
theorem seOxoSource_admitted :
    (parsedSource seOxoSource).map (fun mol =>
      (mol.admissible?, mol.writtenNeighborExact?, mol.valenceOK?,
       mol.rule2MassesKnown?, mol.introductionPredecessorsValid?)) =
    some (true, true, true, true, true) := by decide

/-- The literal Te input passes every admission predicate used by the public entry points. -/
theorem teOxoSource_admitted :
    (parsedSource teOxoSource).map (fun mol =>
      (mol.admissible?, mol.writtenNeighborExact?, mol.valenceOK?,
       mol.rule2MassesKnown?, mol.introductionPredecessorsValid?)) =
    some (true, true, true, true, true) := by decide

/-- The bracket-oxo Se control is admitted as well. -/
theorem seOxoBracketSource_admitted :
    (parsedSource seOxoBracketSource).map (fun mol =>
      (mol.admissible?, mol.writtenNeighborExact?, mol.valenceOK?,
       mol.rule2MassesKnown?, mol.introductionPredecessorsValid?)) =
    some (true, true, true, true, true) := by decide

/-- The bracket-oxo Te control is admitted as well. -/
theorem teOxoBracketSource_admitted :
    (parsedSource teOxoBracketSource).map (fun mol =>
      (mol.admissible?, mol.writtenNeighborExact?, mol.valenceOK?,
       mol.rule2MassesKnown?, mol.introductionPredecessorsValid?)) =
    some (true, true, true, true, true) := by decide

/-- The concrete P-93.2 graph-vs-classifier boundary of one chalcogen centre. -/
structure ChalcogenOxoBoundary where
  effectiveCenter : Bool
  writtenNeighborCount : Nat
  firstOxoBond : Bool
  secondOxoBond : Bool
  thirdOxoBond : Bool
  firstRootEdge : Bool
  secondRootEdge : Bool
  thirdRootEdge : Bool
  deriving DecidableEq, Repr

/-- The boundary observed at centre `0` for the fixtures below. -/
def chalcogenOxoBoundary (mol : RawMolecule) : ChalcogenOxoBoundary where
  effectiveCenter := effectiveOxoCenter? mol 0
  writtenNeighborCount := (mol.writtenNeighbors 0).length
  firstOxoBond := effectiveOxoBond? mol { source := 0, target := 1, kind := .double }
  secondOxoBond := effectiveOxoBond? mol { source := 0, target := 2, kind := .double }
  thirdOxoBond := effectiveOxoBond? mol { source := 0, target := 3, kind := .single }
  firstRootEdge := mol.isTrigonalPyramidalOxidoRootEdge 0 1
  secondRootEdge := mol.isTrigonalPyramidalOxidoRootEdge 0 2
  thirdRootEdge := mol.isTrigonalPyramidalOxidoRootEdge 0 3

/-- Concrete Se boundary: four written neighbours, an effective oxo centre, all three Se-O edges
effective oxo edges, and no production P/S root suppression. -/
theorem seOxoSource_boundary :
    (parsedSource seOxoSource).map chalcogenOxoBoundary =
    some ⟨true, 4, true, true, true, false, false, false⟩ := by decide

/-- Concrete Te boundary, identical to Se. -/
theorem teOxoSource_boundary :
    (parsedSource teOxoSource).map chalcogenOxoBoundary =
    some ⟨true, 4, true, true, true, false, false, false⟩ := by decide

/-- The bracket-oxo Se control has the same effective-oxo boundary and the same missing root
suppression, so it isolates the hydrogen artifact from the classifier gap. -/
theorem seOxoBracketSource_boundary :
    (parsedSource seOxoBracketSource).map chalcogenOxoBoundary =
    some ⟨true, 4, true, true, true, false, false, false⟩ := by decide

/-- The bracket-oxo Te control has the same boundary as the Se control. -/
theorem teOxoBracketSource_boundary :
    (parsedSource teOxoBracketSource).map chalcogenOxoBoundary =
    some ⟨true, 4, true, true, true, false, false, false⟩ := by decide

/-- The production root-edge classifier can only return `true` for a P or S centre.  This is a
statement about the ordinary (non-P-93.2) path, where no quotient has lowered the Se/Te oxo bond
to a single edge first. -/
theorem isTrigonalPyramidalOxidoRootEdge_eq_false_of_centerElement_ne_P_ne_S
    (mol : RawMolecule) (center oxygen : Nat) (spec : AtomSpec)
    (observed : mol.atomAt? center = some spec)
    (notP : spec.element ≠ .P) (notS : spec.element ≠ .S) :
    mol.isTrigonalPyramidalOxidoRootEdge center oxygen = false := by
  unfold RawMolecule.isTrigonalPyramidalOxidoRootEdge
  rw [observed]
  cases oxygenLookup : mol.atomAt? oxygen with
  | none => simp
  | some oxygenSpec =>
      simp [beq_iff_eq, notP, notS]

/-! ## Exact written hydrogen counts

Indices: `0` is the chalcogen centre, `1` the unbracketed oxo oxygen, `2` the `18O` oxygen,
`3` the `[O-]` oxygen, and `4` the unbracketed carbon ligand. -/

/-- Written hydrogen counts of the literal Se input: the oxo oxygen has none, the carbon has
three. -/
theorem seOxoSource_writtenHydrogenCounts :
    (parsedSource seOxoSource).map (fun mol =>
      (List.range mol.atomCount).map mol.hydrogenCountAt) =
    some [0, 0, 0, 0, 3] := by decide

/-- Written hydrogen counts of the literal Te input. -/
theorem teOxoSource_writtenHydrogenCounts :
    (parsedSource teOxoSource).map (fun mol =>
      (List.range mol.atomCount).map mol.hydrogenCountAt) =
    some [0, 0, 0, 0, 3] := by decide

/-- Written hydrogen counts of the bracket-oxo Se control. -/
theorem seOxoBracketSource_writtenHydrogenCounts :
    (parsedSource seOxoBracketSource).map (fun mol =>
      (List.range mol.atomCount).map mol.hydrogenCountAt) =
    some [0, 0, 0, 0, 3] := by decide

/-! ## Actual public P-93.2 path: no spurious hydrogen

With the source-hydrogen freeze in front of the quotient, lowering the `Se=O`/`Te=O` edge cannot
create an implicit hydrogen on the originally unprotonated oxo oxygen. -/

/-- The actual public P-93.2 result keeps the written count vector for the literal Se input. -/
theorem seOxoSource_p93Result_hydrogenCounts :
    (p93Result seOxoSource).map (fun result =>
      (List.range result.parsed.atomCount).map result.parsed.hydrogenCountAt) =
    some [0, 0, 0, 0, 3] := by decide

/-- Tellurium analogue of the repaired count witness. -/
theorem teOxoSource_p93Result_hydrogenCounts :
    (p93Result teOxoSource).map (fun result =>
      (List.range result.parsed.atomCount).map result.parsed.hydrogenCountAt) =
    some [0, 0, 0, 0, 3] := by decide

/-- The bracket control keeps the written count vector through the same public quotient. -/
theorem seOxoBracketSource_p93Result_hydrogenCounts :
    (p93Result seOxoBracketSource).map (fun result =>
      (List.range result.parsed.atomCount).map result.parsed.hydrogenCountAt) =
    some [0, 0, 0, 0, 3] := by decide

/-- Tellurium bracket control analogue. -/
theorem teOxoBracketSource_p93Result_hydrogenCounts :
    (p93Result teOxoBracketSource).map (fun result =>
      (List.range result.parsed.atomCount).map result.parsed.hydrogenCountAt) =
    some [0, 0, 0, 0, 3] := by decide

/-- Actual Se expanded graph: 8 atoms, only the carbon's three hydrogens are materialized, and
the oxo oxygen (index 1) remains hydrogen-free. -/
theorem seOxoSource_p93_expandedGraph :
    (p93Expanded seOxoSource).map (fun mol =>
      (mol.atomCount, mol.writtenNeighbors 1, mol.writtenNeighbors 2,
       mol.writtenNeighbors 3, mol.writtenNeighbors 4)) =
    some (8, [0], [0], [0], [0, 5, 6, 7]) := by decide

/-- Actual Te expanded graph: same repaired shape. -/
theorem teOxoSource_p93_expandedGraph :
    (p93Expanded teOxoSource).map (fun mol =>
      (mol.atomCount, mol.writtenNeighbors 1, mol.writtenNeighbors 2,
       mol.writtenNeighbors 3, mol.writtenNeighbors 4)) =
    some (8, [0], [0], [0], [0, 5, 6, 7]) := by decide

/-- The bracket-oxo Se control has no hydrogen on any oxygen in the repaired expanded graph. -/
theorem seOxoBracketSource_p93_expandedGraph :
    (p93Expanded seOxoBracketSource).map (fun mol =>
      (mol.atomCount, mol.writtenNeighbors 1, mol.writtenNeighbors 2,
       mol.writtenNeighbors 3)) =
    some (8, [0], [0], [0]) := by decide

/-- The bracket-oxo Te control has no hydrogen on any oxygen in the repaired expanded graph. -/
theorem teOxoBracketSource_p93_expandedGraph :
    (p93Expanded teOxoBracketSource).map (fun mol =>
      (mol.atomCount, mol.writtenNeighbors 1, mol.writtenNeighbors 2,
       mol.writtenNeighbors 3)) =
    some (8, [0], [0], [0]) := by decide

/-! ## Actual public P-93.2 path: branch comparisons and outcomes -/

/-- Actual Se branch comparison: with no spurious hydrogen, the two `16O` ligands tie exactly and
the `18O` ligand outranks each by Rule 2. -/
theorem seOxoSource_p93_branchStatus :
    (p93Expanded seOxoSource).map (fun mol =>
      (mol.compareBranchesAuthoritativeStatus 0 1 2,
       mol.compareBranchesAuthoritativeStatus 0 1 3,
       mol.compareBranchesAuthoritativeStatus 0 2 3)) =
    some (.lower, .tied, .higher) := by decide

/-- Tellurium analogue of the repaired branch comparison. -/
theorem teOxoSource_p93_branchStatus :
    (p93Expanded teOxoSource).map (fun mol =>
      (mol.compareBranchesAuthoritativeStatus 0 1 2,
       mol.compareBranchesAuthoritativeStatus 0 1 3,
       mol.compareBranchesAuthoritativeStatus 0 2 3)) =
    some (.lower, .tied, .higher) := by decide

/-- The bracket-oxo Se control through the actual public P-93.2 order. -/
theorem seOxoBracketSource_p93_branchStatus :
    (p93Expanded seOxoBracketSource).map (fun mol =>
      (mol.compareBranchesAuthoritativeStatus 0 1 2,
       mol.compareBranchesAuthoritativeStatus 0 1 3,
       mol.compareBranchesAuthoritativeStatus 0 2 3)) =
    some (.lower, .tied, .higher) := by decide

/-- The bracket-oxo Te control through the actual public P-93.2 order. -/
theorem teOxoBracketSource_p93_branchStatus :
    (p93Expanded teOxoBracketSource).map (fun mol =>
      (mol.compareBranchesAuthoritativeStatus 0 1 2,
       mol.compareBranchesAuthoritativeStatus 0 1 3,
       mol.compareBranchesAuthoritativeStatus 0 2 3)) =
    some (.lower, .tied, .higher) := by decide

/-- Actual Se outcome: the two `16O` ligands are constitutionally identical, so the centre is
refused as non-stereogenic. -/
theorem seOxoSource_p93_tetrahedralOutcome :
    (p93Expanded seOxoSource).map (fun mol =>
      mol.tetrahedralOutcome (analysisFuel mol) 0) =
    some (.refused .notStereogenic) := by decide

/-- Tellurium analogue of the repaired outcome. -/
theorem teOxoSource_p93_tetrahedralOutcome :
    (p93Expanded teOxoSource).map (fun mol =>
      mol.tetrahedralOutcome (analysisFuel mol) 0) =
    some (.refused .notStereogenic) := by decide

/-- The bracket control through the actual public P-93.2 order is correctly refused. -/
theorem seOxoBracketSource_p93_tetrahedralOutcome :
    (p93Expanded seOxoBracketSource).map (fun mol =>
      mol.tetrahedralOutcome (analysisFuel mol) 0) =
    some (.refused .notStereogenic) := by decide

/-- Tellurium bracket control analogue. -/
theorem teOxoBracketSource_p93_tetrahedralOutcome :
    (p93Expanded teOxoBracketSource).map (fun mol =>
      mol.tetrahedralOutcome (analysisFuel mol) 0) =
    some (.refused .notStereogenic) := by decide

/-! ## Legacy predecessor path: the spurious hydrogen

These theorems describe what the predecessor production returned.  They are marked `legacy` and
must not be read as statements about the current public entry point. -/

/-- Predecessor Se counts: one hydrogen is created on the originally unprotonated oxo oxygen
(index 1), giving the vector `[0, 1, 0, 0, 3]`. -/
theorem seOxoSource_legacyResult_hydrogenCounts :
    (legacyResult? seOxoSource).map (fun result =>
      (List.range result.parsed.atomCount).map result.parsed.hydrogenCountAt) =
    some [0, 1, 0, 0, 3] := by decide

/-- Predecessor Te counts exhibit the same artifact. -/
theorem teOxoSource_legacyResult_hydrogenCounts :
    (legacyResult? teOxoSource).map (fun result =>
      (List.range result.parsed.atomCount).map result.parsed.hydrogenCountAt) =
    some [0, 1, 0, 0, 3] := by decide

/-- The bracket control has no artifact even under the predecessor order. -/
theorem seOxoBracketSource_legacyResult_hydrogenCounts :
    (legacyResult? seOxoBracketSource).map (fun result =>
      (List.range result.parsed.atomCount).map result.parsed.hydrogenCountAt) =
    some [0, 0, 0, 0, 3] := by decide

/-- Predecessor Se expanded graph: 9 atoms and the former unbracketed oxo oxygen (index 1) has
gained generated hydrogen atom 5. -/
theorem seOxoSource_legacy_hydrogenArtifact :
    (legacyExpanded seOxoSource).map (fun mol =>
      (mol.atomCount, mol.writtenNeighbors 1, mol.writtenNeighbors 2,
       mol.writtenNeighbors 3, (mol.atomAt? 5).map AtomSpec.element)) =
    some (9, [0, 5], [0], [0], some .H) := by decide

/-- Predecessor Te analogue of the spurious-hydrogen witness. -/
theorem teOxoSource_legacy_hydrogenArtifact :
    (legacyExpanded teOxoSource).map (fun mol =>
      (mol.atomCount, mol.writtenNeighbors 1, mol.writtenNeighbors 2,
       mol.writtenNeighbors 3, (mol.atomAt? 5).map AtomSpec.element)) =
    some (9, [0, 5], [0], [0], some .H) := by decide

/-- The predecessor artifact is branch-visible: the generated hydrogen makes the unlabelled oxo
oxygen (now an OH) outrank the `18O` ligand at Rule 1a, and the `18O` ligand then outranks the
`[O-]`-derived oxygen. -/
theorem seOxoSource_legacy_branchStatus :
    (legacyExpanded seOxoSource).map (fun mol =>
      (mol.compareBranchesAuthoritativeStatus 0 1 2,
       mol.compareBranchesAuthoritativeStatus 0 1 3,
       mol.compareBranchesAuthoritativeStatus 0 2 3)) =
    some (.higher, .higher, .higher) := by decide

/-- The predecessor artifact is outcome-visible: the literal Se spelling was assigned `S`. -/
theorem seOxoSource_legacy_tetrahedralOutcome :
    (legacyExpanded seOxoSource).map (fun mol =>
      mol.tetrahedralOutcome (analysisFuel mol) 0) =
    some (.tetrahedral .S) := by decide

/-- Even with bracket oxygens the predecessor branch comparison beside the missing Se root
suppression still gives the same two-`16O` separation for the plain scan; under the legacy
P-93.2 quotient the oxo edge is single, so the bracket control ties as expected. -/
theorem seOxoBracketSource_legacy_branchStatus :
    (legacyExpanded seOxoBracketSource).map (fun mol =>
      (mol.compareBranchesAuthoritativeStatus 0 1 2,
       mol.compareBranchesAuthoritativeStatus 0 1 3,
       mol.compareBranchesAuthoritativeStatus 0 2 3)) =
    some (.lower, .tied, .higher) := by decide

/-! ## Ordinary (non-P-93.2) path witnesses

The ordinary `analyzeSmiles` pipeline does not insert the P-93.2 quotient, so the P/S-only
root-edge classifier still leaves the written Se oxo double bond in place.  These witnesses record
that separate, still-open classifier gap; they are not the repaired public path. -/

/-- Plain Se pipeline: 8 atoms, no hydrogen on any oxygen. -/
theorem seOxoSource_plain_expandedGraph :
    (plainExpanded seOxoSource).map (fun mol =>
      (mol.atomCount, mol.writtenNeighbors 1, mol.writtenNeighbors 2,
       mol.writtenNeighbors 3)) =
    some (8, [0], [0], [0]) := by decide

/-- Plain Se pipeline: the written double bond has two canonical occurrences, so the unlabelled
`Se=O` oxygen outranks the constitutionally identical `[O-]` oxygen; the two double-bond oxygens
tie under Rule 1 and are separated only by the Rule-2 isotope mass. -/
theorem seOxoSource_plain_branchStatus :
    (plainExpanded seOxoSource).map (fun mol =>
      (mol.compareBranchesAuthoritativeStatus 0 1 2,
       mol.compareBranchesAuthoritativeStatus 0 1 3,
       mol.compareBranchesAuthoritativeStatus 0 2 3)) =
    some (.lower, .higher, .higher) := by decide

/-- Plain Se pipeline emits `R` because the unsuppressed root duplicate separates the two
unlabelled `16O` ligands. -/
theorem seOxoSource_plain_tetrahedralOutcome :
    (plainExpanded seOxoSource).map (fun mol =>
      mol.tetrahedralOutcome (analysisFuel mol) 0) = some (.tetrahedral .R) := by decide

/-- Plain pipeline for the bracket control.  Root multiple-bond suppression is still absent, so
the unlabelled `Se=O` ligand outranks the identical `[O-]` ligand even with bracket oxygens. -/
theorem seOxoBracketSource_plain_branchStatus :
    (plainExpanded seOxoBracketSource).map (fun mol =>
      (mol.compareBranchesAuthoritativeStatus 0 1 2,
       mol.compareBranchesAuthoritativeStatus 0 1 3,
       mol.compareBranchesAuthoritativeStatus 0 2 3)) =
    some (.lower, .higher, .higher) := by decide

/-- The plain bracket control still emits `R`, isolating the ordinary-path root-duplicate gap
from the repaired P-93.2 hydrogen behavior. -/
theorem seOxoBracketSource_plain_tetrahedralOutcome :
    (plainExpanded seOxoBracketSource).map (fun mol =>
      mol.tetrahedralOutcome (analysisFuel mol) 0) = some (.tetrahedral .R) := by decide

/-! ## Public entry points: reachability -/

theorem seOxoSource_plainEntryPoint_reachable :
    (analyzeSmiles seOxoSource).isOk = true := by decide

theorem seOxoSource_p93EntryPoint_reachable :
    (analyzeSmilesP93 seOxoSource).isOk = true := by decide

theorem teOxoSource_p93EntryPoint_reachable :
    (analyzeSmilesP93 teOxoSource).isOk = true := by decide

theorem seOxoBracketSource_p93EntryPoint_reachable :
    (analyzeSmilesP93 seOxoBracketSource).isOk = true := by decide

theorem teOxoBracketSource_p93EntryPoint_reachable :
    (analyzeSmilesP93 teOxoBracketSource).isOk = true := by decide

/-! ## Factored exact computations

A monolithic `decide` on an entire `analyzeSmilesP93` call forces the molecule-wide descriptor
fixed point and all five analyzer segments at once; for this fixture family that reduction exceeds
the build memory budget.  The lemmas below expose every stage as its own exact equality:

* `parse_eq_ok_snapshot` — the exact parse state;
* `certify?_result_of_eq_some` and `certify?_exists_of_checks` — the exact certification step;
* `..._descriptorState` — the exact descriptor state reached by production discovery;
* `..._tetrahedralBranch` through `..._extendedBranch` — the five analyzer segments;
* `..._branchStructure` — the exact five-component record;
* `analyzeNormalized_eq_singleton` — assembly of the normalized analyzer;
* `analyzeSmilesP93_toOption_eq_singleton` and `analyzeSmilesP93Legacy_toOption_eq_singleton` —
  assembly of the actual public and explicit legacy entry points.

Each stage is decided independently, and the final theorems rewrite through the stages, so no
large reduction is repeated. -/

/-- A successful parse is exactly the snapshot. -/
theorem parse_eq_ok_snapshot (source : String)
    (parses : (parseOpenSMILES source).isOk = true) :
    parseOpenSMILES source = .ok (parsedSnapshot source) := by
  cases observed : parseOpenSMILES source with
  | ok mol =>
      simp [parsedSnapshot, observed, Except.toOption, Option.getD_some]
  | error message =>
      have bad : false = true := by
        simpa only [observed, Except.isOk] using parses
      cases bad

/-- The result component of any certified normalization result is the normalization result that
was checked. -/
theorem certify?_result_of_eq_some (result : ChemistryNormalizationResult)
    (certified : CertifiedChemistryNormalizationResult)
    (observed : result.certify? = some certified) : certified.result = result := by
  unfold ChemistryNormalizationResult.certify? at observed
  split at observed
  · split at observed
    · split at observed
      · split at observed
        · split at observed
          · cases observed
            rfl
          · simp at observed
        · simp at observed
      · simp at observed
    · simp at observed
  · simp at observed

/-- Exact certification from the five executable admission facts. -/
theorem certify?_exists_of_checks (result : ChemistryNormalizationResult)
    (introduction : result.parsed.introductionPredecessorsValid? = true)
    (admissible : result.parsed.admissible? = true)
    (neighbors : result.parsed.writtenNeighborExact? = true)
    (valence : result.parsed.valenceOK? = true)
    (masses : result.parsed.rule2MassesKnown? = true) :
    ∃ certified : CertifiedChemistryNormalizationResult,
      result.certify? = some certified ∧ certified.result = result := by
  cases observed : result.certify? with
  | none =>
      exfalso
      simp [ChemistryNormalizationResult.certify?, introduction, admissible, neighbors, valence,
        masses] at observed
  | some certified =>
      exact ⟨certified, rfl, certify?_result_of_eq_some result certified observed⟩

/-- Fieldwise extensionality for the five-segment analyzer record. -/
theorem normalizedStereoAnalysisBranches_ext
    {left right : NormalizedStereoAnalysisBranches}
    (tetrahedral : left.tetrahedral = right.tetrahedral)
    (ordinaryDoubleBond : left.ordinaryDoubleBond = right.ordinaryDoubleBond)
    (coupledDoubleBond : left.coupledDoubleBond = right.coupledDoubleBond)
    (oddCumuleneDoubleBond : left.oddCumuleneDoubleBond = right.oddCumuleneDoubleBond)
    (extendedAxial : left.extendedAxial = right.extendedAxial) : left = right := by
  cases left
  cases right
  simp_all

/-- Assembly of the normalized analyzer from its two molecule-wide guards and the exact five
segments. -/
theorem analyzeNormalized_eq_of_branches (result : ChemistryNormalizationResult)
    (segments : NormalizedStereoAnalysisBranches)
    (masses : result.parsed.rule2MassesKnown? = true)
    (admissible : result.expandedStereochemicalAdmissible? = true)
    (branches : normalizedStereoAnalysisBranches result = segments) :
    analyzeNormalized result =
      segments.tetrahedral ++ segments.ordinaryDoubleBond ++ segments.coupledDoubleBond ++
        segments.oddCumuleneDoubleBond ++ segments.extendedAxial := by
  unfold analyzeNormalized
  rw [masses, admissible, branches]
  rfl

/-- Singleton specialization of `analyzeNormalized_eq_of_branches`. -/
theorem analyzeNormalized_eq_singleton (result : ChemistryNormalizationResult)
    (assignment : StereoAssignment)
    (masses : result.parsed.rule2MassesKnown? = true)
    (admissible : result.expandedStereochemicalAdmissible? = true)
    (branches : normalizedStereoAnalysisBranches result =
      { tetrahedral := [assignment],
        ordinaryDoubleBond := [],
        coupledDoubleBond := [],
        oddCumuleneDoubleBond := [],
        extendedAxial := [] }) :
    analyzeNormalized result = [assignment] := by
  rw [analyzeNormalized_eq_of_branches result
    { tetrahedral := [assignment],
      ordinaryDoubleBond := [],
      coupledDoubleBond := [],
      oddCumuleneDoubleBond := [],
      extendedAxial := [] } masses admissible branches]
  rfl

/-- Public P-93.2 entry-point assembly from the exact parse, certification, and normalized
analysis stages. -/
theorem analyzeSmilesP93_toOption_eq_singleton
    (input : String) (mol : RawMolecule) (certified : CertifiedChemistryNormalizationResult)
    (assignment : StereoAssignment)
    (parsed : parseOpenSMILES input = .ok mol)
    (certifiedEq : normalizeRawMoleculeP93Certified? mol = some certified)
    (admissible : certified.result.expandedStereochemicalAdmissible? = true)
    (analyzed : analyzeNormalized certified.result = [assignment]) :
    (analyzeSmilesP93 input).toOption = some [assignment] := by
  have run : analyzeSmilesP93 input = .ok (analyzeNormalized certified.result) := by
    simp [analyzeSmilesP93, bind, Except.bind, parsed, certifiedEq,
      admissible]
  rw [run, analyzed]
  rfl

/-- Explicit legacy entry-point assembly from the exact parse, certification, and normalized
analysis stages.  This is the predecessor path, not the shipped `analyzeSmilesP93`. -/
theorem analyzeSmilesP93Legacy_toOption_eq_singleton
    (input : String) (mol : RawMolecule) (certified : CertifiedChemistryNormalizationResult)
    (assignment : StereoAssignment)
    (parsed : parseOpenSMILES input = .ok mol)
    (certifiedEq : legacyCertified? mol = some certified)
    (admissible : certified.result.expandedStereochemicalAdmissible? = true)
    (analyzed : analyzeNormalized certified.result = [assignment]) :
    (analyzeSmilesP93Legacy input).toOption = some [assignment] := by
  have run : analyzeSmilesP93Legacy input = .ok (analyzeNormalized certified.result) := by
    simp [analyzeSmilesP93Legacy, bind, Except.bind, parsed, certifiedEq, admissible]
  rw [run, analyzed]
  rfl

/-! ### Actual public path: literal selenium candidate

The actual public path is `normalizeRawMoleculeP93` after the source-hydrogen freeze repair, so
the literal spelling is refused as non-stereogenic. -/

abbrev seOxoP93Result : ChemistryNormalizationResult := p93ResultOf seOxoSource

def seOxoP93Assignment : StereoAssignment :=
  { unit := StereoUnit.tetrahedral 0,
    outcome := StereoOutcome.refused StereoRefusal.notStereogenic }

theorem seOxoSource_parse_eq :
    parseOpenSMILES seOxoSource = .ok (parsedSnapshot seOxoSource) :=
  parse_eq_ok_snapshot seOxoSource seOxoSource_parses

theorem seOxoP93_descriptorState :
    discoverRawDescriptors seOxoP93Result
        (seOxoP93Result.parsed.withExplicitHydrogens)
        (analysisFuel (seOxoP93Result.parsed.withExplicitHydrogens)) =
      initialRawDescriptorState seOxoP93Result
        (seOxoP93Result.parsed.withExplicitHydrogens)
        (analysisFuel (seOxoP93Result.parsed.withExplicitHydrogens)) := by
  decide +kernel

theorem seOxoP93_rule2MassesKnown :
    seOxoP93Result.parsed.rule2MassesKnown? = true := by
  decide +kernel

theorem seOxoP93_expandedStereochemicalAdmissible :
    seOxoP93Result.expandedStereochemicalAdmissible? = true := by
  decide +kernel

theorem seOxoP93_certifyChecks :
    seOxoP93Result.parsed.introductionPredecessorsValid? = true ∧
    seOxoP93Result.parsed.admissible? = true ∧
    seOxoP93Result.parsed.writtenNeighborExact? = true ∧
    seOxoP93Result.parsed.valenceOK? = true ∧
    seOxoP93Result.parsed.rule2MassesKnown? = true := by
  decide +kernel

theorem seOxoP93_certified?_exists :
    ∃ certified : CertifiedChemistryNormalizationResult,
      normalizeRawMoleculeP93Certified? (parsedSnapshot seOxoSource) = some certified ∧
        certified.result = seOxoP93Result := by
  rcases seOxoP93_certifyChecks with ⟨h1, h2, h3, h4, h5⟩
  rcases certify?_exists_of_checks seOxoP93Result h1 h2 h3 h4 h5 with
    ⟨certified, hcert, hresult⟩
  exact ⟨certified,
    by simpa [normalizeRawMoleculeP93Certified?, seOxoP93Result, p93ResultOf] using hcert,
    hresult⟩

theorem seOxoP93_tetrahedralBranch :
    (normalizedStereoAnalysisBranches seOxoP93Result).tetrahedral =
      [seOxoP93Assignment] := by
  rw [normalizedStereoAnalysisBranches_tetrahedral, seOxoP93_descriptorState]
  decide +kernel

theorem seOxoP93_ordinaryBranch :
    (normalizedStereoAnalysisBranches seOxoP93Result).ordinaryDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_ordinaryDoubleBond, seOxoP93_descriptorState]
  decide +kernel

theorem seOxoP93_coupledBranch :
    (normalizedStereoAnalysisBranches seOxoP93Result).coupledDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_coupledDoubleBond]
  dsimp only
  rw [seOxoP93_descriptorState]
  decide +kernel

theorem seOxoP93_oddBranch :
    (normalizedStereoAnalysisBranches seOxoP93Result).oddCumuleneDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_oddCumuleneDoubleBond]
  dsimp only
  rw [seOxoP93_descriptorState]
  decide +kernel

theorem seOxoP93_extendedBranch :
    (normalizedStereoAnalysisBranches seOxoP93Result).extendedAxial = [] := by
  rw [normalizedStereoAnalysisBranches_extendedAxial]
  dsimp only
  rw [seOxoP93_descriptorState]
  decide +kernel

theorem seOxoP93_branchStructure :
    normalizedStereoAnalysisBranches seOxoP93Result =
      { tetrahedral := [seOxoP93Assignment],
        ordinaryDoubleBond := [],
        coupledDoubleBond := [],
        oddCumuleneDoubleBond := [],
        extendedAxial := [] } := by
  refine normalizedStereoAnalysisBranches_ext ?_ ?_ ?_ ?_ ?_
  · simpa using seOxoP93_tetrahedralBranch
  · simpa using seOxoP93_ordinaryBranch
  · simpa using seOxoP93_coupledBranch
  · simpa using seOxoP93_oddBranch
  · simpa using seOxoP93_extendedBranch

theorem seOxoP93_analyzeNormalized :
    analyzeNormalized seOxoP93Result = [seOxoP93Assignment] :=
  analyzeNormalized_eq_singleton seOxoP93Result seOxoP93Assignment
    seOxoP93_rule2MassesKnown seOxoP93_expandedStereochemicalAdmissible
    seOxoP93_branchStructure

/-! ### Actual public path: literal tellurium candidate -/

abbrev teOxoP93Result : ChemistryNormalizationResult := p93ResultOf teOxoSource

def teOxoP93Assignment : StereoAssignment :=
  { unit := StereoUnit.tetrahedral 0,
    outcome := StereoOutcome.refused StereoRefusal.notStereogenic }

theorem teOxoSource_parse_eq :
    parseOpenSMILES teOxoSource = .ok (parsedSnapshot teOxoSource) :=
  parse_eq_ok_snapshot teOxoSource teOxoSource_parses

theorem teOxoP93_descriptorState :
    discoverRawDescriptors teOxoP93Result
        (teOxoP93Result.parsed.withExplicitHydrogens)
        (analysisFuel (teOxoP93Result.parsed.withExplicitHydrogens)) =
      initialRawDescriptorState teOxoP93Result
        (teOxoP93Result.parsed.withExplicitHydrogens)
        (analysisFuel (teOxoP93Result.parsed.withExplicitHydrogens)) := by
  decide +kernel

theorem teOxoP93_rule2MassesKnown :
    teOxoP93Result.parsed.rule2MassesKnown? = true := by
  decide +kernel

theorem teOxoP93_expandedStereochemicalAdmissible :
    teOxoP93Result.expandedStereochemicalAdmissible? = true := by
  decide +kernel

theorem teOxoP93_certifyChecks :
    teOxoP93Result.parsed.introductionPredecessorsValid? = true ∧
    teOxoP93Result.parsed.admissible? = true ∧
    teOxoP93Result.parsed.writtenNeighborExact? = true ∧
    teOxoP93Result.parsed.valenceOK? = true ∧
    teOxoP93Result.parsed.rule2MassesKnown? = true := by
  decide +kernel

theorem teOxoP93_certified?_exists :
    ∃ certified : CertifiedChemistryNormalizationResult,
      normalizeRawMoleculeP93Certified? (parsedSnapshot teOxoSource) = some certified ∧
        certified.result = teOxoP93Result := by
  rcases teOxoP93_certifyChecks with ⟨h1, h2, h3, h4, h5⟩
  rcases certify?_exists_of_checks teOxoP93Result h1 h2 h3 h4 h5 with
    ⟨certified, hcert, hresult⟩
  exact ⟨certified,
    by simpa [normalizeRawMoleculeP93Certified?, teOxoP93Result, p93ResultOf] using hcert,
    hresult⟩

theorem teOxoP93_tetrahedralBranch :
    (normalizedStereoAnalysisBranches teOxoP93Result).tetrahedral =
      [teOxoP93Assignment] := by
  rw [normalizedStereoAnalysisBranches_tetrahedral, teOxoP93_descriptorState]
  decide +kernel

theorem teOxoP93_ordinaryBranch :
    (normalizedStereoAnalysisBranches teOxoP93Result).ordinaryDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_ordinaryDoubleBond, teOxoP93_descriptorState]
  decide +kernel

theorem teOxoP93_coupledBranch :
    (normalizedStereoAnalysisBranches teOxoP93Result).coupledDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_coupledDoubleBond]
  dsimp only
  rw [teOxoP93_descriptorState]
  decide +kernel

theorem teOxoP93_oddBranch :
    (normalizedStereoAnalysisBranches teOxoP93Result).oddCumuleneDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_oddCumuleneDoubleBond]
  dsimp only
  rw [teOxoP93_descriptorState]
  decide +kernel

theorem teOxoP93_extendedBranch :
    (normalizedStereoAnalysisBranches teOxoP93Result).extendedAxial = [] := by
  rw [normalizedStereoAnalysisBranches_extendedAxial]
  dsimp only
  rw [teOxoP93_descriptorState]
  decide +kernel

theorem teOxoP93_branchStructure :
    normalizedStereoAnalysisBranches teOxoP93Result =
      { tetrahedral := [teOxoP93Assignment],
        ordinaryDoubleBond := [],
        coupledDoubleBond := [],
        oddCumuleneDoubleBond := [],
        extendedAxial := [] } := by
  refine normalizedStereoAnalysisBranches_ext ?_ ?_ ?_ ?_ ?_
  · simpa using teOxoP93_tetrahedralBranch
  · simpa using teOxoP93_ordinaryBranch
  · simpa using teOxoP93_coupledBranch
  · simpa using teOxoP93_oddBranch
  · simpa using teOxoP93_extendedBranch

theorem teOxoP93_analyzeNormalized :
    analyzeNormalized teOxoP93Result = [teOxoP93Assignment] :=
  analyzeNormalized_eq_singleton teOxoP93Result teOxoP93Assignment
    teOxoP93_rule2MassesKnown teOxoP93_expandedStereochemicalAdmissible
    teOxoP93_branchStructure

/-! ### Actual public path: bracket-oxo selenium control -/

abbrev seOxoBracketP93Result : ChemistryNormalizationResult := p93ResultOf seOxoBracketSource

def seOxoBracketP93Assignment : StereoAssignment :=
  { unit := StereoUnit.tetrahedral 0,
    outcome := StereoOutcome.refused StereoRefusal.notStereogenic }

theorem seOxoBracketSource_parse_eq :
    parseOpenSMILES seOxoBracketSource = .ok (parsedSnapshot seOxoBracketSource) :=
  parse_eq_ok_snapshot seOxoBracketSource seOxoBracketSource_parses

theorem seOxoBracketP93_descriptorState :
    discoverRawDescriptors seOxoBracketP93Result
        (seOxoBracketP93Result.parsed.withExplicitHydrogens)
        (analysisFuel (seOxoBracketP93Result.parsed.withExplicitHydrogens)) =
      initialRawDescriptorState seOxoBracketP93Result
        (seOxoBracketP93Result.parsed.withExplicitHydrogens)
        (analysisFuel (seOxoBracketP93Result.parsed.withExplicitHydrogens)) := by
  decide +kernel

theorem seOxoBracketP93_rule2MassesKnown :
    seOxoBracketP93Result.parsed.rule2MassesKnown? = true := by
  decide +kernel

theorem seOxoBracketP93_expandedStereochemicalAdmissible :
    seOxoBracketP93Result.expandedStereochemicalAdmissible? = true := by
  decide +kernel

theorem seOxoBracketP93_certifyChecks :
    seOxoBracketP93Result.parsed.introductionPredecessorsValid? = true ∧
    seOxoBracketP93Result.parsed.admissible? = true ∧
    seOxoBracketP93Result.parsed.writtenNeighborExact? = true ∧
    seOxoBracketP93Result.parsed.valenceOK? = true ∧
    seOxoBracketP93Result.parsed.rule2MassesKnown? = true := by
  decide +kernel

theorem seOxoBracketP93_certified?_exists :
    ∃ certified : CertifiedChemistryNormalizationResult,
      normalizeRawMoleculeP93Certified? (parsedSnapshot seOxoBracketSource) = some certified ∧
        certified.result = seOxoBracketP93Result := by
  rcases seOxoBracketP93_certifyChecks with ⟨h1, h2, h3, h4, h5⟩
  rcases certify?_exists_of_checks seOxoBracketP93Result h1 h2 h3 h4 h5 with
    ⟨certified, hcert, hresult⟩
  exact ⟨certified,
    by simpa [normalizeRawMoleculeP93Certified?, seOxoBracketP93Result, p93ResultOf] using hcert,
    hresult⟩

theorem seOxoBracketP93_tetrahedralBranch :
    (normalizedStereoAnalysisBranches seOxoBracketP93Result).tetrahedral =
      [seOxoBracketP93Assignment] := by
  rw [normalizedStereoAnalysisBranches_tetrahedral, seOxoBracketP93_descriptorState]
  decide +kernel

theorem seOxoBracketP93_ordinaryBranch :
    (normalizedStereoAnalysisBranches seOxoBracketP93Result).ordinaryDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_ordinaryDoubleBond, seOxoBracketP93_descriptorState]
  decide +kernel

theorem seOxoBracketP93_coupledBranch :
    (normalizedStereoAnalysisBranches seOxoBracketP93Result).coupledDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_coupledDoubleBond]
  dsimp only
  rw [seOxoBracketP93_descriptorState]
  decide +kernel

theorem seOxoBracketP93_oddBranch :
    (normalizedStereoAnalysisBranches seOxoBracketP93Result).oddCumuleneDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_oddCumuleneDoubleBond]
  dsimp only
  rw [seOxoBracketP93_descriptorState]
  decide +kernel

theorem seOxoBracketP93_extendedBranch :
    (normalizedStereoAnalysisBranches seOxoBracketP93Result).extendedAxial = [] := by
  rw [normalizedStereoAnalysisBranches_extendedAxial]
  dsimp only
  rw [seOxoBracketP93_descriptorState]
  decide +kernel

theorem seOxoBracketP93_branchStructure :
    normalizedStereoAnalysisBranches seOxoBracketP93Result =
      { tetrahedral := [seOxoBracketP93Assignment],
        ordinaryDoubleBond := [],
        coupledDoubleBond := [],
        oddCumuleneDoubleBond := [],
        extendedAxial := [] } := by
  refine normalizedStereoAnalysisBranches_ext ?_ ?_ ?_ ?_ ?_
  · simpa using seOxoBracketP93_tetrahedralBranch
  · simpa using seOxoBracketP93_ordinaryBranch
  · simpa using seOxoBracketP93_coupledBranch
  · simpa using seOxoBracketP93_oddBranch
  · simpa using seOxoBracketP93_extendedBranch

theorem seOxoBracketP93_analyzeNormalized :
    analyzeNormalized seOxoBracketP93Result = [seOxoBracketP93Assignment] :=
  analyzeNormalized_eq_singleton seOxoBracketP93Result seOxoBracketP93Assignment
    seOxoBracketP93_rule2MassesKnown seOxoBracketP93_expandedStereochemicalAdmissible
    seOxoBracketP93_branchStructure

/-! ### Actual public path: bracket-oxo tellurium control -/

abbrev teOxoBracketP93Result : ChemistryNormalizationResult := p93ResultOf teOxoBracketSource

def teOxoBracketP93Assignment : StereoAssignment :=
  { unit := StereoUnit.tetrahedral 0,
    outcome := StereoOutcome.refused StereoRefusal.notStereogenic }

theorem teOxoBracketSource_parse_eq :
    parseOpenSMILES teOxoBracketSource = .ok (parsedSnapshot teOxoBracketSource) :=
  parse_eq_ok_snapshot teOxoBracketSource teOxoBracketSource_parses

theorem teOxoBracketP93_descriptorState :
    discoverRawDescriptors teOxoBracketP93Result
        (teOxoBracketP93Result.parsed.withExplicitHydrogens)
        (analysisFuel (teOxoBracketP93Result.parsed.withExplicitHydrogens)) =
      initialRawDescriptorState teOxoBracketP93Result
        (teOxoBracketP93Result.parsed.withExplicitHydrogens)
        (analysisFuel (teOxoBracketP93Result.parsed.withExplicitHydrogens)) := by
  decide +kernel

theorem teOxoBracketP93_rule2MassesKnown :
    teOxoBracketP93Result.parsed.rule2MassesKnown? = true := by
  decide +kernel

theorem teOxoBracketP93_expandedStereochemicalAdmissible :
    teOxoBracketP93Result.expandedStereochemicalAdmissible? = true := by
  decide +kernel

theorem teOxoBracketP93_certifyChecks :
    teOxoBracketP93Result.parsed.introductionPredecessorsValid? = true ∧
    teOxoBracketP93Result.parsed.admissible? = true ∧
    teOxoBracketP93Result.parsed.writtenNeighborExact? = true ∧
    teOxoBracketP93Result.parsed.valenceOK? = true ∧
    teOxoBracketP93Result.parsed.rule2MassesKnown? = true := by
  decide +kernel

theorem teOxoBracketP93_certified?_exists :
    ∃ certified : CertifiedChemistryNormalizationResult,
      normalizeRawMoleculeP93Certified? (parsedSnapshot teOxoBracketSource) = some certified ∧
        certified.result = teOxoBracketP93Result := by
  rcases teOxoBracketP93_certifyChecks with ⟨h1, h2, h3, h4, h5⟩
  rcases certify?_exists_of_checks teOxoBracketP93Result h1 h2 h3 h4 h5 with
    ⟨certified, hcert, hresult⟩
  exact ⟨certified,
    by simpa [normalizeRawMoleculeP93Certified?, teOxoBracketP93Result, p93ResultOf] using hcert,
    hresult⟩

theorem teOxoBracketP93_tetrahedralBranch :
    (normalizedStereoAnalysisBranches teOxoBracketP93Result).tetrahedral =
      [teOxoBracketP93Assignment] := by
  rw [normalizedStereoAnalysisBranches_tetrahedral, teOxoBracketP93_descriptorState]
  decide +kernel

theorem teOxoBracketP93_ordinaryBranch :
    (normalizedStereoAnalysisBranches teOxoBracketP93Result).ordinaryDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_ordinaryDoubleBond, teOxoBracketP93_descriptorState]
  decide +kernel

theorem teOxoBracketP93_coupledBranch :
    (normalizedStereoAnalysisBranches teOxoBracketP93Result).coupledDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_coupledDoubleBond]
  dsimp only
  rw [teOxoBracketP93_descriptorState]
  decide +kernel

theorem teOxoBracketP93_oddBranch :
    (normalizedStereoAnalysisBranches teOxoBracketP93Result).oddCumuleneDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_oddCumuleneDoubleBond]
  dsimp only
  rw [teOxoBracketP93_descriptorState]
  decide +kernel

theorem teOxoBracketP93_extendedBranch :
    (normalizedStereoAnalysisBranches teOxoBracketP93Result).extendedAxial = [] := by
  rw [normalizedStereoAnalysisBranches_extendedAxial]
  dsimp only
  rw [teOxoBracketP93_descriptorState]
  decide +kernel

theorem teOxoBracketP93_branchStructure :
    normalizedStereoAnalysisBranches teOxoBracketP93Result =
      { tetrahedral := [teOxoBracketP93Assignment],
        ordinaryDoubleBond := [],
        coupledDoubleBond := [],
        oddCumuleneDoubleBond := [],
        extendedAxial := [] } := by
  refine normalizedStereoAnalysisBranches_ext ?_ ?_ ?_ ?_ ?_
  · simpa using teOxoBracketP93_tetrahedralBranch
  · simpa using teOxoBracketP93_ordinaryBranch
  · simpa using teOxoBracketP93_coupledBranch
  · simpa using teOxoBracketP93_oddBranch
  · simpa using teOxoBracketP93_extendedBranch

theorem teOxoBracketP93_analyzeNormalized :
    analyzeNormalized teOxoBracketP93Result = [teOxoBracketP93Assignment] :=
  analyzeNormalized_eq_singleton teOxoBracketP93Result teOxoBracketP93Assignment
    teOxoBracketP93_rule2MassesKnown teOxoBracketP93_expandedStereochemicalAdmissible
    teOxoBracketP93_branchStructure

/-! ### Legacy predecessor path: literal selenium -/

abbrev seOxoLegacyResult : ChemistryNormalizationResult := legacyResultOf seOxoSource

def seOxoLegacyAssignment : StereoAssignment :=
  { unit := StereoUnit.tetrahedral 0, outcome := StereoOutcome.tetrahedral RS.S }

theorem seOxoLegacy_descriptorState :
    discoverRawDescriptors seOxoLegacyResult
        (seOxoLegacyResult.parsed.withExplicitHydrogens)
        (analysisFuel (seOxoLegacyResult.parsed.withExplicitHydrogens)) =
      initialRawDescriptorState seOxoLegacyResult
        (seOxoLegacyResult.parsed.withExplicitHydrogens)
        (analysisFuel (seOxoLegacyResult.parsed.withExplicitHydrogens)) := by
  decide +kernel

theorem seOxoLegacy_rule2MassesKnown :
    seOxoLegacyResult.parsed.rule2MassesKnown? = true := by
  decide +kernel

theorem seOxoLegacy_expandedStereochemicalAdmissible :
    seOxoLegacyResult.expandedStereochemicalAdmissible? = true := by
  decide +kernel

theorem seOxoLegacy_certifyChecks :
    seOxoLegacyResult.parsed.introductionPredecessorsValid? = true ∧
    seOxoLegacyResult.parsed.admissible? = true ∧
    seOxoLegacyResult.parsed.writtenNeighborExact? = true ∧
    seOxoLegacyResult.parsed.valenceOK? = true ∧
    seOxoLegacyResult.parsed.rule2MassesKnown? = true := by
  decide +kernel

theorem seOxoLegacy_certified?_exists :
    ∃ certified : CertifiedChemistryNormalizationResult,
      legacyCertified? (parsedSnapshot seOxoSource) = some certified ∧
        certified.result = seOxoLegacyResult := by
  rcases seOxoLegacy_certifyChecks with ⟨h1, h2, h3, h4, h5⟩
  rcases certify?_exists_of_checks seOxoLegacyResult h1 h2 h3 h4 h5 with
    ⟨certified, hcert, hresult⟩
  exact ⟨certified,
    by simpa [legacyCertified?, seOxoLegacyResult, legacyResultOf] using hcert,
    hresult⟩

theorem seOxoLegacy_tetrahedralBranch :
    (normalizedStereoAnalysisBranches seOxoLegacyResult).tetrahedral =
      [seOxoLegacyAssignment] := by
  rw [normalizedStereoAnalysisBranches_tetrahedral, seOxoLegacy_descriptorState]
  decide +kernel

theorem seOxoLegacy_ordinaryBranch :
    (normalizedStereoAnalysisBranches seOxoLegacyResult).ordinaryDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_ordinaryDoubleBond, seOxoLegacy_descriptorState]
  decide +kernel

theorem seOxoLegacy_coupledBranch :
    (normalizedStereoAnalysisBranches seOxoLegacyResult).coupledDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_coupledDoubleBond]
  dsimp only
  rw [seOxoLegacy_descriptorState]
  decide +kernel

theorem seOxoLegacy_oddBranch :
    (normalizedStereoAnalysisBranches seOxoLegacyResult).oddCumuleneDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_oddCumuleneDoubleBond]
  dsimp only
  rw [seOxoLegacy_descriptorState]
  decide +kernel

theorem seOxoLegacy_extendedBranch :
    (normalizedStereoAnalysisBranches seOxoLegacyResult).extendedAxial = [] := by
  rw [normalizedStereoAnalysisBranches_extendedAxial]
  dsimp only
  rw [seOxoLegacy_descriptorState]
  decide +kernel

theorem seOxoLegacy_branchStructure :
    normalizedStereoAnalysisBranches seOxoLegacyResult =
      { tetrahedral := [seOxoLegacyAssignment],
        ordinaryDoubleBond := [],
        coupledDoubleBond := [],
        oddCumuleneDoubleBond := [],
        extendedAxial := [] } := by
  refine normalizedStereoAnalysisBranches_ext ?_ ?_ ?_ ?_ ?_
  · simpa using seOxoLegacy_tetrahedralBranch
  · simpa using seOxoLegacy_ordinaryBranch
  · simpa using seOxoLegacy_coupledBranch
  · simpa using seOxoLegacy_oddBranch
  · simpa using seOxoLegacy_extendedBranch

theorem seOxoLegacy_analyzeNormalized :
    analyzeNormalized seOxoLegacyResult = [seOxoLegacyAssignment] :=
  analyzeNormalized_eq_singleton seOxoLegacyResult seOxoLegacyAssignment
    seOxoLegacy_rule2MassesKnown seOxoLegacy_expandedStereochemicalAdmissible
    seOxoLegacy_branchStructure

/-! ### Legacy predecessor path: literal tellurium -/

abbrev teOxoLegacyResult : ChemistryNormalizationResult := legacyResultOf teOxoSource

def teOxoLegacyAssignment : StereoAssignment :=
  { unit := StereoUnit.tetrahedral 0, outcome := StereoOutcome.tetrahedral RS.S }

theorem teOxoLegacy_descriptorState :
    discoverRawDescriptors teOxoLegacyResult
        (teOxoLegacyResult.parsed.withExplicitHydrogens)
        (analysisFuel (teOxoLegacyResult.parsed.withExplicitHydrogens)) =
      initialRawDescriptorState teOxoLegacyResult
        (teOxoLegacyResult.parsed.withExplicitHydrogens)
        (analysisFuel (teOxoLegacyResult.parsed.withExplicitHydrogens)) := by
  decide +kernel

theorem teOxoLegacy_rule2MassesKnown :
    teOxoLegacyResult.parsed.rule2MassesKnown? = true := by
  decide +kernel

theorem teOxoLegacy_expandedStereochemicalAdmissible :
    teOxoLegacyResult.expandedStereochemicalAdmissible? = true := by
  decide +kernel

theorem teOxoLegacy_certifyChecks :
    teOxoLegacyResult.parsed.introductionPredecessorsValid? = true ∧
    teOxoLegacyResult.parsed.admissible? = true ∧
    teOxoLegacyResult.parsed.writtenNeighborExact? = true ∧
    teOxoLegacyResult.parsed.valenceOK? = true ∧
    teOxoLegacyResult.parsed.rule2MassesKnown? = true := by
  decide +kernel

theorem teOxoLegacy_certified?_exists :
    ∃ certified : CertifiedChemistryNormalizationResult,
      legacyCertified? (parsedSnapshot teOxoSource) = some certified ∧
        certified.result = teOxoLegacyResult := by
  rcases teOxoLegacy_certifyChecks with ⟨h1, h2, h3, h4, h5⟩
  rcases certify?_exists_of_checks teOxoLegacyResult h1 h2 h3 h4 h5 with
    ⟨certified, hcert, hresult⟩
  exact ⟨certified,
    by simpa [legacyCertified?, teOxoLegacyResult, legacyResultOf] using hcert,
    hresult⟩

theorem teOxoLegacy_tetrahedralBranch :
    (normalizedStereoAnalysisBranches teOxoLegacyResult).tetrahedral =
      [teOxoLegacyAssignment] := by
  rw [normalizedStereoAnalysisBranches_tetrahedral, teOxoLegacy_descriptorState]
  decide +kernel

theorem teOxoLegacy_ordinaryBranch :
    (normalizedStereoAnalysisBranches teOxoLegacyResult).ordinaryDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_ordinaryDoubleBond, teOxoLegacy_descriptorState]
  decide +kernel

theorem teOxoLegacy_coupledBranch :
    (normalizedStereoAnalysisBranches teOxoLegacyResult).coupledDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_coupledDoubleBond]
  dsimp only
  rw [teOxoLegacy_descriptorState]
  decide +kernel

theorem teOxoLegacy_oddBranch :
    (normalizedStereoAnalysisBranches teOxoLegacyResult).oddCumuleneDoubleBond = [] := by
  rw [normalizedStereoAnalysisBranches_oddCumuleneDoubleBond]
  dsimp only
  rw [teOxoLegacy_descriptorState]
  decide +kernel

theorem teOxoLegacy_extendedBranch :
    (normalizedStereoAnalysisBranches teOxoLegacyResult).extendedAxial = [] := by
  rw [normalizedStereoAnalysisBranches_extendedAxial]
  dsimp only
  rw [teOxoLegacy_descriptorState]
  decide +kernel

theorem teOxoLegacy_branchStructure :
    normalizedStereoAnalysisBranches teOxoLegacyResult =
      { tetrahedral := [teOxoLegacyAssignment],
        ordinaryDoubleBond := [],
        coupledDoubleBond := [],
        oddCumuleneDoubleBond := [],
        extendedAxial := [] } := by
  refine normalizedStereoAnalysisBranches_ext ?_ ?_ ?_ ?_ ?_
  · simpa using teOxoLegacy_tetrahedralBranch
  · simpa using teOxoLegacy_ordinaryBranch
  · simpa using teOxoLegacy_coupledBranch
  · simpa using teOxoLegacy_oddBranch
  · simpa using teOxoLegacy_extendedBranch

theorem teOxoLegacy_analyzeNormalized :
    analyzeNormalized teOxoLegacyResult = [teOxoLegacyAssignment] :=
  analyzeNormalized_eq_singleton teOxoLegacyResult teOxoLegacyAssignment
    teOxoLegacy_rule2MassesKnown teOxoLegacy_expandedStereochemicalAdmissible
    teOxoLegacy_branchStructure

/-! ## Exact public assignment lists

The public entry point `analyzeSmilesP93` is the actual production path.  The following theorems
state its complete output list, not merely `isOk`.  After the source-hydrogen freeze repair the
literal unbracketed Se and Te spellings are refused as not stereogenic, matching what the
predecessor module proved for its local candidate fidelity path; the bracket controls are refused
in the same way.  The predecessor outputs are stated separately below under explicit `legacy`
names.

The proofs rewrite through the factored parse, certification, descriptor-state, branch, and
analyzer stages above; no monolithic reduction of the analyzer is repeated here. -/

theorem seOxoSource_p93_exactAssignmentList :
    (analyzeSmilesP93 seOxoSource).toOption =
      some [{ unit := StereoUnit.tetrahedral 0,
              outcome := StereoOutcome.refused StereoRefusal.notStereogenic }] := by
  obtain ⟨certified, hcert, hresult⟩ := seOxoP93_certified?_exists
  have hadmissible : certified.result.expandedStereochemicalAdmissible? = true := by
    rw [hresult]
    exact seOxoP93_expandedStereochemicalAdmissible
  have hanalyzed : analyzeNormalized certified.result = [seOxoP93Assignment] := by
    rw [hresult]
    exact seOxoP93_analyzeNormalized
  have h := analyzeSmilesP93_toOption_eq_singleton seOxoSource (parsedSnapshot seOxoSource)
    certified seOxoP93Assignment seOxoSource_parse_eq hcert hadmissible hanalyzed
  simpa [seOxoP93Assignment] using h

theorem teOxoSource_p93_exactAssignmentList :
    (analyzeSmilesP93 teOxoSource).toOption =
      some [{ unit := StereoUnit.tetrahedral 0,
              outcome := StereoOutcome.refused StereoRefusal.notStereogenic }] := by
  obtain ⟨certified, hcert, hresult⟩ := teOxoP93_certified?_exists
  have hadmissible : certified.result.expandedStereochemicalAdmissible? = true := by
    rw [hresult]
    exact teOxoP93_expandedStereochemicalAdmissible
  have hanalyzed : analyzeNormalized certified.result = [teOxoP93Assignment] := by
    rw [hresult]
    exact teOxoP93_analyzeNormalized
  have h := analyzeSmilesP93_toOption_eq_singleton teOxoSource (parsedSnapshot teOxoSource)
    certified teOxoP93Assignment teOxoSource_parse_eq hcert hadmissible hanalyzed
  simpa [teOxoP93Assignment] using h

theorem seOxoBracketSource_p93_exactAssignmentList :
    (analyzeSmilesP93 seOxoBracketSource).toOption =
      some [{ unit := StereoUnit.tetrahedral 0,
              outcome := StereoOutcome.refused StereoRefusal.notStereogenic }] := by
  obtain ⟨certified, hcert, hresult⟩ := seOxoBracketP93_certified?_exists
  have hadmissible : certified.result.expandedStereochemicalAdmissible? = true := by
    rw [hresult]
    exact seOxoBracketP93_expandedStereochemicalAdmissible
  have hanalyzed : analyzeNormalized certified.result = [seOxoBracketP93Assignment] := by
    rw [hresult]
    exact seOxoBracketP93_analyzeNormalized
  have h := analyzeSmilesP93_toOption_eq_singleton seOxoBracketSource
    (parsedSnapshot seOxoBracketSource) certified seOxoBracketP93Assignment
    seOxoBracketSource_parse_eq hcert hadmissible hanalyzed
  simpa [seOxoBracketP93Assignment] using h

theorem teOxoBracketSource_p93_exactAssignmentList :
    (analyzeSmilesP93 teOxoBracketSource).toOption =
      some [{ unit := StereoUnit.tetrahedral 0,
              outcome := StereoOutcome.refused StereoRefusal.notStereogenic }] := by
  obtain ⟨certified, hcert, hresult⟩ := teOxoBracketP93_certified?_exists
  have hadmissible : certified.result.expandedStereochemicalAdmissible? = true := by
    rw [hresult]
    exact teOxoBracketP93_expandedStereochemicalAdmissible
  have hanalyzed : analyzeNormalized certified.result = [teOxoBracketP93Assignment] := by
    rw [hresult]
    exact teOxoBracketP93_analyzeNormalized
  have h := analyzeSmilesP93_toOption_eq_singleton teOxoBracketSource
    (parsedSnapshot teOxoBracketSource) certified teOxoBracketP93Assignment
    teOxoBracketSource_parse_eq hcert hadmissible hanalyzed
  simpa [teOxoBracketP93Assignment] using h

/-! ## Exact predecessor assignment lists, under explicit legacy names

These record what the predecessor order returned for the literal spellings.  They are stated
about `analyzeSmilesP93Legacy`, never about `analyzeSmilesP93`. -/

theorem seOxoSource_legacyP93_exactAssignmentList :
    (analyzeSmilesP93Legacy seOxoSource).toOption =
      some [{ unit := StereoUnit.tetrahedral 0, outcome := StereoOutcome.tetrahedral RS.S }] := by
  obtain ⟨certified, hcert, hresult⟩ := seOxoLegacy_certified?_exists
  have hadmissible : certified.result.expandedStereochemicalAdmissible? = true := by
    rw [hresult]
    exact seOxoLegacy_expandedStereochemicalAdmissible
  have hanalyzed : analyzeNormalized certified.result = [seOxoLegacyAssignment] := by
    rw [hresult]
    exact seOxoLegacy_analyzeNormalized
  have h := analyzeSmilesP93Legacy_toOption_eq_singleton seOxoSource
    (parsedSnapshot seOxoSource) certified seOxoLegacyAssignment seOxoSource_parse_eq
    hcert hadmissible hanalyzed
  simpa [seOxoLegacyAssignment] using h

theorem teOxoSource_legacyP93_exactAssignmentList :
    (analyzeSmilesP93Legacy teOxoSource).toOption =
      some [{ unit := StereoUnit.tetrahedral 0, outcome := StereoOutcome.tetrahedral RS.S }] := by
  obtain ⟨certified, hcert, hresult⟩ := teOxoLegacy_certified?_exists
  have hadmissible : certified.result.expandedStereochemicalAdmissible? = true := by
    rw [hresult]
    exact teOxoLegacy_expandedStereochemicalAdmissible
  have hanalyzed : analyzeNormalized certified.result = [teOxoLegacyAssignment] := by
    rw [hresult]
    exact teOxoLegacy_analyzeNormalized
  have h := analyzeSmilesP93Legacy_toOption_eq_singleton teOxoSource
    (parsedSnapshot teOxoSource) certified teOxoLegacyAssignment teOxoSource_parse_eq
    hcert hadmissible hanalyzed
  simpa [teOxoLegacyAssignment] using h

/-! ## Kernel-authority guards -/

assert_kernel_only seOxoSource_parses
assert_kernel_only seOxoSource_admitted
assert_kernel_only teOxoSource_admitted
assert_kernel_only seOxoBracketSource_admitted
assert_kernel_only teOxoBracketSource_admitted
assert_kernel_only seOxoSource_boundary
assert_kernel_only teOxoSource_boundary
assert_kernel_only seOxoBracketSource_boundary
assert_kernel_only teOxoBracketSource_boundary
assert_kernel_only isTrigonalPyramidalOxidoRootEdge_eq_false_of_centerElement_ne_P_ne_S
assert_kernel_only seOxoSource_writtenHydrogenCounts
assert_kernel_only teOxoSource_writtenHydrogenCounts
assert_kernel_only seOxoBracketSource_writtenHydrogenCounts
assert_kernel_only seOxoSource_p93Result_hydrogenCounts
assert_kernel_only teOxoSource_p93Result_hydrogenCounts
assert_kernel_only seOxoBracketSource_p93Result_hydrogenCounts
assert_kernel_only teOxoBracketSource_p93Result_hydrogenCounts
assert_kernel_only seOxoSource_p93_expandedGraph
assert_kernel_only teOxoSource_p93_expandedGraph
assert_kernel_only seOxoBracketSource_p93_expandedGraph
assert_kernel_only teOxoBracketSource_p93_expandedGraph
assert_kernel_only seOxoSource_p93_branchStatus
assert_kernel_only teOxoSource_p93_branchStatus
assert_kernel_only seOxoBracketSource_p93_branchStatus
assert_kernel_only teOxoBracketSource_p93_branchStatus
assert_kernel_only seOxoSource_p93_tetrahedralOutcome
assert_kernel_only teOxoSource_p93_tetrahedralOutcome
assert_kernel_only seOxoBracketSource_p93_tetrahedralOutcome
assert_kernel_only teOxoBracketSource_p93_tetrahedralOutcome
assert_kernel_only seOxoSource_legacyResult_hydrogenCounts
assert_kernel_only teOxoSource_legacyResult_hydrogenCounts
assert_kernel_only seOxoBracketSource_legacyResult_hydrogenCounts
assert_kernel_only seOxoSource_legacy_hydrogenArtifact
assert_kernel_only teOxoSource_legacy_hydrogenArtifact
assert_kernel_only seOxoSource_legacy_branchStatus
assert_kernel_only seOxoSource_legacy_tetrahedralOutcome
assert_kernel_only seOxoBracketSource_legacy_branchStatus
assert_kernel_only seOxoSource_plain_expandedGraph
assert_kernel_only seOxoSource_plain_branchStatus
assert_kernel_only seOxoSource_plain_tetrahedralOutcome
assert_kernel_only seOxoBracketSource_plain_branchStatus
assert_kernel_only seOxoBracketSource_plain_tetrahedralOutcome
assert_kernel_only seOxoSource_plainEntryPoint_reachable
assert_kernel_only seOxoSource_p93EntryPoint_reachable
assert_kernel_only teOxoSource_p93EntryPoint_reachable
assert_kernel_only seOxoBracketSource_p93EntryPoint_reachable
assert_kernel_only teOxoBracketSource_p93EntryPoint_reachable
assert_kernel_only parse_eq_ok_snapshot
assert_kernel_only certify?_result_of_eq_some
assert_kernel_only certify?_exists_of_checks
assert_kernel_only analyzeNormalized_eq_of_branches
assert_kernel_only analyzeNormalized_eq_singleton
assert_kernel_only analyzeSmilesP93_toOption_eq_singleton
assert_kernel_only analyzeSmilesP93Legacy_toOption_eq_singleton
assert_kernel_only seOxoP93_descriptorState
assert_kernel_only seOxoP93_certified?_exists
assert_kernel_only seOxoP93_branchStructure
assert_kernel_only seOxoP93_analyzeNormalized
assert_kernel_only teOxoP93_descriptorState
assert_kernel_only teOxoP93_certified?_exists
assert_kernel_only teOxoP93_branchStructure
assert_kernel_only teOxoP93_analyzeNormalized
assert_kernel_only seOxoBracketP93_descriptorState
assert_kernel_only seOxoBracketP93_certified?_exists
assert_kernel_only seOxoBracketP93_branchStructure
assert_kernel_only seOxoBracketP93_analyzeNormalized
assert_kernel_only teOxoBracketP93_descriptorState
assert_kernel_only teOxoBracketP93_certified?_exists
assert_kernel_only teOxoBracketP93_branchStructure
assert_kernel_only teOxoBracketP93_analyzeNormalized
assert_kernel_only seOxoLegacy_descriptorState
assert_kernel_only seOxoLegacy_certified?_exists
assert_kernel_only seOxoLegacy_branchStructure
assert_kernel_only seOxoLegacy_analyzeNormalized
assert_kernel_only teOxoLegacy_descriptorState
assert_kernel_only teOxoLegacy_certified?_exists
assert_kernel_only teOxoLegacy_branchStructure
assert_kernel_only teOxoLegacy_analyzeNormalized
assert_kernel_only seOxoSource_p93_exactAssignmentList
assert_kernel_only teOxoSource_p93_exactAssignmentList
assert_kernel_only seOxoBracketSource_p93_exactAssignmentList
assert_kernel_only teOxoBracketSource_p93_exactAssignmentList
assert_kernel_only seOxoSource_legacyP93_exactAssignmentList
assert_kernel_only teOxoSource_legacyP93_exactAssignmentList

end BlueBookP93.ChalcogenOxoPublicFidelity
end TetraStereo.OneCenter
