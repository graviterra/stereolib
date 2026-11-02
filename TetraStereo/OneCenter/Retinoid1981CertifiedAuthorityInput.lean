import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.Retinoid1981FigureGraphTranscription
import TetraStereo.KernelOnly

set_option autoImplicit false















namespace TetraStereo.OneCenter
namespace Retinoid1981
namespace FigureAuthorityInput

open FigureGraphTranscription

def atomElementToPeriodic? : AtomElement → Option PeriodicElement
  | .carbon => PeriodicElement.ofAtomicNumber? 6
  | .nitrogen => PeriodicElement.ofAtomicNumber? 7
  | .oxygen => PeriodicElement.ofAtomicNumber? 8
  | .fluorine => PeriodicElement.ofAtomicNumber? 9
  | .genericSubstituent => none

def atomNodeToSemanticAtom? (node : AtomNode) : Option SemanticAtom := do
  let element ← atomElementToPeriodic? node.element
  pure { element := element }

def nodeIndexAux? : List AtomNode → Nat → Nat → Option Nat
  | [], _locant, _index => none
  | node :: remaining, locant, index =>
      if node.locant = locant then some index
      else nodeIndexAux? remaining locant (index + 1)

def heavyAtomNodeIndex? (graph : HeavyAtomGraph) (locant : Nat) : Option Nat :=
  nodeIndexAux? graph.nodes locant 0

def bondOrderToNat : FigureGraphTranscription.BondOrder → Nat
  | .single => 1
  | .double => 2

def graphBondToSemanticInteraction? (graph : HeavyAtomGraph)
    (bond : GraphBond) : Option SemanticInteraction := do
  let low ← heavyAtomNodeIndex? graph bond.low
  let high ← heavyAtomNodeIndex? graph bond.high
  pure { participants := [low, high], kind := .covalent (bondOrderToNat bond.order) }

def heavyAtomGraphToAuthoritativeChemicalInput? (graph : HeavyAtomGraph) :
    Option AuthoritativeChemicalInput := do
  let atoms ← graph.nodes.mapM atomNodeToSemanticAtom?
  let interactions ← graph.bonds.mapM (graphBondToSemanticInteraction? graph)
  pure { molecule := { atoms := atoms, interactions := interactions } }

structure AuthorityInputCandidate where
  artifact : SourceAudit.ImageArtifact
  graph : HeavyAtomGraph
  deriving DecidableEq, Repr

/-- Literal source-order graph occurrences. Artifacts A51 and A52a each contribute two graphs. -/
def authorityInputCandidates : List AuthorityInputCandidate :=
  figureGraphFamilies.flatMap fun family =>
    family.graphs.map fun graph => ⟨family.artifact, graph⟩

@[simp] theorem authority_input_candidate_count : authorityInputCandidates.length = 16 := by
  decide

structure CertifiedGraphAuthorityInput where
  candidate : AuthorityInputCandidate
  certified : CertifiedAuthoritativeChemicalInput
  atomCountExact :
    certified.input.molecule.atoms.length = candidate.graph.nodes.length
  interactionCountExact :
    certified.input.molecule.interactions.length = candidate.graph.bonds.length

def AuthorityInputCandidate.certify? (candidate : AuthorityInputCandidate) :
    Option CertifiedGraphAuthorityInput := do
  let input ← heavyAtomGraphToAuthoritativeChemicalInput? candidate.graph
  let certified ← input.certify?
  if atomCountExact :
      certified.input.molecule.atoms.length = candidate.graph.nodes.length then
    if interactionCountExact :
        certified.input.molecule.interactions.length = candidate.graph.bonds.length then
      some { candidate := candidate
             certified := certified
             atomCountExact := atomCountExact
             interactionCountExact := interactionCountExact }
    else none
  else none

def concreteAuthorityInputs : List CertifiedGraphAuthorityInput :=
  authorityInputCandidates.filterMap AuthorityInputCandidate.certify?

def unresolvedAuthorityGraphs : List AuthorityInputCandidate :=
  authorityInputCandidates.filter fun candidate => candidate.certify?.isNone

@[simp] theorem concrete_authority_input_count : concreteAuthorityInputs.length = 14 := by
  decide

@[simp] theorem unresolved_authority_graph_count : unresolvedAuthorityGraphs.length = 2 := by
  decide

@[simp] theorem unresolved_authority_artifacts_exact :
    unresolvedAuthorityGraphs.map AuthorityInputCandidate.artifact =
      [ .glucuronideSubstituent, .motretinideEtretinate ] := by
  decide

@[simp] theorem concrete_authority_artifacts_exact :
    concreteAuthorityInputs.map (fun entry => entry.candidate.artifact) =
      [ .stereoparentSkeleton
      , .didehydroretinol
      , .alphaVitaminA
      , .epoxyDihydroretinol
      , .fluororetinoate
      , .secoRetinol
      , .acetylDinorRetinoicAcid
      , .anhydroVitaminA
      , .retroRetinylAcetate
      , .hydroxyAcetoxyRetinol
      , .hydroxyAcetoxyRetinol
      , .cisRetinoidExamples
      , .cisRetinoidExamples
      , .retroRetinalOxime ] := by
  decide

@[simp] theorem certified_atom_count_exact (entry : CertifiedGraphAuthorityInput) :
    entry.certified.input.molecule.atoms.length = entry.candidate.graph.nodes.length :=
  entry.atomCountExact

@[simp] theorem certified_interaction_count_exact (entry : CertifiedGraphAuthorityInput) :
    entry.certified.input.molecule.interactions.length = entry.candidate.graph.bonds.length :=
  entry.interactionCountExact

theorem every_concrete_authority_input_structurally_wellFormed
    (entry : CertifiedGraphAuthorityInput) :
    entry.certified.input.StructurallyWellFormed :=
  entry.certified.structurallyWellFormed

@[simp] theorem authority_input_frontier_count_exact :
    concreteAuthorityInputs.length + unresolvedAuthorityGraphs.length =
      authorityInputCandidates.length := by
  rw [concrete_authority_input_count, unresolved_authority_graph_count,
    authority_input_candidate_count]

end FigureAuthorityInput
end Retinoid1981
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.unresolved_authority_artifacts_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.concrete_authority_artifacts_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.certified_atom_count_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.certified_interaction_count_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.every_concrete_authority_input_structurally_wellFormed
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.authority_input_frontier_count_exact
