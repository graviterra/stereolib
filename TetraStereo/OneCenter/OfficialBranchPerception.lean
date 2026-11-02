import TetraStereo.OneCenter.DescriptorPathInference
import TetraStereo.OneCenter.OfficialContextPerception
import TetraStereo.OneCenter.OfficialCIPEngine

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

/-!
  Molecule-wide official CIP branch perception.

  `OfficialContextPerception` converts already-perceived descriptor evidence into official
  Rule 3/4/5 contexts.  This module connects that evidence layer to molecular branch walking:
  ligand branches are expanded with the cycle-cut walker, descriptor-bearing centers are read from
  a global discovery state, and the resulting branch evidence is fed directly into the official
  comparator.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace DescriptorDiscoveryState

variable {m : MultiCenterMolecule V} {cfg : m.Configuration}

/-- Descriptor evidence available at one distinguished center after global discovery.

Lowercase pseudoasymmetric descriptors are preferred over local `R/S` seeds because they are the
descriptor that Rule 4c should see once a center has been resolved as pseudoasymmetric. -/
def perceivedDescriptorAt? (state : DescriptorDiscoveryState m cfg) (center : m.Center) :
    Option PerceivedDescriptor :=
  Option.first ((state.pseudo center).map PerceivedDescriptor.pseudoTetrahedral)
    ((state.rs center).map PerceivedDescriptor.tetrahedral)

@[simp] theorem perceivedDescriptorAt?_eq_some_of_pseudo_eq_some
    (state : DescriptorDiscoveryState m cfg) (center : m.Center) (descriptor : PseudoRS)
    (h : state.pseudo center = some descriptor) :
    state.perceivedDescriptorAt? center =
      some (PerceivedDescriptor.pseudoTetrahedral descriptor) := by
  simp [perceivedDescriptorAt?, h]

@[simp] theorem perceivedDescriptorAt?_eq_some_of_pseudo_eq_none_rs_eq_some
    (state : DescriptorDiscoveryState m cfg) (center : m.Center) (descriptor : RS)
    (hpseudo : state.pseudo center = none) (hrs : state.rs center = some descriptor) :
    state.perceivedDescriptorAt? center =
      some (PerceivedDescriptor.tetrahedral descriptor) := by
  simp [perceivedDescriptorAt?, hpseudo, hrs]

@[simp] theorem perceivedDescriptorAt?_eq_none_of_pseudo_eq_none_rs_eq_none
    (state : DescriptorDiscoveryState m cfg) (center : m.Center)
    (hpseudo : state.pseudo center = none) (hrs : state.rs center = none) :
    state.perceivedDescriptorAt? center = none := by
  simp [perceivedDescriptorAt?, hpseudo, hrs]

end DescriptorDiscoveryState

/-- A descriptor-bearing source center found while walking a ligand branch. -/
structure BranchDescriptorSource (m : MultiCenterMolecule V) where
  source : m.Center
  descriptor : PerceivedDescriptor

namespace BranchDescriptorSource

variable {m : MultiCenterMolecule V}

/-- The branch-source descriptor as one-ligand perceived evidence. -/
def toEvidence (source : BranchDescriptorSource m) : PerceivedLigandEvidence :=
  PerceivedLigandEvidence.ofDescriptor source.descriptor

/-- The official context carried by this one branch-source descriptor. -/
def toOfficialLigandRuleContext (source : BranchDescriptorSource m) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  source.toEvidence.toOfficialLigandRuleContext

@[simp] theorem toEvidence_descriptor? (source : BranchDescriptorSource m) :
    source.toEvidence.descriptor? = some source.descriptor :=
  rfl

end BranchDescriptorSource

/-- First pair of descriptor sources whose molecular centers are distinct. -/
def firstDistinctDescriptorSourcePair? {m : MultiCenterMolecule V} :
    List (BranchDescriptorSource m) →
      Option (BranchDescriptorSource m × BranchDescriptorSource m)
  | [] => none
  | source :: sources =>
      match sources.find? fun other => decide (other.source ≠ source.source) with
      | some other => some (source, other)
      | none => firstDistinctDescriptorSourcePair? sources

@[simp] theorem firstDistinctDescriptorSourcePair?_cons_cons_of_source_ne
    {m : MultiCenterMolecule V} (left right : BranchDescriptorSource m)
    (rest : List (BranchDescriptorSource m)) (h : right.source ≠ left.source) :
    firstDistinctDescriptorSourcePair? (left :: right :: rest) = some (left, right) := by
  simp [firstDistinctDescriptorSourcePair?, h]

/-- Convert all descriptor sources found on one branch into branch-level evidence. -/
def evidenceOfDescriptorSources {m : MultiCenterMolecule V}
    (sources : List (BranchDescriptorSource m)) : PerceivedLigandEvidence where
  descriptor? := sources.head?.map fun source => source.descriptor
  descriptorPair? :=
    (firstDistinctDescriptorSourcePair? sources).map fun pair =>
      (pair.1.descriptor, pair.2.descriptor)

@[simp] theorem evidenceOfDescriptorSources_nil {m : MultiCenterMolecule V} :
    evidenceOfDescriptorSources ([] : List (BranchDescriptorSource m)) =
      PerceivedLigandEvidence.empty := by
  rfl

theorem evidenceOfDescriptorSources_rule4bPair?_of_two_distinct_sources
    {m : MultiCenterMolecule V} (left right : BranchDescriptorSource m)
    (rest : List (BranchDescriptorSource m)) (h : right.source ≠ left.source) :
    (evidenceOfDescriptorSources (left :: right :: rest)).rule4bPair? =
      PerceivedDescriptor.pairKind? left.descriptor right.descriptor := by
  simp [evidenceOfDescriptorSources, PerceivedLigandEvidence.rule4bPair?, h]

namespace MultiCenterMolecule

variable (m : MultiCenterMolecule V)

/-! ### Branch source collection -/

/-- All distinguished source centers reached in one branch frontier layer. -/
def branchSourcesAtDepth (center : m.Center) (i : Fin 4) (depth : ℕ) :
    List m.Center :=
  (m.branchFrontier center i depth).filterMap fun state =>
    m.centerOfAtomExcept? center state.current

/-- Collect distinguished source centers while walking a branch from increasing frontier depths. -/
def branchSourcesFrom (center : m.Center) (i : Fin 4) (depth : ℕ) :
    ℕ → List m.Center
  | 0 => m.branchSourcesAtDepth center i depth
  | fuel + 1 =>
      m.branchSourcesAtDepth center i depth ++
        branchSourcesFrom center i (depth + 1) fuel

/-- Collect distinguished source centers found up to a fuel bound. -/
def branchSourcesWithin (center : m.Center) (i : Fin 4) (fuel : ℕ) :
    List m.Center :=
  m.branchSourcesFrom center i 0 fuel

/-- Default finite branch-source collection. -/
def branchSources (center : m.Center) (i : Fin 4) : List m.Center :=
  m.branchSourcesWithin center i (Fintype.card V)

@[simp] theorem branchSourcesWithin_zero (center : m.Center) (i : Fin 4) :
    m.branchSourcesWithin center i 0 = m.branchSourcesAtDepth center i 0 :=
  rfl

@[simp] theorem branchSourcesAtDepth_zero (center : m.Center) (i : Fin 4) :
    m.branchSourcesAtDepth center i 0 =
      match m.centerOfAtomExcept? center (m.ligandAtomAt center i) with
      | some source => [source]
      | none => [] := by
  cases h : m.centerOfAtomExcept? center (m.ligandAtomAt center i) <;>
    simp [branchSourcesAtDepth, branchFrontier, branchRootState,
      MoleculeGraph.cycleCutFrontier, h]

/-- Descriptor-bearing source centers found on a ligand branch. -/
def branchDescriptorSourcesWithin {cfg : m.Configuration}
    (state : DescriptorDiscoveryState m cfg) (center : m.Center) (i : Fin 4) (fuel : ℕ) :
    List (BranchDescriptorSource m) :=
  (m.branchSourcesWithin center i fuel).filterMap fun source =>
    (state.perceivedDescriptorAt? source).map fun descriptor =>
      { source := source, descriptor := descriptor }

/-- Default descriptor-bearing source centers found on a ligand branch. -/
def branchDescriptorSources {cfg : m.Configuration}
    (state : DescriptorDiscoveryState m cfg) (center : m.Center) (i : Fin 4) :
    List (BranchDescriptorSource m) :=
  m.branchDescriptorSourcesWithin state center i (Fintype.card V)

/-- First descriptor-bearing source center found on a ligand branch. -/
def firstBranchDescriptorSourceWithin? {cfg : m.Configuration}
    (state : DescriptorDiscoveryState m cfg) (center : m.Center) (i : Fin 4) (fuel : ℕ) :
    Option (BranchDescriptorSource m) :=
  (m.branchDescriptorSourcesWithin state center i fuel).head?

/-- First distinct descriptor-source pair found on a ligand branch. -/
def firstBranchDescriptorSourcePairWithin? {cfg : m.Configuration}
    (state : DescriptorDiscoveryState m cfg) (center : m.Center) (i : Fin 4) (fuel : ℕ) :
    Option (BranchDescriptorSource m × BranchDescriptorSource m) :=
  firstDistinctDescriptorSourcePair? (m.branchDescriptorSourcesWithin state center i fuel)

/-! ### Official context generation from branch evidence -/

/-- Branch-level evidence discovered automatically from molecular source centers. -/
def branchLigandEvidenceWithin {cfg : m.Configuration}
    (state : DescriptorDiscoveryState m cfg) (center : m.Center) (i : Fin 4) (fuel : ℕ) :
    PerceivedLigandEvidence :=
  evidenceOfDescriptorSources (m.branchDescriptorSourcesWithin state center i fuel)

/-- Official ligand context discovered automatically from molecular source centers. -/
def officialBranchContextWithin {cfg : m.Configuration}
    (state : DescriptorDiscoveryState m cfg) (center : m.Center) (i : Fin 4) (fuel : ℕ) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  (m.branchLigandEvidenceWithin state center i fuel).toOfficialLigandRuleContext

/-- Default official ligand context discovered automatically from molecular source centers. -/
def officialBranchContext {cfg : m.Configuration}
    (state : DescriptorDiscoveryState m cfg) (center : m.Center) (i : Fin 4) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  m.officialBranchContextWithin state center i (Fintype.card V)

end MultiCenterMolecule

namespace Rule5TaskSelector

variable {m : MultiCenterMolecule V} {cfg : m.Configuration}
variable (selector : Rule5TaskSelector m cfg)

/-- Automatic official contexts after running this selector's descriptor-discovery schedule once. -/
def officialContextFromRunOnceWithin (fuel : ℕ) :
    m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext :=
  fun center i => m.officialBranchContextWithin selector.schedule.runOnce center i fuel

/-- Default automatic official contexts after running this selector's schedule once. -/
def officialContextFromRunOnce :
    m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext :=
  selector.officialContextFromRunOnceWithin (Fintype.card V)

end Rule5TaskSelector

namespace MultiCenterMolecule

variable (m : MultiCenterMolecule V) (cfg : m.Configuration)

/-- The global discovery state used by the path-walking official branch perception engine. -/
def officialBranchPerceptionStateWithin (fuel : ℕ) : DescriptorDiscoveryState m cfg :=
  (pathRule5TaskSelectorWithin m cfg fuel).schedule.runOnce

/-- Automatic official contexts from branch walking plus one pass of descriptor discovery. -/
def officialBranchContextFromPathsWithin (fuel : ℕ) :
    m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext :=
  fun center i => m.officialBranchContextWithin
    (m.officialBranchPerceptionStateWithin cfg fuel) center i fuel

/-- Default automatic official contexts from branch walking plus one pass of descriptor discovery. -/
def officialBranchContextFromPaths :
    m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext :=
  m.officialBranchContextFromPathsWithin cfg (Fintype.card V)

/-- Compare two ligands using automatically perceived official branch contexts and the canonical
official hierarchical-digraph engine. -/
def cipRuleCompareOfficialBranchDescriptorWithin (fuel : ℕ)
    (center : m.Center) (i j : Fin 4) : CIPTraceCertificate :=
  m.cipOfficialCompareAt (m.officialBranchContextFromPathsWithin cfg fuel) center i j

/-- Default comparison using automatically perceived official branch contexts. -/
def cipRuleCompareOfficialBranchDescriptor
    (center : m.Center) (i j : Fin 4) : CIPTraceCertificate :=
  m.cipRuleCompareOfficialBranchDescriptorWithin cfg (Fintype.card V) center i j

/-- Result surface for automatic official branch perception at a multi-center molecule. -/
structure OfficialBranchPerceptionEngineResult where
  discoveryState : DescriptorDiscoveryState m cfg
  context : m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext
  compare : m.Center → Fin 4 → Fin 4 → CIPTraceCertificate

/-- Run the automatic official branch perception engine with a shared branch/search fuel. -/
def officialBranchPerceptionEngineWithin (fuel : ℕ) :
    OfficialBranchPerceptionEngineResult m cfg where
  discoveryState := m.officialBranchPerceptionStateWithin cfg fuel
  context := m.officialBranchContextFromPathsWithin cfg fuel
  compare := m.cipRuleCompareOfficialBranchDescriptorWithin cfg fuel

/-- Default automatic official branch perception engine. -/
def officialBranchPerceptionEngine : OfficialBranchPerceptionEngineResult m cfg :=
  m.officialBranchPerceptionEngineWithin cfg (Fintype.card V)

end MultiCenterMolecule

end
end OneCenter
end TetraStereo
