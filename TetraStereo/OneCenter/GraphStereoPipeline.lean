import TetraStereo.OneCenter.MultiCenterDetection
import TetraStereo.OneCenter.MultiCenterCIPRSRelations

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
  Graph-level stereochemistry pipeline.

  This module packages the lower-level pieces into the path used by future examples:

  raw molecular graph
    → detected tetrahedral centers
    → detected multi-center system
    → configurations / CIP-normalized `R/S` patterns
    → meso, chiral, enantiomeric, and diastereomeric relations by symmetry.
-/

/-- The automatically detected multi-center stereochemical system of a graph. -/
abbrev detectedStereoSystem (m : MoleculeGraph V) : MultiCenterMolecule V :=
  m.detectedMultiCenterMolecule

/-- Centers in the automatically detected stereochemical system. -/
abbrev GraphCenter (m : MoleculeGraph V) : Type _ :=
  m.detectedStereoSystem.Center

/-- Frame configurations on all automatically detected centers. -/
abbrev GraphConfiguration (m : MoleculeGraph V) : Type _ :=
  m.detectedStereoSystem.Configuration

/-- Configuration orbits by graph-induced symmetries of the detected system. -/
abbrev GraphConfigurationQ (m : MoleculeGraph V) : Type _ :=
  m.detectedStereoSystem.ConfigurationQ

/-- Automorphisms of the detected stereochemical system. -/
abbrev GraphStereoAut (m : MoleculeGraph V) : Type _ :=
  m.detectedStereoSystem.Aut

/-- CIP-normalized `R/S` patterns on all automatically detected centers. -/
abbrev GraphCipRSPattern (m : MoleculeGraph V) : Type _ :=
  m.detectedStereoSystem.CipRSPattern

/-- Symmetry classes of graph-level CIP-normalized `R/S` patterns. -/
abbrev GraphCipRSPatternQ (m : MoleculeGraph V) : Type _ :=
  m.detectedStereoSystem.CipRSPatternQ

/-- Every automatically detected center is CIP-stereogenic. -/
abbrev GraphStereogenicByCIP (m : MoleculeGraph V) : Prop :=
  ∀ c : m.GraphCenter, m.detectedStereoSystem.StereogenicByCIPAt c

/-- Every automatically detected center is cycle-cut CIP-stereogenic. -/
abbrev GraphStereogenicByCIPCycleCut (m : MoleculeGraph V) : Prop :=
  ∀ c : m.GraphCenter, m.detectedStereoSystem.StereogenicByCIPCycleCutAt c

/-- A graph automorphism as a stereo-system automorphism of the detected centers. -/
def graphStereoAutOfGraphAut (m : MoleculeGraph V) (e : m.Aut) : m.GraphStereoAut :=
  m.detectedMultiCenterAutOfGraphAut e

@[simp] theorem coe_graphStereoAutOfGraphAut (m : MoleculeGraph V) (e : m.Aut) :
    ((m.graphStereoAutOfGraphAut e : m.GraphStereoAut) : Equiv.Perm V) = e := rfl

/-- The raw CIP-normalized graph-level `R/S` pattern of a configuration.

This is deterministic even if an automatically detected center has tied CIP keys.  Prefer
`graphCipRSPatternOfResolved` or `graphCipRSPattern?` for descriptor-level graph statements. -/
abbrev graphCipRSPattern (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.GraphCipRSPattern :=
  m.detectedStereoSystem.cipRSPatternOfConfiguration cfg

/-- The raw cycle-cut CIP-normalized graph-level `R/S` pattern of a configuration. -/
abbrev graphCipRSPatternCycleCut (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.GraphCipRSPattern :=
  m.detectedStereoSystem.cipRSPatternOfConfigurationCycleCut cfg

/-- Safe cycle-cut graph-level CIP-normalized `R/S` pattern: returns `none` unless every detected
center is cycle-cut CIP-resolved. -/
noncomputable def graphCipRSPatternCycleCut? (m : MoleculeGraph V)
    (cfg : m.GraphConfiguration) : Option m.GraphCipRSPattern :=
  m.detectedStereoSystem.cipRSPatternOfConfigurationCycleCut? cfg

/-- The graph-level CIP-normalized `R/S` pattern with explicit resolved-CIP evidence for every
detected center. -/
abbrev graphCipRSPatternOfResolved (m : MoleculeGraph V) (_ : m.GraphStereogenicByCIP)
    (cfg : m.GraphConfiguration) : m.GraphCipRSPattern :=
  m.graphCipRSPattern cfg

/-- Safe graph-level CIP-normalized `R/S` pattern: returns `none` unless every detected center is
CIP-resolved. -/
noncomputable def graphCipRSPattern? (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    Option m.GraphCipRSPattern :=
  by
    classical
    exact
      if h : m.GraphStereogenicByCIP then
        some (m.graphCipRSPatternOfResolved h cfg)
      else
        none

theorem graphCipRSPattern?_eq_some_of_stereogenicByCIP (m : MoleculeGraph V)
    (h : m.GraphStereogenicByCIP) (cfg : m.GraphConfiguration) :
    m.graphCipRSPattern? cfg = some (m.graphCipRSPattern cfg) := by
  classical
  simp [graphCipRSPattern?, h, graphCipRSPatternOfResolved]

theorem graphCipRSPatternCycleCut?_eq_some_of_stereogenicByCIPCycleCut
    (m : MoleculeGraph V) (h : m.GraphStereogenicByCIPCycleCut)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSPatternCycleCut? cfg =
      some (m.graphCipRSPatternCycleCut cfg) := by
  classical
  exact
    m.detectedStereoSystem.cipRSPatternOfConfigurationCycleCut?_eq_some_of_allCentersResolvedByCIPCycleCut
      h cfg

/-! ### Preferred descriptor-facing graph aliases -/

/-- Descriptor-facing graph-level CIP-stereogenicity. -/
abbrev GraphStereogenicByCIPDescriptor (m : MoleculeGraph V) : Prop :=
  m.GraphStereogenicByCIPCycleCut

/-- Raw descriptor-facing graph-level `R/S` pattern, currently using cycle-cut CIP. -/
abbrev graphCipRSPatternDescriptor (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.GraphCipRSPattern :=
  m.graphCipRSPatternCycleCut cfg

/-- Safe descriptor-facing graph-level CIP-normalized `R/S` pattern. -/
abbrev graphCipRSPatternDescriptor? (m : MoleculeGraph V)
    (cfg : m.GraphConfiguration) : Option m.GraphCipRSPattern :=
  m.graphCipRSPatternCycleCut? cfg

theorem graphCipRSPatternDescriptor?_eq_some_of_stereogenicByCIPDescriptor
    (m : MoleculeGraph V) (h : m.GraphStereogenicByCIPDescriptor)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSPatternDescriptor? cfg = some (m.graphCipRSPatternDescriptor cfg) := by
  exact m.graphCipRSPatternCycleCut?_eq_some_of_stereogenicByCIPCycleCut h cfg

/-- The quotient class of a graph-level configuration's CIP-normalized `R/S` pattern. -/
noncomputable def graphCipRSClass (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.GraphCipRSPatternQ :=
  Quotient.mk'' (m.graphCipRSPattern cfg)

/-- The quotient class of a graph-level CIP-normalized `R/S` pattern, with explicit resolved-CIP
evidence for every detected center. -/
noncomputable def graphCipRSClassOfResolved (m : MoleculeGraph V) (h : m.GraphStereogenicByCIP)
    (cfg : m.GraphConfiguration) : m.GraphCipRSPatternQ :=
  Quotient.mk'' (m.graphCipRSPatternOfResolved h cfg)

/-- Safe graph-level CIP-normalized `R/S` quotient class. -/
noncomputable def graphCipRSClass? (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    Option m.GraphCipRSPatternQ :=
  by
    classical
    exact
      if h : m.GraphStereogenicByCIP then
        some (m.graphCipRSClassOfResolved h cfg)
      else
        none

theorem graphCipRSClass?_eq_some_of_stereogenicByCIP (m : MoleculeGraph V)
    (h : m.GraphStereogenicByCIP) (cfg : m.GraphConfiguration) :
    m.graphCipRSClass? cfg = some (m.graphCipRSClass cfg) := by
  classical
  simp [graphCipRSClass?, h, graphCipRSClassOfResolved, graphCipRSClass,
    graphCipRSPatternOfResolved]

/-- Safe graph-level cycle-cut CIP-normalized `R/S` quotient class. -/
noncomputable def graphCipRSClassCycleCut? (m : MoleculeGraph V)
    (cfg : m.GraphConfiguration) : Option m.GraphCipRSPatternQ :=
  (m.graphCipRSPatternCycleCut? cfg).map Quotient.mk''

/-- Safe descriptor-facing graph-level CIP-normalized `R/S` quotient class. -/
noncomputable def graphCipRSClassDescriptor? (m : MoleculeGraph V)
    (cfg : m.GraphConfiguration) : Option m.GraphCipRSPatternQ :=
  m.graphCipRSClassCycleCut? cfg

/-- Raw and cycle-cut keys agree at every automatically detected center. -/
abbrev GraphRawCycleCutKeyAgreement (m : MoleculeGraph V) : Prop :=
  m.detectedStereoSystem.AllCentersRawCycleCutKeyAgreement

theorem graphRawCycleCutKeyAgreement_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike) :
    m.GraphRawCycleCutKeyAgreement := by
  simpa [GraphRawCycleCutKeyAgreement, detectedStereoSystem,
    MoleculeGraph.detectedMultiCenterMolecule] using
    m.detectedStereoSystem.allCentersRawCycleCutKeyAgreement_of_treeLike htree

theorem graphStereogenicByCIP_iff_graphStereogenicByCIPCycleCut_of_rawCycleCutKeyAgreement
    (m : MoleculeGraph V) (h : m.GraphRawCycleCutKeyAgreement) :
    m.GraphStereogenicByCIP ↔ m.GraphStereogenicByCIPCycleCut := by
  constructor
  · intro hst c
    exact
      (m.detectedStereoSystem.stereogenicByCIPAt_iff_stereogenicByCIPCycleCutAt_of_rawCycleCutKeyAgreementAt
        c (h c)).1 (hst c)
  · intro hst c
    exact
      (m.detectedStereoSystem.stereogenicByCIPAt_iff_stereogenicByCIPCycleCutAt_of_rawCycleCutKeyAgreementAt
        c (h c)).2 (hst c)

theorem graphStereogenicByCIP_iff_graphStereogenicByCIPCycleCut_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike) :
    m.GraphStereogenicByCIP ↔ m.GraphStereogenicByCIPCycleCut :=
  m.graphStereogenicByCIP_iff_graphStereogenicByCIPCycleCut_of_rawCycleCutKeyAgreement
    (m.graphRawCycleCutKeyAgreement_of_treeLike htree)

theorem graphStereogenicByCIP_iff_graphStereogenicByCIPDescriptor_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike) :
    m.GraphStereogenicByCIP ↔ m.GraphStereogenicByCIPDescriptor :=
  m.graphStereogenicByCIP_iff_graphStereogenicByCIPCycleCut_of_treeLike htree

theorem graphCipRSPattern_eq_graphCipRSPatternCycleCut_of_rawCycleCutKeyAgreement
    (m : MoleculeGraph V) (h : m.GraphRawCycleCutKeyAgreement)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSPattern cfg = m.graphCipRSPatternCycleCut cfg :=
  m.detectedStereoSystem.cipRSPatternOfConfiguration_eq_cipRSPatternOfConfigurationCycleCut_of_allCentersRawCycleCutKeyAgreement
    h cfg

theorem graphCipRSPattern_eq_graphCipRSPatternCycleCut_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSPattern cfg = m.graphCipRSPatternCycleCut cfg :=
  m.graphCipRSPattern_eq_graphCipRSPatternCycleCut_of_rawCycleCutKeyAgreement
    (m.graphRawCycleCutKeyAgreement_of_treeLike htree) cfg

theorem graphCipRSPattern?_eq_none_of_not_stereogenicByCIP
    (m : MoleculeGraph V) (h : ¬ m.GraphStereogenicByCIP)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSPattern? cfg = none := by
  classical
  change
    (if h' : m.GraphStereogenicByCIP then
      some (m.graphCipRSPatternOfResolved h' cfg)
    else
      none) = none
  rw [dif_neg h]

theorem graphCipRSPatternCycleCut?_eq_none_of_not_stereogenicByCIPCycleCut
    (m : MoleculeGraph V) (h : ¬ m.GraphStereogenicByCIPCycleCut)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSPatternCycleCut? cfg = none := by
  simp [graphCipRSPatternCycleCut?, MultiCenterMolecule.cipRSPatternOfConfigurationCycleCut?,
    m.detectedStereoSystem.cipConfigurationRSCycleCut?_eq_none_of_not_allCentersResolvedByCIPCycleCut
      h cfg]

theorem graphCipRSPattern?_eq_graphCipRSPatternCycleCut?_of_rawCycleCutKeyAgreement
    (m : MoleculeGraph V) (h : m.GraphRawCycleCutKeyAgreement)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSPattern? cfg = m.graphCipRSPatternCycleCut? cfg := by
  classical
  have hst :=
    m.graphStereogenicByCIP_iff_graphStereogenicByCIPCycleCut_of_rawCycleCutKeyAgreement h
  by_cases hr : m.GraphStereogenicByCIP
  · have hrc : m.GraphStereogenicByCIPCycleCut := hst.1 hr
    rw [m.graphCipRSPattern?_eq_some_of_stereogenicByCIP hr cfg]
    rw [m.graphCipRSPatternCycleCut?_eq_some_of_stereogenicByCIPCycleCut hrc cfg]
    rw [m.graphCipRSPattern_eq_graphCipRSPatternCycleCut_of_rawCycleCutKeyAgreement h cfg]
  · have hrc : ¬ m.GraphStereogenicByCIPCycleCut := by
      intro hrc
      exact hr (hst.2 hrc)
    rw [m.graphCipRSPattern?_eq_none_of_not_stereogenicByCIP hr cfg]
    rw [m.graphCipRSPatternCycleCut?_eq_none_of_not_stereogenicByCIPCycleCut hrc cfg]

theorem graphCipRSPattern?_eq_graphCipRSPatternCycleCut?_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSPattern? cfg = m.graphCipRSPatternCycleCut? cfg :=
  m.graphCipRSPattern?_eq_graphCipRSPatternCycleCut?_of_rawCycleCutKeyAgreement
    (m.graphRawCycleCutKeyAgreement_of_treeLike htree) cfg

theorem graphCipRSPattern?_eq_graphCipRSPatternDescriptor?_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSPattern? cfg = m.graphCipRSPatternDescriptor? cfg :=
  m.graphCipRSPattern?_eq_graphCipRSPatternCycleCut?_of_treeLike htree cfg

theorem graphCipRSClass?_eq_none_of_not_stereogenicByCIP
    (m : MoleculeGraph V) (h : ¬ m.GraphStereogenicByCIP)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSClass? cfg = none := by
  classical
  change
    (if h' : m.GraphStereogenicByCIP then
      some (m.graphCipRSClassOfResolved h' cfg)
    else
      none) = none
  rw [dif_neg h]

theorem graphCipRSClassCycleCut?_eq_some_of_stereogenicByCIPCycleCut
    (m : MoleculeGraph V) (h : m.GraphStereogenicByCIPCycleCut)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSClassCycleCut? cfg = some (Quotient.mk'' (m.graphCipRSPatternCycleCut cfg)) := by
  simp [graphCipRSClassCycleCut?,
    m.graphCipRSPatternCycleCut?_eq_some_of_stereogenicByCIPCycleCut h cfg]

theorem graphCipRSClassCycleCut?_eq_none_of_not_stereogenicByCIPCycleCut
    (m : MoleculeGraph V) (h : ¬ m.GraphStereogenicByCIPCycleCut)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSClassCycleCut? cfg = none := by
  simp [graphCipRSClassCycleCut?,
    m.graphCipRSPatternCycleCut?_eq_none_of_not_stereogenicByCIPCycleCut h cfg]

theorem graphCipRSClass?_eq_graphCipRSClassCycleCut?_of_rawCycleCutKeyAgreement
    (m : MoleculeGraph V) (h : m.GraphRawCycleCutKeyAgreement)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSClass? cfg = m.graphCipRSClassCycleCut? cfg := by
  classical
  have hst :=
    m.graphStereogenicByCIP_iff_graphStereogenicByCIPCycleCut_of_rawCycleCutKeyAgreement h
  by_cases hr : m.GraphStereogenicByCIP
  · have hrc : m.GraphStereogenicByCIPCycleCut := hst.1 hr
    rw [m.graphCipRSClass?_eq_some_of_stereogenicByCIP hr cfg]
    rw [m.graphCipRSClassCycleCut?_eq_some_of_stereogenicByCIPCycleCut hrc cfg]
    simp [graphCipRSClass,
      m.graphCipRSPattern_eq_graphCipRSPatternCycleCut_of_rawCycleCutKeyAgreement h cfg]
  · have hrc : ¬ m.GraphStereogenicByCIPCycleCut := by
      intro hrc
      exact hr (hst.2 hrc)
    rw [m.graphCipRSClass?_eq_none_of_not_stereogenicByCIP hr cfg]
    rw [m.graphCipRSClassCycleCut?_eq_none_of_not_stereogenicByCIPCycleCut hrc cfg]

theorem graphCipRSClass?_eq_graphCipRSClassCycleCut?_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSClass? cfg = m.graphCipRSClassCycleCut? cfg :=
  m.graphCipRSClass?_eq_graphCipRSClassCycleCut?_of_rawCycleCutKeyAgreement
    (m.graphRawCycleCutKeyAgreement_of_treeLike htree) cfg

theorem graphCipRSClass?_eq_graphCipRSClassDescriptor?_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSClass? cfg = m.graphCipRSClassDescriptor? cfg :=
  m.graphCipRSClass?_eq_graphCipRSClassCycleCut?_of_treeLike htree cfg

theorem graphCipRSClassDescriptor?_eq_some_of_stereogenicByCIPDescriptor
    (m : MoleculeGraph V) (h : m.GraphStereogenicByCIPDescriptor)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSClassDescriptor? cfg =
      some (Quotient.mk'' (m.graphCipRSPatternDescriptor cfg)) := by
  simpa [graphCipRSClassDescriptor?, graphCipRSPatternDescriptor] using
    m.graphCipRSClassCycleCut?_eq_some_of_stereogenicByCIPCycleCut h cfg

theorem graphCipRSPattern?_eq_some_graphCipRSPatternDescriptor_of_treeLike_descriptor
    (m : MoleculeGraph V) (htree : m.TreeLike)
    (hdesc : m.GraphStereogenicByCIPDescriptor) (cfg : m.GraphConfiguration) :
    m.graphCipRSPattern? cfg = some (m.graphCipRSPatternDescriptor cfg) := by
  have hraw : m.GraphStereogenicByCIP :=
    (m.graphStereogenicByCIP_iff_graphStereogenicByCIPDescriptor_of_treeLike htree).2 hdesc
  rw [m.graphCipRSPattern?_eq_some_of_stereogenicByCIP hraw cfg]
  rw [m.graphCipRSPattern_eq_graphCipRSPatternCycleCut_of_treeLike htree cfg]

theorem graphCipRSClass?_eq_some_graphCipRSClassDescriptor_of_treeLike_descriptor
    (m : MoleculeGraph V) (htree : m.TreeLike)
    (hdesc : m.GraphStereogenicByCIPDescriptor) (cfg : m.GraphConfiguration) :
    m.graphCipRSClass? cfg =
      some (Quotient.mk'' (m.graphCipRSPatternDescriptor cfg)) := by
  have hraw : m.GraphStereogenicByCIP :=
    (m.graphStereogenicByCIP_iff_graphStereogenicByCIPDescriptor_of_treeLike htree).2 hdesc
  rw [m.graphCipRSClass?_eq_some_of_stereogenicByCIP hraw cfg]
  simp [graphCipRSClass, graphCipRSPatternDescriptor,
    m.graphCipRSPattern_eq_graphCipRSPatternCycleCut_of_treeLike htree cfg]

/-- The induced map from graph-level configuration orbits to CIP-normalized `R/S` classes. -/
noncomputable def graphCipRSClassQMap (m : MoleculeGraph V) (hst : m.GraphStereogenicByCIP) :
    m.GraphConfigurationQ → m.GraphCipRSPatternQ :=
  m.detectedStereoSystem.cipConfigurationRSQ hst

/-- The cycle-cut induced map from graph-level configuration orbits to CIP-normalized `R/S`
classes. -/
noncomputable def graphCipRSClassQMapCycleCut
    (m : MoleculeGraph V) (hst : m.GraphStereogenicByCIPCycleCut) :
    m.GraphConfigurationQ → m.GraphCipRSPatternQ :=
  m.detectedStereoSystem.cipConfigurationRSCycleCutQ hst

/-- The descriptor-facing induced map from graph-level configuration orbits to CIP-normalized
`R/S` classes. -/
abbrev graphCipRSClassQMapDescriptor
    (m : MoleculeGraph V) (hst : m.GraphStereogenicByCIPDescriptor) :
    m.GraphConfigurationQ → m.GraphCipRSPatternQ :=
  m.graphCipRSClassQMapCycleCut hst

theorem graphCipRSClassQMap_eq_graphCipRSClassQMapCycleCut_of_rawCycleCutKeyAgreement
    (m : MoleculeGraph V) (h : m.GraphRawCycleCutKeyAgreement)
    (hst : m.GraphStereogenicByCIP) :
    m.graphCipRSClassQMap hst =
      m.graphCipRSClassQMapCycleCut
        (fun c =>
          (m.detectedStereoSystem.stereogenicByCIPAt_iff_stereogenicByCIPCycleCutAt_of_rawCycleCutKeyAgreementAt
            c (h c)).1 (hst c)) := by
  simpa [graphCipRSClassQMap, graphCipRSClassQMapCycleCut] using
    m.detectedStereoSystem.cipConfigurationRSQ_eq_cipConfigurationRSCycleCutQ_of_allCentersRawCycleCutKeyAgreement
      h hst

theorem graphCipRSClassQMap_eq_graphCipRSClassQMapCycleCut_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike)
    (hst : m.GraphStereogenicByCIP) :
    m.graphCipRSClassQMap hst =
      m.graphCipRSClassQMapCycleCut
        (fun c => (m.graphStereogenicByCIP_iff_graphStereogenicByCIPCycleCut_of_treeLike
          htree).1 hst c) :=
  m.graphCipRSClassQMap_eq_graphCipRSClassQMapCycleCut_of_rawCycleCutKeyAgreement
    (m.graphRawCycleCutKeyAgreement_of_treeLike htree) hst

theorem graphCipRSClassQMap_eq_graphCipRSClassQMapDescriptor_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike)
    (hst : m.GraphStereogenicByCIP) :
    m.graphCipRSClassQMap hst =
      m.graphCipRSClassQMapDescriptor
        ((m.graphStereogenicByCIP_iff_graphStereogenicByCIPDescriptor_of_treeLike htree).1 hst) :=
  m.graphCipRSClassQMap_eq_graphCipRSClassQMapCycleCut_of_treeLike htree hst

/-- Same CIP `R/S` class for graph-level configurations. -/
abbrev GraphSameCipRSClass (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : Prop :=
  m.detectedStereoSystem.SameCipRSConfigurationClass cfg₁ cfg₂

/-- Mirror-related CIP `R/S` classes for graph-level configurations. -/
abbrev GraphMirrorCipRSClass (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : Prop :=
  m.detectedStereoSystem.MirrorCipRSConfigurationClass cfg₁ cfg₂

/-- Same descriptor-facing cycle-cut CIP `R/S` class for graph-level configurations. -/
abbrev GraphSameCipRSClassCycleCut
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : Prop :=
  m.detectedStereoSystem.SameCipRSConfigurationCycleCutClass cfg₁ cfg₂

/-- Mirror-related descriptor-facing cycle-cut CIP `R/S` classes for graph-level configurations. -/
abbrev GraphMirrorCipRSClassCycleCut
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : Prop :=
  m.detectedStereoSystem.MirrorCipRSConfigurationCycleCutClass cfg₁ cfg₂

/-- Same descriptor-facing CIP `R/S` class for graph-level configurations. -/
abbrev GraphSameCipRSClassDescriptor
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : Prop :=
  m.GraphSameCipRSClassCycleCut cfg₁ cfg₂

/-- Mirror-related descriptor-facing CIP `R/S` classes for graph-level configurations. -/
abbrev GraphMirrorCipRSClassDescriptor
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : Prop :=
  m.GraphMirrorCipRSClassCycleCut cfg₁ cfg₂

/-- Graph-level meso classification by symmetry. -/
abbrev GraphMesoBySymmetry (m : MoleculeGraph V) (cfg : m.GraphConfiguration) : Prop :=
  m.detectedStereoSystem.MesoCipRSConfigurationBySymmetry cfg

/-- Graph-level chiral classification by symmetry. -/
abbrev GraphChiralBySymmetry (m : MoleculeGraph V) (cfg : m.GraphConfiguration) : Prop :=
  m.detectedStereoSystem.ChiralCipRSConfigurationBySymmetry cfg

/-- Graph-level descriptor-facing cycle-cut meso classification by symmetry. -/
abbrev GraphMesoBySymmetryCycleCut (m : MoleculeGraph V) (cfg : m.GraphConfiguration) : Prop :=
  m.detectedStereoSystem.MesoCipRSConfigurationCycleCutBySymmetry cfg

/-- Graph-level descriptor-facing cycle-cut chiral classification by symmetry. -/
abbrev GraphChiralBySymmetryCycleCut (m : MoleculeGraph V) (cfg : m.GraphConfiguration) : Prop :=
  m.detectedStereoSystem.ChiralCipRSConfigurationCycleCutBySymmetry cfg

/-- Descriptor-facing graph-level meso classification by symmetry. -/
abbrev GraphMesoBySymmetryDescriptor (m : MoleculeGraph V) (cfg : m.GraphConfiguration) : Prop :=
  m.GraphMesoBySymmetryCycleCut cfg

/-- Descriptor-facing graph-level chiral classification by symmetry. -/
abbrev GraphChiralBySymmetryDescriptor (m : MoleculeGraph V) (cfg : m.GraphConfiguration) : Prop :=
  m.GraphChiralBySymmetryCycleCut cfg

/-- Graph-level enantiomeric relation by CIP `R/S` classes. -/
abbrev GraphEnantiomericBySymmetry (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) :
    Prop :=
  m.detectedStereoSystem.EnantiomericCipRSConfigurationsBySymmetry cfg₁ cfg₂

/-- Graph-level diastereomeric relation by CIP `R/S` classes. -/
abbrev GraphDiastereomericBySymmetry (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) :
    Prop :=
  m.detectedStereoSystem.DiastereomericCipRSConfigurationsBySymmetry cfg₁ cfg₂

/-- Graph-level descriptor-facing cycle-cut enantiomeric relation by CIP `R/S` classes. -/
abbrev GraphEnantiomericBySymmetryCycleCut
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : Prop :=
  m.detectedStereoSystem.EnantiomericCipRSConfigurationsCycleCutBySymmetry cfg₁ cfg₂

/-- Graph-level descriptor-facing cycle-cut diastereomeric relation by CIP `R/S` classes. -/
abbrev GraphDiastereomericBySymmetryCycleCut
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : Prop :=
  m.detectedStereoSystem.DiastereomericCipRSConfigurationsCycleCutBySymmetry cfg₁ cfg₂

/-- Graph-level descriptor-facing enantiomeric relation by CIP `R/S` classes. -/
abbrev GraphEnantiomericBySymmetryDescriptor
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : Prop :=
  m.GraphEnantiomericBySymmetryCycleCut cfg₁ cfg₂

/-- Graph-level descriptor-facing diastereomeric relation by CIP `R/S` classes. -/
abbrev GraphDiastereomericBySymmetryDescriptor
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : Prop :=
  m.GraphDiastereomericBySymmetryCycleCut cfg₁ cfg₂

theorem graphSameCipRSClass_iff_cycleCut_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike) (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.GraphSameCipRSClass cfg₁ cfg₂ ↔ m.GraphSameCipRSClassCycleCut cfg₁ cfg₂ := by
  have hsys : m.detectedStereoSystem.mol.TreeLike := by
    simpa [detectedStereoSystem, MoleculeGraph.detectedMultiCenterMolecule] using htree
  simpa [GraphSameCipRSClass, GraphSameCipRSClassCycleCut] using
    m.detectedStereoSystem.sameCipRSConfigurationClass_iff_cycleCut_of_treeLike hsys cfg₁ cfg₂

theorem graphMirrorCipRSClass_iff_cycleCut_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike) (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.GraphMirrorCipRSClass cfg₁ cfg₂ ↔ m.GraphMirrorCipRSClassCycleCut cfg₁ cfg₂ := by
  have hsys : m.detectedStereoSystem.mol.TreeLike := by
    simpa [detectedStereoSystem, MoleculeGraph.detectedMultiCenterMolecule] using htree
  simpa [GraphMirrorCipRSClass, GraphMirrorCipRSClassCycleCut] using
    m.detectedStereoSystem.mirrorCipRSConfigurationClass_iff_cycleCut_of_treeLike hsys cfg₁ cfg₂

theorem graphMesoBySymmetry_iff_cycleCut_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike) (cfg : m.GraphConfiguration) :
    m.GraphMesoBySymmetry cfg ↔ m.GraphMesoBySymmetryCycleCut cfg := by
  have hsys : m.detectedStereoSystem.mol.TreeLike := by
    simpa [detectedStereoSystem, MoleculeGraph.detectedMultiCenterMolecule] using htree
  simpa [GraphMesoBySymmetry, GraphMesoBySymmetryCycleCut] using
    m.detectedStereoSystem.mesoCipRSConfigurationBySymmetry_iff_cycleCut_of_treeLike hsys cfg

theorem graphChiralBySymmetry_iff_cycleCut_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike) (cfg : m.GraphConfiguration) :
    m.GraphChiralBySymmetry cfg ↔ m.GraphChiralBySymmetryCycleCut cfg := by
  have hsys : m.detectedStereoSystem.mol.TreeLike := by
    simpa [detectedStereoSystem, MoleculeGraph.detectedMultiCenterMolecule] using htree
  simpa [GraphChiralBySymmetry, GraphChiralBySymmetryCycleCut] using
    m.detectedStereoSystem.chiralCipRSConfigurationBySymmetry_iff_cycleCut_of_treeLike hsys cfg

theorem graphEnantiomericBySymmetry_iff_cycleCut_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike) (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.GraphEnantiomericBySymmetry cfg₁ cfg₂ ↔
      m.GraphEnantiomericBySymmetryCycleCut cfg₁ cfg₂ := by
  have hsys : m.detectedStereoSystem.mol.TreeLike := by
    simpa [detectedStereoSystem, MoleculeGraph.detectedMultiCenterMolecule] using htree
  simpa [GraphEnantiomericBySymmetry, GraphEnantiomericBySymmetryCycleCut] using
    m.detectedStereoSystem.enantiomericCipRSConfigurationsBySymmetry_iff_cycleCut_of_treeLike
      hsys cfg₁ cfg₂

theorem graphDiastereomericBySymmetry_iff_cycleCut_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike) (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.GraphDiastereomericBySymmetry cfg₁ cfg₂ ↔
      m.GraphDiastereomericBySymmetryCycleCut cfg₁ cfg₂ := by
  have hsys : m.detectedStereoSystem.mol.TreeLike := by
    simpa [detectedStereoSystem, MoleculeGraph.detectedMultiCenterMolecule] using htree
  simpa [GraphDiastereomericBySymmetry, GraphDiastereomericBySymmetryCycleCut] using
    m.detectedStereoSystem.diastereomericCipRSConfigurationsBySymmetry_iff_cycleCut_of_treeLike
      hsys cfg₁ cfg₂

theorem graphCipRSClassification_exhaustive
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.GraphSameCipRSClass cfg₁ cfg₂ ∨
      m.GraphEnantiomericBySymmetry cfg₁ cfg₂ ∨
        m.GraphDiastereomericBySymmetry cfg₁ cfg₂ := by
  simpa [GraphSameCipRSClass, GraphEnantiomericBySymmetry,
    GraphDiastereomericBySymmetry] using
    m.detectedStereoSystem.cipRSConfiguration_classification_exhaustive cfg₁ cfg₂

theorem graphCipRSCycleCutClassification_exhaustive
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.GraphSameCipRSClassCycleCut cfg₁ cfg₂ ∨
      m.GraphEnantiomericBySymmetryCycleCut cfg₁ cfg₂ ∨
        m.GraphDiastereomericBySymmetryCycleCut cfg₁ cfg₂ := by
  simpa [GraphSameCipRSClassCycleCut, GraphEnantiomericBySymmetryCycleCut,
    GraphDiastereomericBySymmetryCycleCut] using
    m.detectedStereoSystem.cipRSConfigurationCycleCut_classification_exhaustive cfg₁ cfg₂

theorem graphCipRSDescriptorClassification_exhaustive
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.GraphSameCipRSClassCycleCut cfg₁ cfg₂ ∨
      m.GraphEnantiomericBySymmetryCycleCut cfg₁ cfg₂ ∨
        m.GraphDiastereomericBySymmetryCycleCut cfg₁ cfg₂ :=
  m.graphCipRSCycleCutClassification_exhaustive cfg₁ cfg₂

theorem graphEnantiomeric_or_diastereomeric_iff_not_same
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.GraphEnantiomericBySymmetry cfg₁ cfg₂ ∨
        m.GraphDiastereomericBySymmetry cfg₁ cfg₂ ↔
      ¬ m.GraphSameCipRSClass cfg₁ cfg₂ := by
  simpa [GraphSameCipRSClass, GraphEnantiomericBySymmetry,
    GraphDiastereomericBySymmetry] using
    m.detectedStereoSystem.cipRSConfiguration_enantiomeric_or_diastereomeric_iff_not_same
      cfg₁ cfg₂

theorem graphCycleCutEnantiomeric_or_diastereomeric_iff_not_same
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.GraphEnantiomericBySymmetryCycleCut cfg₁ cfg₂ ∨
        m.GraphDiastereomericBySymmetryCycleCut cfg₁ cfg₂ ↔
      ¬ m.GraphSameCipRSClassCycleCut cfg₁ cfg₂ := by
  simpa [GraphSameCipRSClassCycleCut, GraphEnantiomericBySymmetryCycleCut,
    GraphDiastereomericBySymmetryCycleCut] using
    m.detectedStereoSystem.cipRSConfigurationCycleCut_enantiomeric_or_diastereomeric_iff_not_same
      cfg₁ cfg₂

theorem graphDescriptorEnantiomeric_or_diastereomeric_iff_not_same
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.GraphEnantiomericBySymmetryCycleCut cfg₁ cfg₂ ∨
        m.GraphDiastereomericBySymmetryCycleCut cfg₁ cfg₂ ↔
      ¬ m.GraphSameCipRSClassCycleCut cfg₁ cfg₂ :=
  m.graphCycleCutEnantiomeric_or_diastereomeric_iff_not_same cfg₁ cfg₂

/-- Interpret a concrete relation outcome as a proposition about graph-level raw CIP `R/S`
classes. -/
def GraphCipRSClassificationHolds
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : CipRSClassRelation → Prop
  | .same => m.GraphSameCipRSClass cfg₁ cfg₂
  | .enantiomeric => m.GraphEnantiomericBySymmetry cfg₁ cfg₂
  | .diastereomeric => m.GraphDiastereomericBySymmetry cfg₁ cfg₂

/-- Interpret a concrete relation outcome as a proposition about graph-level descriptor-facing CIP
`R/S` classes. -/
def GraphCipRSDescriptorClassificationHolds
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : CipRSClassRelation → Prop
  | .same => m.GraphSameCipRSClassDescriptor cfg₁ cfg₂
  | .enantiomeric => m.GraphEnantiomericBySymmetryDescriptor cfg₁ cfg₂
  | .diastereomeric => m.GraphDiastereomericBySymmetryDescriptor cfg₁ cfg₂

/-- Concrete classifier for graph-level raw CIP `R/S` classes. -/
noncomputable def graphCipRSClassifier
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : CipRSClassRelation :=
  m.detectedStereoSystem.classifyCipRSConfiguration cfg₁ cfg₂

/-- Concrete classifier for graph-level descriptor-facing CIP `R/S` classes. -/
noncomputable def graphCipRSDescriptorClassifier
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : CipRSClassRelation :=
  m.detectedStereoSystem.classifyCipRSConfigurationCycleCut cfg₁ cfg₂

/-- Safe descriptor-facing graph classifier: refuses to classify unless every detected center has
resolved descriptor priorities. -/
noncomputable def graphCipRSDescriptorClassifier?
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : Option CipRSClassRelation :=
  by
    classical
    exact
      if _ : m.GraphStereogenicByCIPDescriptor then
        some (m.graphCipRSDescriptorClassifier cfg₁ cfg₂)
      else
        none

theorem graphCipRSClassifier_sound
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.GraphCipRSClassificationHolds cfg₁ cfg₂
      (m.graphCipRSClassifier cfg₁ cfg₂) := by
  simpa [graphCipRSClassifier, GraphCipRSClassificationHolds, GraphSameCipRSClass,
    GraphEnantiomericBySymmetry, GraphDiastereomericBySymmetry] using
    m.detectedStereoSystem.classifyCipRSConfiguration_sound cfg₁ cfg₂

theorem graphCipRSDescriptorClassifier_sound
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.GraphCipRSDescriptorClassificationHolds cfg₁ cfg₂
      (m.graphCipRSDescriptorClassifier cfg₁ cfg₂) := by
  simpa [graphCipRSDescriptorClassifier, GraphCipRSDescriptorClassificationHolds,
    GraphSameCipRSClassDescriptor, GraphEnantiomericBySymmetryDescriptor,
    GraphDiastereomericBySymmetryDescriptor, GraphSameCipRSClassCycleCut,
    GraphEnantiomericBySymmetryCycleCut, GraphDiastereomericBySymmetryCycleCut] using
    m.detectedStereoSystem.classifyCipRSConfigurationCycleCut_sound cfg₁ cfg₂

theorem graphCipRSDescriptorClassifier?_eq_some_of_stereogenicByCIPDescriptor
    (m : MoleculeGraph V) (h : m.GraphStereogenicByCIPDescriptor)
    (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.graphCipRSDescriptorClassifier? cfg₁ cfg₂ =
      some (m.graphCipRSDescriptorClassifier cfg₁ cfg₂) := by
  classical
  simp [graphCipRSDescriptorClassifier?, h]

theorem graphCipRSClassifier_self_same
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.graphCipRSClassifier cfg cfg = CipRSClassRelation.same := by
  classical
  simpa [graphCipRSClassifier] using
    (m.detectedStereoSystem.classifyCipRSConfiguration_self_same cfg)

theorem graphCipRSClassifier_self_same_sound
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.GraphCipRSClassificationHolds cfg cfg CipRSClassRelation.same := by
  have hsound := m.graphCipRSClassifier_sound cfg cfg
  simpa [m.graphCipRSClassifier_self_same cfg] using hsound

theorem graphCipRSDescriptorClassifier_self_same
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.graphCipRSDescriptorClassifier cfg cfg = CipRSClassRelation.same := by
  classical
  simpa [graphCipRSDescriptorClassifier] using
    (m.detectedStereoSystem.classifyCipRSConfigurationCycleCut_self_same cfg)

theorem graphCipRSDescriptorClassifier_self_same_sound
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.GraphCipRSDescriptorClassificationHolds cfg cfg CipRSClassRelation.same := by
  have hsound := m.graphCipRSDescriptorClassifier_sound cfg cfg
  simpa [m.graphCipRSDescriptorClassifier_self_same cfg] using hsound

theorem graphCipRSDescriptorClassifier?_eq_some_same_of_stereogenicByCIPDescriptor_self
    (m : MoleculeGraph V) (h : m.GraphStereogenicByCIPDescriptor)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSDescriptorClassifier? cfg cfg = some CipRSClassRelation.same := by
  have hsafe := m.graphCipRSDescriptorClassifier?_eq_some_of_stereogenicByCIPDescriptor h cfg cfg
  simpa [m.graphCipRSDescriptorClassifier_self_same cfg] using hsafe

theorem graphCipRSDescriptorClassifier_self_mirror_same_of_meso
    (m : MoleculeGraph V) {cfg : m.GraphConfiguration}
    (h : m.GraphMesoBySymmetryDescriptor cfg) :
    m.graphCipRSDescriptorClassifier cfg
      (m.detectedStereoSystem.mirrorConfiguration cfg) = CipRSClassRelation.same := by
  classical
  simpa [graphCipRSDescriptorClassifier] using
    (m.detectedStereoSystem.classifyCipRSConfigurationCycleCut_self_mirror_same_of_meso
      (cfg := cfg) h)

theorem graphCipRSDescriptorClassifier_self_mirror_same_sound_of_meso
    (m : MoleculeGraph V) {cfg : m.GraphConfiguration}
    (h : m.GraphMesoBySymmetryDescriptor cfg) :
    m.GraphCipRSDescriptorClassificationHolds cfg
      (m.detectedStereoSystem.mirrorConfiguration cfg) CipRSClassRelation.same := by
  have hsound :=
    m.graphCipRSDescriptorClassifier_sound cfg (m.detectedStereoSystem.mirrorConfiguration cfg)
  simpa [m.graphCipRSDescriptorClassifier_self_mirror_same_of_meso h] using hsound

theorem graphCipRSDescriptorClassifier?_eq_some_same_of_stereogenicByCIPDescriptor_self_mirror
    (m : MoleculeGraph V) (hresolved : m.GraphStereogenicByCIPDescriptor)
    {cfg : m.GraphConfiguration} (hmeso : m.GraphMesoBySymmetryDescriptor cfg) :
    m.graphCipRSDescriptorClassifier? cfg (m.detectedStereoSystem.mirrorConfiguration cfg) =
      some CipRSClassRelation.same := by
  have hsafe :=
    m.graphCipRSDescriptorClassifier?_eq_some_of_stereogenicByCIPDescriptor hresolved cfg
      (m.detectedStereoSystem.mirrorConfiguration cfg)
  simpa [m.graphCipRSDescriptorClassifier_self_mirror_same_of_meso hmeso] using hsafe

theorem graphCipRSDescriptorClassifier_self_mirror_enantiomeric_of_chiral
    (m : MoleculeGraph V) {cfg : m.GraphConfiguration}
    (h : m.GraphChiralBySymmetryDescriptor cfg) :
    m.graphCipRSDescriptorClassifier cfg
      (m.detectedStereoSystem.mirrorConfiguration cfg) = CipRSClassRelation.enantiomeric := by
  classical
  simpa [graphCipRSDescriptorClassifier] using
    (m.detectedStereoSystem.classifyCipRSConfigurationCycleCut_self_mirror_enantiomeric_of_chiral
      (cfg := cfg) h)

theorem graphCipRSDescriptorClassifier_self_mirror_enantiomeric_sound_of_chiral
    (m : MoleculeGraph V) {cfg : m.GraphConfiguration}
    (h : m.GraphChiralBySymmetryDescriptor cfg) :
    m.GraphCipRSDescriptorClassificationHolds cfg
      (m.detectedStereoSystem.mirrorConfiguration cfg) CipRSClassRelation.enantiomeric := by
  have hsound :=
    m.graphCipRSDescriptorClassifier_sound cfg (m.detectedStereoSystem.mirrorConfiguration cfg)
  simpa [m.graphCipRSDescriptorClassifier_self_mirror_enantiomeric_of_chiral h] using hsound

theorem graphCipRSDescriptorClassifier?_eq_some_enantiomeric_of_stereogenicByCIPDescriptor_self_mirror
    (m : MoleculeGraph V) (hresolved : m.GraphStereogenicByCIPDescriptor)
    {cfg : m.GraphConfiguration} (hchiral : m.GraphChiralBySymmetryDescriptor cfg) :
    m.graphCipRSDescriptorClassifier? cfg (m.detectedStereoSystem.mirrorConfiguration cfg) =
      some CipRSClassRelation.enantiomeric := by
  have hsafe :=
    m.graphCipRSDescriptorClassifier?_eq_some_of_stereogenicByCIPDescriptor hresolved cfg
      (m.detectedStereoSystem.mirrorConfiguration cfg)
  simpa [m.graphCipRSDescriptorClassifier_self_mirror_enantiomeric_of_chiral hchiral] using hsafe

/-- Exactly one graph-level raw CIP `R/S` relation holds between two configurations. -/
def GraphCipRSClassificationExactlyOne
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : Prop :=
  (m.GraphSameCipRSClass cfg₁ cfg₂ ∧
      ¬ m.GraphEnantiomericBySymmetry cfg₁ cfg₂ ∧
      ¬ m.GraphDiastereomericBySymmetry cfg₁ cfg₂) ∨
    (m.GraphEnantiomericBySymmetry cfg₁ cfg₂ ∧
      ¬ m.GraphSameCipRSClass cfg₁ cfg₂ ∧
      ¬ m.GraphDiastereomericBySymmetry cfg₁ cfg₂) ∨
    (m.GraphDiastereomericBySymmetry cfg₁ cfg₂ ∧
      ¬ m.GraphSameCipRSClass cfg₁ cfg₂ ∧
      ¬ m.GraphEnantiomericBySymmetry cfg₁ cfg₂)

/-- Exactly one graph-level descriptor-facing cycle-cut CIP `R/S` relation holds between two
configurations. -/
def GraphCipRSCycleCutClassificationExactlyOne
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : Prop :=
  (m.GraphSameCipRSClassCycleCut cfg₁ cfg₂ ∧
      ¬ m.GraphEnantiomericBySymmetryCycleCut cfg₁ cfg₂ ∧
      ¬ m.GraphDiastereomericBySymmetryCycleCut cfg₁ cfg₂) ∨
    (m.GraphEnantiomericBySymmetryCycleCut cfg₁ cfg₂ ∧
      ¬ m.GraphSameCipRSClassCycleCut cfg₁ cfg₂ ∧
      ¬ m.GraphDiastereomericBySymmetryCycleCut cfg₁ cfg₂) ∨
    (m.GraphDiastereomericBySymmetryCycleCut cfg₁ cfg₂ ∧
      ¬ m.GraphSameCipRSClassCycleCut cfg₁ cfg₂ ∧
      ¬ m.GraphEnantiomericBySymmetryCycleCut cfg₁ cfg₂)

/-- Exactly one graph-level descriptor-facing CIP `R/S` relation holds between two
configurations. -/
abbrev GraphCipRSDescriptorClassificationExactlyOne
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : Prop :=
  m.GraphCipRSCycleCutClassificationExactlyOne cfg₁ cfg₂

theorem graphCipRSClassification_exactly_one
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.GraphCipRSClassificationExactlyOne cfg₁ cfg₂ := by
  simpa [GraphCipRSClassificationExactlyOne, GraphSameCipRSClass,
    GraphEnantiomericBySymmetry, GraphDiastereomericBySymmetry] using
    m.detectedStereoSystem.cipRSConfiguration_classification_exactly_one cfg₁ cfg₂

theorem graphCipRSCycleCutClassification_exactly_one
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.GraphCipRSCycleCutClassificationExactlyOne cfg₁ cfg₂ := by
  simpa [GraphCipRSCycleCutClassificationExactlyOne, GraphSameCipRSClassCycleCut,
    GraphEnantiomericBySymmetryCycleCut, GraphDiastereomericBySymmetryCycleCut] using
    m.detectedStereoSystem.cipRSConfigurationCycleCut_classification_exactly_one cfg₁ cfg₂

theorem graphCipRSDescriptorClassification_exactly_one
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.GraphCipRSDescriptorClassificationExactlyOne cfg₁ cfg₂ :=
  m.graphCipRSCycleCutClassification_exactly_one cfg₁ cfg₂

@[simp] theorem graphCipRSPattern_mirrorConfiguration (m : MoleculeGraph V)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSPattern (m.detectedStereoSystem.mirrorConfiguration cfg) =
      -m.graphCipRSPattern cfg :=
  m.detectedStereoSystem.cipRSPatternOfConfiguration_mirrorConfiguration cfg

@[simp] theorem graphCipRSPatternCycleCut_mirrorConfiguration
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.graphCipRSPatternCycleCut (m.detectedStereoSystem.mirrorConfiguration cfg) =
      -m.graphCipRSPatternCycleCut cfg :=
  m.detectedStereoSystem.cipRSPatternOfConfigurationCycleCut_mirrorConfiguration cfg

theorem graphCipRSPattern_smul_eq_of_stereogenicByCIP (m : MoleculeGraph V)
    (hst : m.GraphStereogenicByCIP) (e : m.GraphStereoAut) (cfg : m.GraphConfiguration) :
    e • m.graphCipRSPattern cfg = m.graphCipRSPattern (e • cfg) :=
  m.detectedStereoSystem.cipRSPatternOfConfiguration_smul_eq_of_stereogenicByCIPAt
    (hst := hst) (e := e) (cfg := cfg)

theorem graphCipRSPatternCycleCut_smul_eq_of_stereogenicByCIPCycleCut
    (m : MoleculeGraph V) (hst : m.GraphStereogenicByCIPCycleCut)
    (e : m.GraphStereoAut) (cfg : m.GraphConfiguration) :
    e • m.graphCipRSPatternCycleCut cfg = m.graphCipRSPatternCycleCut (e • cfg) :=
  m.detectedStereoSystem.cipRSPatternOfConfigurationCycleCut_smul_eq_of_stereogenicByCIPCycleCutAt
    (hst := hst) (e := e) (cfg := cfg)

theorem graphMesoBySymmetry_iff_exists_smul_eq_mirror (m : MoleculeGraph V)
    (hst : m.GraphStereogenicByCIP) (cfg : m.GraphConfiguration) :
    m.GraphMesoBySymmetry cfg ↔
      ∃ e : m.GraphStereoAut,
        m.graphCipRSPattern (e • cfg) =
          m.graphCipRSPattern (m.detectedStereoSystem.mirrorConfiguration cfg) :=
  m.detectedStereoSystem.mesoCipRSConfigurationBySymmetry_iff_exists_smul_eq_mirror
    (hst := hst) (cfg := cfg)

theorem graphChiralBySymmetry_iff_forall_smul_ne_mirror (m : MoleculeGraph V)
    (hst : m.GraphStereogenicByCIP) (cfg : m.GraphConfiguration) :
    m.GraphChiralBySymmetry cfg ↔
      ∀ e : m.GraphStereoAut,
        m.graphCipRSPattern (e • cfg) ≠
          m.graphCipRSPattern (m.detectedStereoSystem.mirrorConfiguration cfg) :=
  m.detectedStereoSystem.chiralCipRSConfigurationBySymmetry_iff_forall_smul_ne_mirror
    (hst := hst) (cfg := cfg)

theorem graphMesoBySymmetryCycleCut_iff_exists_smul_eq_mirror
    (m : MoleculeGraph V) (hst : m.GraphStereogenicByCIPCycleCut)
    (cfg : m.GraphConfiguration) :
    m.GraphMesoBySymmetryCycleCut cfg ↔
      ∃ e : m.GraphStereoAut,
        m.graphCipRSPatternCycleCut (e • cfg) =
          m.graphCipRSPatternCycleCut (m.detectedStereoSystem.mirrorConfiguration cfg) :=
  m.detectedStereoSystem.mesoCipRSConfigurationCycleCutBySymmetry_iff_exists_smul_eq_mirror
    (hst := hst) (cfg := cfg)

theorem graphChiralBySymmetryCycleCut_iff_forall_smul_ne_mirror
    (m : MoleculeGraph V) (hst : m.GraphStereogenicByCIPCycleCut)
    (cfg : m.GraphConfiguration) :
    m.GraphChiralBySymmetryCycleCut cfg ↔
      ∀ e : m.GraphStereoAut,
        m.graphCipRSPatternCycleCut (e • cfg) ≠
          m.graphCipRSPatternCycleCut (m.detectedStereoSystem.mirrorConfiguration cfg) :=
  m.detectedStereoSystem.chiralCipRSConfigurationCycleCutBySymmetry_iff_forall_smul_ne_mirror
    (hst := hst) (cfg := cfg)

theorem graphMesoBySymmetry_iff_not_chiral
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.GraphMesoBySymmetry cfg ↔ ¬ m.GraphChiralBySymmetry cfg :=
  m.detectedStereoSystem.mesoCipRSConfigurationBySymmetry_iff_not_chiral cfg

theorem graphChiralBySymmetry_iff_not_meso
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.GraphChiralBySymmetry cfg ↔ ¬ m.GraphMesoBySymmetry cfg :=
  m.detectedStereoSystem.chiralCipRSConfigurationBySymmetry_iff_not_meso cfg

theorem graphMesoBySymmetryCycleCut_iff_not_chiral
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.GraphMesoBySymmetryCycleCut cfg ↔ ¬ m.GraphChiralBySymmetryCycleCut cfg :=
  m.detectedStereoSystem.mesoCipRSConfigurationCycleCutBySymmetry_iff_not_chiral cfg

theorem graphChiralBySymmetryCycleCut_iff_not_meso
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.GraphChiralBySymmetryCycleCut cfg ↔ ¬ m.GraphMesoBySymmetryCycleCut cfg :=
  m.detectedStereoSystem.chiralCipRSConfigurationCycleCutBySymmetry_iff_not_meso cfg

theorem graphMesoBySymmetryDescriptor_iff_not_chiral
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.GraphMesoBySymmetryDescriptor cfg ↔ ¬ m.GraphChiralBySymmetryDescriptor cfg :=
  m.graphMesoBySymmetryCycleCut_iff_not_chiral cfg

theorem graphChiralBySymmetryDescriptor_iff_not_meso
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.GraphChiralBySymmetryDescriptor cfg ↔ ¬ m.GraphMesoBySymmetryDescriptor cfg :=
  m.graphChiralBySymmetryCycleCut_iff_not_meso cfg

/-- Interpret a concrete chirality outcome as a descriptor-facing graph chirality proposition. -/
def GraphDescriptorChiralityHolds
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) : CipRSChirality → Prop
  | .meso => m.GraphMesoBySymmetryDescriptor cfg
  | .chiral => m.GraphChiralBySymmetryDescriptor cfg

/-- Concrete descriptor-facing graph chirality classifier. -/
noncomputable def graphCipRSDescriptorChiralityClassifier
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) : CipRSChirality :=
  by
    classical
    exact
      if m.GraphMesoBySymmetryDescriptor cfg then
        .meso
      else
        .chiral

/-- Safe descriptor-facing graph chirality classifier: refuses to classify unless every detected
center has resolved descriptor priorities. -/
noncomputable def graphCipRSDescriptorChiralityClassifier?
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) : Option CipRSChirality :=
  by
    classical
    exact
      if _ : m.GraphStereogenicByCIPDescriptor then
        some (m.graphCipRSDescriptorChiralityClassifier cfg)
      else
        none

theorem graphCipRSDescriptorChiralityClassifier_sound
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.GraphDescriptorChiralityHolds cfg
      (m.graphCipRSDescriptorChiralityClassifier cfg) := by
  classical
  unfold graphCipRSDescriptorChiralityClassifier GraphDescriptorChiralityHolds
  by_cases hmeso : m.GraphMesoBySymmetryDescriptor cfg
  · simp [hmeso]
  · have hchiral : m.GraphChiralBySymmetryDescriptor cfg :=
      (m.graphChiralBySymmetryDescriptor_iff_not_meso cfg).2 hmeso
    simp [hmeso, hchiral]

theorem graphCipRSDescriptorChiralityClassifier?_eq_some_of_stereogenicByCIPDescriptor
    (m : MoleculeGraph V) (h : m.GraphStereogenicByCIPDescriptor)
    (cfg : m.GraphConfiguration) :
    m.graphCipRSDescriptorChiralityClassifier? cfg =
      some (m.graphCipRSDescriptorChiralityClassifier cfg) := by
  classical
  simp [graphCipRSDescriptorChiralityClassifier?, h]

/-- A bundled end-to-end certificate for the graph-level descriptor stereochemistry pipeline.

Under the flagship theorem below, tree-like graphs with descriptor-resolved detected centers have
total safe descriptor endpoints and an exact descriptor classification for any two configurations. -/
structure GraphDescriptorPipelineCertificate
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : Prop where
  rawPatternLeft :
    m.graphCipRSPattern? cfg₁ = some (m.graphCipRSPatternDescriptor cfg₁)
  rawPatternRight :
    m.graphCipRSPattern? cfg₂ = some (m.graphCipRSPatternDescriptor cfg₂)
  descriptorPatternLeft :
    m.graphCipRSPatternDescriptor? cfg₁ = some (m.graphCipRSPatternDescriptor cfg₁)
  descriptorPatternRight :
    m.graphCipRSPatternDescriptor? cfg₂ = some (m.graphCipRSPatternDescriptor cfg₂)
  rawClassLeft :
    m.graphCipRSClass? cfg₁ = some (Quotient.mk'' (m.graphCipRSPatternDescriptor cfg₁))
  rawClassRight :
    m.graphCipRSClass? cfg₂ = some (Quotient.mk'' (m.graphCipRSPatternDescriptor cfg₂))
  descriptorClassLeft :
    m.graphCipRSClassDescriptor? cfg₁ =
      some (Quotient.mk'' (m.graphCipRSPatternDescriptor cfg₁))
  descriptorClassRight :
    m.graphCipRSClassDescriptor? cfg₂ =
      some (Quotient.mk'' (m.graphCipRSPatternDescriptor cfg₂))
  classification :
    m.GraphCipRSDescriptorClassificationExactlyOne cfg₁ cfg₂
  mesoChiralLeft :
    m.GraphMesoBySymmetryDescriptor cfg₁ ↔ ¬ m.GraphChiralBySymmetryDescriptor cfg₁
  mesoChiralRight :
    m.GraphMesoBySymmetryDescriptor cfg₂ ↔ ¬ m.GraphChiralBySymmetryDescriptor cfg₂

theorem treeLike_graphDescriptorPipelineCertificate
    (m : MoleculeGraph V) (htree : m.TreeLike)
    (hdesc : m.GraphStereogenicByCIPDescriptor)
    (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.GraphDescriptorPipelineCertificate cfg₁ cfg₂ where
  rawPatternLeft :=
    m.graphCipRSPattern?_eq_some_graphCipRSPatternDescriptor_of_treeLike_descriptor
      htree hdesc cfg₁
  rawPatternRight :=
    m.graphCipRSPattern?_eq_some_graphCipRSPatternDescriptor_of_treeLike_descriptor
      htree hdesc cfg₂
  descriptorPatternLeft :=
    m.graphCipRSPatternDescriptor?_eq_some_of_stereogenicByCIPDescriptor hdesc cfg₁
  descriptorPatternRight :=
    m.graphCipRSPatternDescriptor?_eq_some_of_stereogenicByCIPDescriptor hdesc cfg₂
  rawClassLeft :=
    m.graphCipRSClass?_eq_some_graphCipRSClassDescriptor_of_treeLike_descriptor
      htree hdesc cfg₁
  rawClassRight :=
    m.graphCipRSClass?_eq_some_graphCipRSClassDescriptor_of_treeLike_descriptor
      htree hdesc cfg₂
  descriptorClassLeft :=
    m.graphCipRSClassDescriptor?_eq_some_of_stereogenicByCIPDescriptor hdesc cfg₁
  descriptorClassRight :=
    m.graphCipRSClassDescriptor?_eq_some_of_stereogenicByCIPDescriptor hdesc cfg₂
  classification :=
    m.graphCipRSDescriptorClassification_exactly_one cfg₁ cfg₂
  mesoChiralLeft :=
    m.graphMesoBySymmetryDescriptor_iff_not_chiral cfg₁
  mesoChiralRight :=
    m.graphMesoBySymmetryDescriptor_iff_not_chiral cfg₂

/-- A proof-carrying graph descriptor classification result.

It contains the concrete classifier output, proof that the safe classifier returns that output,
proof that the output denotes the correct stereochemical relation, and the full endpoint/pipeline
certificate. -/
structure GraphDescriptorClassifierCertificate
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration) : Type where
  outcome : CipRSClassRelation
  classifierValue :
    m.graphCipRSDescriptorClassifier? cfg₁ cfg₂ = some outcome
  sound :
    m.GraphCipRSDescriptorClassificationHolds cfg₁ cfg₂ outcome
  pipeline :
    m.GraphDescriptorPipelineCertificate cfg₁ cfg₂

/-- End-to-end certified descriptor classifier for tree-like, descriptor-resolved molecular graphs. -/
def treeLike_graphDescriptorClassifierCertificate
    (m : MoleculeGraph V) (htree : m.TreeLike)
    (hdesc : m.GraphStereogenicByCIPDescriptor)
    (cfg₁ cfg₂ : m.GraphConfiguration) :
    m.GraphDescriptorClassifierCertificate cfg₁ cfg₂ where
  outcome := m.graphCipRSDescriptorClassifier cfg₁ cfg₂
  classifierValue :=
    m.graphCipRSDescriptorClassifier?_eq_some_of_stereogenicByCIPDescriptor hdesc cfg₁ cfg₂
  sound :=
    m.graphCipRSDescriptorClassifier_sound cfg₁ cfg₂
  pipeline :=
    m.treeLike_graphDescriptorPipelineCertificate htree hdesc cfg₁ cfg₂

/-- A proof-carrying descriptor chirality result for one graph configuration. -/
structure GraphDescriptorChiralityCertificate
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) : Type where
  outcome : CipRSChirality
  classifierValue :
    m.graphCipRSDescriptorChiralityClassifier? cfg = some outcome
  sound :
    m.GraphDescriptorChiralityHolds cfg outcome
  rawPattern :
    m.graphCipRSPattern? cfg = some (m.graphCipRSPatternDescriptor cfg)
  descriptorPattern :
    m.graphCipRSPatternDescriptor? cfg = some (m.graphCipRSPatternDescriptor cfg)
  rawClass :
    m.graphCipRSClass? cfg = some (Quotient.mk'' (m.graphCipRSPatternDescriptor cfg))
  descriptorClass :
    m.graphCipRSClassDescriptor? cfg =
      some (Quotient.mk'' (m.graphCipRSPatternDescriptor cfg))
  complement :
    m.GraphMesoBySymmetryDescriptor cfg ↔ ¬ m.GraphChiralBySymmetryDescriptor cfg

/-- End-to-end certified descriptor chirality classifier for one tree-like, descriptor-resolved
graph configuration. -/
def treeLike_graphDescriptorChiralityCertificate
    (m : MoleculeGraph V) (htree : m.TreeLike)
    (hdesc : m.GraphStereogenicByCIPDescriptor)
    (cfg : m.GraphConfiguration) :
    m.GraphDescriptorChiralityCertificate cfg where
  outcome := m.graphCipRSDescriptorChiralityClassifier cfg
  classifierValue :=
    m.graphCipRSDescriptorChiralityClassifier?_eq_some_of_stereogenicByCIPDescriptor hdesc cfg
  sound :=
    m.graphCipRSDescriptorChiralityClassifier_sound cfg
  rawPattern :=
    m.graphCipRSPattern?_eq_some_graphCipRSPatternDescriptor_of_treeLike_descriptor
      htree hdesc cfg
  descriptorPattern :=
    m.graphCipRSPatternDescriptor?_eq_some_of_stereogenicByCIPDescriptor hdesc cfg
  rawClass :=
    m.graphCipRSClass?_eq_some_graphCipRSClassDescriptor_of_treeLike_descriptor
      htree hdesc cfg
  descriptorClass :=
    m.graphCipRSClassDescriptor?_eq_some_of_stereogenicByCIPDescriptor hdesc cfg
  complement :=
    m.graphMesoBySymmetryDescriptor_iff_not_chiral cfg

theorem graphMesoBySymmetry_iff_same_mirror (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.GraphMesoBySymmetry cfg ↔
      m.GraphSameCipRSClass cfg (m.detectedStereoSystem.mirrorConfiguration cfg) :=
  m.detectedStereoSystem.mesoCipRSConfigurationBySymmetry_iff_same_mirror cfg

theorem graphChiralBySymmetry_iff_not_same_mirror (m : MoleculeGraph V)
    (cfg : m.GraphConfiguration) :
    m.GraphChiralBySymmetry cfg ↔
      ¬ m.GraphSameCipRSClass cfg (m.detectedStereoSystem.mirrorConfiguration cfg) :=
  m.detectedStereoSystem.chiralCipRSConfigurationBySymmetry_iff_not_same_mirror cfg

theorem graphMesoBySymmetryCycleCut_iff_same_mirror
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.GraphMesoBySymmetryCycleCut cfg ↔
      m.GraphSameCipRSClassCycleCut cfg (m.detectedStereoSystem.mirrorConfiguration cfg) :=
  m.detectedStereoSystem.mesoCipRSConfigurationCycleCutBySymmetry_iff_same_mirror cfg

theorem graphChiralBySymmetryCycleCut_iff_not_same_mirror
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.GraphChiralBySymmetryCycleCut cfg ↔
      ¬ m.GraphSameCipRSClassCycleCut cfg (m.detectedStereoSystem.mirrorConfiguration cfg) :=
  m.detectedStereoSystem.chiralCipRSConfigurationCycleCutBySymmetry_iff_not_same_mirror cfg

theorem graphEnantiomeric_self_mirror_iff_chiral (m : MoleculeGraph V)
    (cfg : m.GraphConfiguration) :
    m.GraphEnantiomericBySymmetry cfg (m.detectedStereoSystem.mirrorConfiguration cfg) ↔
      m.GraphChiralBySymmetry cfg :=
  m.detectedStereoSystem.enantiomeric_cipRSConfigurations_self_mirror_iff_chiral cfg

theorem graphEnantiomericCycleCut_self_mirror_iff_chiral
    (m : MoleculeGraph V) (cfg : m.GraphConfiguration) :
    m.GraphEnantiomericBySymmetryCycleCut cfg (m.detectedStereoSystem.mirrorConfiguration cfg) ↔
      m.GraphChiralBySymmetryCycleCut cfg :=
  m.detectedStereoSystem.enantiomeric_cipRSConfigurationsCycleCut_self_mirror_iff_chiral cfg

end MoleculeGraph

end
end OneCenter
end TetraStereo
