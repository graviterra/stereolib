/-
# Whole-authority joint molecular/source assembly over one ordered native source list

This module integrates the full concrete source-family vocabulary of the repository into one
ordered, heterogeneous list of individual native observations over a single independently supplied
molecular core, and proves that the actual upstream molecular-evidence assembly plus the concrete
family codecs is an exact inverse on the whole request, including arbitrary correlated sets of
requests, injectivity, and the count-indexed (`Σ n, Fin n`) cross-count form.

## Individual rows

The union rows are individual observations, not family blocks.  A `RawWholeSourceEntry` stores one
raw observation of one family, its genuine source binding (the shared graph, the exact coordinate
channel, the drawing channel and the three encoding equalities), the family's actual `ValidFor`
predicate at that source, and the exact identifiers of the designated source (a native P-94 context
for the P-94 family, the common molecule/conversion source for the fullerene family, the explicit
atom enumeration for every binding).  A `NativeWholeSourceEntry` stores the corresponding actual
encoded native observation, the native context that the family decoder reads, and the validity
certificate at the reconstructed native source.  Because every row is one observation, an arbitrary
interleaving of families and repetitions is preserved by the single ordered list.

## The concrete codecs

`encodeWholeEntry` applies the family's actual encoder to the individual observation:
`relabelFrame`, `relabelObservation` (acyclic/fused/cyclophane/spiro), `toNativeObservation`
(noncarbon), `relabelCyclicObservation`, `relabelNativeObservation`, the actual successor relational
relabelling, `FullereneAuthorityCommonSource.encodeFamily`, and the P-94 `ofAuthorityValid` at the
reconstructed source resolver.  `decodeWholeEntry` applies the family's actual decoder:
`decodeFrame`, `unrelabelObservation`, `ofNativeObservation`, `unrelabelCyclicObservation`,
`decodeObservation`, `unrelabelNativeObservation`, the successor relational `unrelabelObservation`,
`FullereneAuthorityDecodeContext.decodeFamily`, and the P-94 `toAuthority` at the same resolver.
The exact inverse is proved family by family from the actual upstream inverse theorems.

No original `CertifiedAuthoritativeChemicalInput` is stored in a native entry.  For P-94 the
designated source is always `OrganicStereoNativeP94SourceContext.decodeSourceContext` of the actual
common graph and the native optional geometry; only the graph is tied to the core, so a P-94 source
may supply a different conformer geometry at the same graph.  For fullerene the native codec
explicitly does not carry the common molecule and its conversion, so those two fields are recorded
as necessary native provenance; they are not the original raw observation record.

## Main results

* `decodeWhole_assembleWhole` — exact inverse including the dependent core, enumeration and list.
* `decodeWhole_entries_heq`, `decodeWhole_getElem?_heq` — occurrence-level preservation.
* `assembleWhole_injective` and `decodeWhole_image_assembleWhole_image` — the correlated Set image
  inverse (not a marginal product).
* `assembleWhole_stateGraph_eq_core`, `assembleWhole_stateRationalPositions?_eq_core`,
  `assembleWhole_stateDiagram?_eq_core`, `assembleWhole_stateConformation_eq_core` — the actual
  output respects every core channel.
* `fixedLabel_retains_labels` — the fixed arbitrary-label `V` theorem: labels are retained.
* `source_ties_at_output` and the per-family `*_entry_ties` corollaries — the actual output
  projections are tied to the entry-native source through
  `MixedOutputPhysicalBinding.decodeEvidence_*` and the concrete assembly lemmas.
* `sourceContextAt?_ties` — the source graph/spatial/diagram reconstructed from the actual assembled
  state and the entry-native provenance.
* `decodeFinWhole_assembleFinWhole` and `decodeFinWhole_image_assembleFinWhole_image` — the
  `Σ n, WholeSourceRequest (Fin n)` form with a real encoder/decoder and exact cross-count Set
  inverse.
* `uncertaintySet_image`, `uncertaintySet_distinct_atom_counts` and
  `crossFamily_ordered_witness` — one concrete uncertainty set with two different atom counts and one
  ordered cross-family witness built from explicitly supplied policies and payloads.

Constructor exhaustiveness (`sourceFamily_exhaustive`, `mem_allFamilies`) proves only the actual
enumerated source vocabulary of this module; it claims nothing about unformalised chemical phenomena
or physical validity.
-/

import TetraStereo.OneCenter.OrganicStereoMixedOutputPhysicalBinding
import TetraStereo.OneCenter.OrganicStereoMolecularCanonicalTransport
import TetraStereo.OneCenter.OrganicStereoP93AcyclicIngress
import TetraStereo.OneCenter.OrganicStereoNoncarbonTetrahedralIngress
import TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress
import TetraStereo.OneCenter.OrganicStereoFusedVonBaeyerIngress
import TetraStereo.OneCenter.OrganicStereoCyclophaneAuthorityIngress
import TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress
import TetraStereo.OneCenter.OrganicStereoFullereneAuthorityIngress
import TetraStereo.OneCenter.OrganicStereoRelationalFullereneIngress
import TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding
import TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress
import TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes
import TetraStereo.OneCenter.OrganicStereoP94AuthorityObservationIngress
import TetraStereo.OneCenter.OrganicStereoNativeP94SourceContext
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter
namespace OrganicStereoWholeAuthorityMolecularAssembly

open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoMixedSourceAssembly
open OrganicStereoMixedOutputPhysicalBinding
open OrganicStereoMolecularCanonicalTransport
open OrganicStereoP93PhysicalFrameIngress
open OrganicStereoP93AcyclicIngress
open OrganicStereoNoncarbonTetrahedralIngress
open OrganicStereoMonocyclicRingAssemblyIngress
open OrganicStereoFusedVonBaeyerIngress
open OrganicStereoCyclophaneAuthorityIngress
open OrganicStereoSpiroAuthorityIngress
open OrganicStereoFullereneAuthorityIngress
open OrganicStereoRelationalFullereneIngress
open OrganicStereoRelationalFullereneInputEncoding
open OrganicStereoCoupledRingChainNativeAxes
open OrganicStereoP94AuthorityObservationIngress
open OrganicStereoNativeP94SourceContext

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The enumerated source-family vocabulary -/

/-- The actual enumerated concrete source-family vocabulary of the whole-authority assembly.  This
is a tag vocabulary only; it says nothing about chemical phenomena outside these constructors. -/
inductive SourceFamily where
  /-- The accepted legacy P-93 physical-frame source. -/
  | legacy
  /-- Full P-94 authority observations with their actual `ValidFor` predicate. -/
  | p94
  /-- P-93 acyclic authority observations. -/
  | acyclic
  /-- P-93 noncarbon tetrahedral authority observations. -/
  | noncarbon
  /-- The unified monocyclic/ring-assembly source. -/
  | unifiedMonoRing
  /-- P-93 fused/von Baeyer authority observations. -/
  | fusedVonBaeyer
  /-- P-93 cyclophane authority observations. -/
  | cyclophane
  /-- P-93 spiro authority observations. -/
  | spiro
  /-- The native whole-molecule fullerene authority source. -/
  | fullereneAuthority
  /-- The relational fullerene authority source. -/
  | relationalFullerene
  /-- Coupled ring-chain authority observations, including their native axes. -/
  | coupledRingChain
  deriving DecidableEq, Repr

/-- The complete ordered vocabulary list. -/
def allFamilies : List SourceFamily :=
  [.legacy, .p94, .acyclic, .noncarbon, .unifiedMonoRing, .fusedVonBaeyer, .cyclophane,
    .spiro, .fullereneAuthority, .relationalFullerene, .coupledRingChain]

/-- Constructor exhaustiveness of the actual enumerated vocabulary.  This proves only that every
tag of this module is one of the eleven listed constructors. -/
theorem sourceFamily_exhaustive (family : SourceFamily) :
    family = .legacy ∨ family = .p94 ∨ family = .acyclic ∨ family = .noncarbon ∨
      family = .unifiedMonoRing ∨ family = .fusedVonBaeyer ∨ family = .cyclophane ∨
        family = .spiro ∨ family = .fullereneAuthority ∨ family = .relationalFullerene ∨
          family = .coupledRingChain := by
  cases family <;> simp

/-- Every constructor occurs in the vocabulary list. -/
theorem mem_allFamilies (family : SourceFamily) : family ∈ allFamilies := by
  cases family <;> simp [allFamilies]

/-- The vocabulary count is exactly eleven. -/
theorem allFamilies_length : allFamilies.length = 11 := rfl

/-! ## Reconstructed source bindings -/

/-- The comparable native source context carried by every family satellite and by the P-94
reconstruction. -/
structure NativeSourceContext (V : Type*) [DecidableEq V] [Fintype V] where
  /-- The source interaction graph. -/
  graph : FiniteAtomInteractionHypergraph V
  /-- The optional exact source coordinates. -/
  spatial? : Option (V → CartesianPoint3) := none
  /-- The optional source drawing. -/
  diagram? : Option (OrganicDiagramSource V) := none

/-- Reconstruct the accepted source binding from a native finite source and the kept explicit
enumeration.  The source is the exact encoding of the native graph and optional channels; the three
binding equalities are definitional, and spatial well-formedness is derived from the exact encoder.
No stored source record is used. -/
def reconstructedBinding (shared : OrganicFiniteSource V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V where
  source := shared.encode enumeration
  shared := shared
  enumeration := enumeration
  graph_eq := rfl
  spatial_eq := rfl
  diagram_eq := rfl
  spatial_wellFormed := by
    cases hspatial : shared.spatial? with
    | none =>
        simp [OrganicFiniteSource.encode, AuthoritativeChemicalInput.SpatialIndicesWellFormed,
          OrganicFiniteSource.encodeSpatial?, hspatial]
    | some positions =>
        simp [OrganicFiniteSource.encode, AuthoritativeChemicalInput.SpatialIndicesWellFormed,
          OrganicFiniteSource.encodeSpatial?, hspatial,
          FiniteAtomInteractionHypergraph.encode_atomCount]

@[simp] theorem reconstructedBinding_source (shared : OrganicFiniteSource V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (reconstructedBinding shared enumeration).source = shared.encode enumeration := rfl

@[simp] theorem reconstructedBinding_shared (shared : OrganicFiniteSource V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (reconstructedBinding shared enumeration).shared = shared := rfl

@[simp] theorem reconstructedBinding_enumeration (shared : OrganicFiniteSource V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (reconstructedBinding shared enumeration).enumeration = enumeration := rfl

/-- Extensionality of accepted source bindings from the three data components.  The four proof
fields are propositionally irrelevant. -/
theorem sourceBinding_ext {first second :
    OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V}
    (hsource : first.source = second.source)
    (hshared : first.shared = second.shared)
    (henumeration : first.enumeration = second.enumeration) : first = second := by
  obtain ⟨firstSource, firstShared, firstEnumeration, firstGraph, firstSpatial,
    firstDiagram, firstWellFormed⟩ := first
  obtain ⟨secondSource, secondShared, secondEnumeration, secondGraph, secondSpatial,
    secondDiagram, secondWellFormed⟩ := second
  subst hsource
  subst hshared
  subst henumeration
  rfl

/-- The reconstructed binding is exactly the raw binding at the same enumeration. -/
theorem reconstructedBinding_eq (binding :
    OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (h : binding.enumeration = enumeration) :
    reconstructedBinding binding.shared enumeration = binding := by
  obtain ⟨source, shared, enumeration', graph_eq, spatial_eq, diagram_eq, wellFormed⟩ := binding
  subst h
  have hsource : shared.encode enumeration' = source := by
    apply authoritativeInput_ext
    · exact graph_eq
    · exact spatial_eq
    · exact diagram_eq
  subst hsource
  unfold reconstructedBinding
  rfl

/-- The exact encoding of the kept shared source at the requested enumeration is the original
binding source. -/
theorem shared_encode_eq_source
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (h : binding.enumeration = enumeration) :
    binding.shared.encode enumeration = binding.source := by
  rw [← h]
  exact binding.encode_shared

/-! ## The singleton satellites of the individual rows

Every family satellite below contains exactly the one native observation of its row.  The row's
individual observation is therefore never bundled with another row's observation. -/

def legacySatellite (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (frame : PhysicalFrame V) :
    OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSatellite V where
  graph := graph
  spatial? := spatial?
  diagram? := diagram?
  frames := [frame]

def acyclicSatellite (policy : P93AcyclicAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : AcyclicObservation V policy) :
    OrganicStereoP93AcyclicIngress.AcyclicObservationSatellite V policy where
  graph := graph
  spatial? := spatial?
  diagram? := diagram?
  observations := [observation]

def noncarbonSatellite (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : NativeNoncarbonObservation V policy.Descriptor) :
    OrganicStereoNoncarbonTetrahedralIngress.NoncarbonObservationSatellite V policy where
  graph := graph
  spatial? := spatial?
  diagram? := diagram?
  observations := [observation]

def cyclicSatellite (monocyclicPolicy : P93MonocyclicAuthorityPolicy)
    (assemblyPolicy : P93RingAssemblyAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : CyclicObservation V monocyclicPolicy assemblyPolicy) :
    OrganicStereoMonocyclicRingAssemblyIngress.CyclicObservationSatellite V
      monocyclicPolicy assemblyPolicy where
  graph := graph
  spatial? := spatial?
  diagram? := diagram?
  observations := [observation]

def fusedSatellite (fusedPolicy : P93FusedAuthorityPolicy)
    (vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy) :
    OrganicStereoFusedVonBaeyerIngress.FusedVonBaeyerSatellite V fusedPolicy vonBaeyerPolicy where
  graph := graph
  spatial? := spatial?
  diagram? := diagram?
  observations := [observation]

def cyclophaneSatellite (policy : P93CyclophaneAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : NativeCyclophaneAuthorityObservation V policy) :
    OrganicStereoCyclophaneAuthorityIngress.CyclophaneAuthorityObservationSatellite V policy where
  graph := graph
  spatial? := spatial?
  diagram? := diagram?
  observations := [observation]

def spiroSatellite (policy : P93SpiroAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : NativeSpiroAuthorityObservation policy V) :
    OrganicStereoSpiroAuthorityIngress.SpiroAuthoritySatellite policy V where
  graph := graph
  spatial? := spatial?
  diagram? := diagram?
  observations := [observation]

def fullereneSatellite (policy : P93FullereneAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : NativeFullereneAuthorityObservationFamily V) :
    OrganicStereoFullereneAuthorityIngress.FullereneAuthoritySatellite policy V where
  graph := graph
  spatial? := spatial?
  diagram? := diagram?
  observations := [observation]

def relationalSatellite (policy : P93RelationalFullereneAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : NativeRelationalFullereneObservation V enumeration policy) :
    OrganicStereoRelationalFullereneInputEncoding.NativeRelationalFullereneObservationSatellite
      V enumeration policy where
  graph := graph
  spatial? := spatial?
  diagram? := diagram?
  observations := [observation]

def coupledSatellite (policy : P93CoupledRingChainAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : SuppliedNativeCoupledRingChainObservation V policy) :
    OrganicStereoCoupledRingChainNativeAxes.NativeCoupledObservationSatellite V policy where
  graph := graph
  spatial? := spatial?
  diagram? := diagram?
  observations := [observation]

@[simp] theorem legacySatellite_toFiniteSource
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (frame : PhysicalFrame V) :
    (legacySatellite binding.shared.graph binding.shared.spatial? binding.shared.diagram?
      frame).toFiniteSource = binding.shared := rfl

@[simp] theorem acyclicSatellite_toFiniteSource
    (policy : P93AcyclicAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : AcyclicObservation V policy) :
    (acyclicSatellite policy binding.shared.graph binding.shared.spatial?
      binding.shared.diagram? observation).toFiniteSource = binding.shared := rfl

@[simp] theorem noncarbonSatellite_toFiniteSource
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : NativeNoncarbonObservation V policy.Descriptor) :
    (noncarbonSatellite policy binding.shared.graph binding.shared.spatial?
      binding.shared.diagram? observation).toFiniteSource = binding.shared := rfl

@[simp] theorem cyclicSatellite_toFiniteSource
    (monocyclicPolicy : P93MonocyclicAuthorityPolicy)
    (assemblyPolicy : P93RingAssemblyAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : CyclicObservation V monocyclicPolicy assemblyPolicy) :
    (cyclicSatellite monocyclicPolicy assemblyPolicy binding.shared.graph binding.shared.spatial?
      binding.shared.diagram? observation).toFiniteSource = binding.shared := rfl

@[simp] theorem fusedSatellite_toFiniteSource
    (fusedPolicy : P93FusedAuthorityPolicy)
    (vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy) :
    (fusedSatellite fusedPolicy vonBaeyerPolicy binding.shared.graph binding.shared.spatial?
      binding.shared.diagram? observation).toFiniteSource = binding.shared := rfl

@[simp] theorem cyclophaneSatellite_toFiniteSource
    (policy : P93CyclophaneAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : NativeCyclophaneAuthorityObservation V policy) :
    (cyclophaneSatellite policy binding.shared.graph binding.shared.spatial?
      binding.shared.diagram? observation).toFiniteSource = binding.shared := rfl

@[simp] theorem spiroSatellite_toFiniteSource
    (policy : P93SpiroAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : NativeSpiroAuthorityObservation policy V) :
    (spiroSatellite policy binding.shared.graph binding.shared.spatial?
      binding.shared.diagram? observation).toFiniteSource = binding.shared := rfl

@[simp] theorem fullereneSatellite_toFiniteSource
    (policy : P93FullereneAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : NativeFullereneAuthorityObservationFamily V) :
    (fullereneSatellite policy binding.shared.graph binding.shared.spatial?
      binding.shared.diagram? observation).toFiniteSource = binding.shared := rfl

@[simp] theorem relationalSatellite_toFiniteSource
    (policy : P93RelationalFullereneAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : NativeRelationalFullereneObservation V enumeration policy) :
    (relationalSatellite policy binding.shared.graph binding.shared.spatial?
      binding.shared.diagram? enumeration observation).toFiniteSource = binding.shared := rfl

@[simp] theorem coupledSatellite_toFiniteSource
    (policy : P93CoupledRingChainAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : SuppliedNativeCoupledRingChainObservation V policy) :
    (coupledSatellite policy binding.shared.graph binding.shared.spatial?
      binding.shared.diagram? observation).toFiniteSource = binding.shared := rfl

/-! ## The actual single-observation decoders -/

def legacyDecoded (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (frame : PhysicalFrame V) : SourcePhysicalFrame :=
  decodeFrame enumeration
    ((legacySatellite graph spatial? diagram? frame).spatialConfiguration enumeration) frame

def acyclicDecoded (enumeration : V ≃ Fin (Fintype.card V)) {policy : P93AcyclicAuthorityPolicy}
    (observation : AcyclicObservation V policy) : SourceAcyclicObservation policy :=
  OrganicStereoP93AcyclicIngress.unrelabelObservation enumeration observation

def noncarbonDecoded (enumeration : V ≃ Fin (Fintype.card V))
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (observation : NativeNoncarbonObservation V policy.Descriptor) :
    SourceNoncarbonObservation policy :=
  OrganicStereoNoncarbonTetrahedralIngress.ofNativeObservation enumeration policy observation

def cyclicDecoded (enumeration : V ≃ Fin (Fintype.card V))
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy}
    (observation : CyclicObservation V monocyclicPolicy assemblyPolicy) :
    SourceCyclicObservation monocyclicPolicy assemblyPolicy :=
  OrganicStereoMonocyclicRingAssemblyIngress.unrelabelCyclicObservation enumeration observation

def fusedDecoded (enumeration : V ≃ Fin (Fintype.card V))
    {fusedPolicy : P93FusedAuthorityPolicy}
    {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observation : SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy) :
    SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy :=
  OrganicStereoFusedVonBaeyerIngress.unrelabelObservation enumeration observation

def cyclophaneDecoded (enumeration : V ≃ Fin (Fintype.card V))
    {policy : P93CyclophaneAuthorityPolicy}
    (observation : NativeCyclophaneAuthorityObservation V policy) :
    SourceCyclophaneAuthorityObservation policy :=
  OrganicStereoCyclophaneAuthorityIngress.unrelabelObservation enumeration observation

def spiroDecoded (enumeration : V ≃ Fin (Fintype.card V))
    {policy : P93SpiroAuthorityPolicy}
    (observation : NativeSpiroAuthorityObservation policy V) :
    SourceSpiroAuthorityObservation policy :=
  OrganicStereoSpiroAuthorityIngress.decodeObservation enumeration observation

def fullereneDecoded (policy : P93FullereneAuthorityPolicy)
    (enumeration : V ≃ Fin (Fintype.card V))
    (spatial? : Option (V → CartesianPoint3))
    (observation : NativeFullereneAuthorityObservationFamily V) :
    SourceFullereneAuthorityObservation policy :=
  (OrganicStereoFullereneAuthorityIngress.FullereneAuthorityDecodeContext.ofEnumeration
    enumeration spatial?).decodeFamily policy observation

def relationalDecoded (policy : P93RelationalFullereneAuthorityPolicy)
    (enumeration : V ≃ Fin (Fintype.card V))
    (spatial? : Option (V → CartesianPoint3))
    (observation : NativeRelationalFullereneObservation V enumeration policy) :
    P93RelationalFullereneAuthorityObservation policy :=
  OrganicStereoRelationalFullereneInputEncoding.unrelabelObservation enumeration policy
    (OrganicFiniteSource.encodeSpatial? enumeration spatial?) observation

def coupledDecoded (enumeration : V ≃ Fin (Fintype.card V))
    {policy : P93CoupledRingChainAuthorityPolicy}
    (observation : SuppliedNativeCoupledRingChainObservation V policy) :
    P93CoupledRingChainAuthorityObservation policy :=
  OrganicStereoCoupledRingChainNativeAxes.unrelabelNativeObservation enumeration observation

/-! ## The actual single-observation validity statements -/

def LegacyRowValid (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (frame : PhysicalFrame V) : Prop :=
  (legacyDecoded enumeration graph spatial? diagram? frame).ValidFor
    ((legacySatellite graph spatial? diagram? frame).toFiniteSource.encode enumeration)

def AcyclicRowValid (policy : P93AcyclicAuthorityPolicy)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : AcyclicObservation V policy) : Prop :=
  (acyclicDecoded enumeration observation).ValidFor
    ((acyclicSatellite policy graph spatial? diagram? observation).toFiniteSource.encode enumeration)

def NoncarbonRowValid (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : NativeNoncarbonObservation V policy.Descriptor) : Prop :=
  SourceNoncarbonObservation.ValidFor policy
    ((noncarbonSatellite policy graph spatial? diagram? observation).toFiniteSource.encode
      enumeration)
    (noncarbonDecoded enumeration policy observation)

def CyclicRowValid (monocyclicPolicy : P93MonocyclicAuthorityPolicy)
    (assemblyPolicy : P93RingAssemblyAuthorityPolicy)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : CyclicObservation V monocyclicPolicy assemblyPolicy) : Prop :=
  (cyclicDecoded enumeration observation).ValidFor
    ((cyclicSatellite monocyclicPolicy assemblyPolicy graph spatial? diagram?
      observation).toFiniteSource.encode enumeration)

def FusedRowValid (fusedPolicy : P93FusedAuthorityPolicy)
    (vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy) : Prop :=
  (fusedDecoded enumeration observation).ValidFor
    ((fusedSatellite fusedPolicy vonBaeyerPolicy graph spatial? diagram?
      observation).toFiniteSource.encode enumeration)

def CyclophaneRowValid (policy : P93CyclophaneAuthorityPolicy)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : NativeCyclophaneAuthorityObservation V policy) : Prop :=
  (cyclophaneDecoded enumeration observation).ValidFor
    ((cyclophaneSatellite policy graph spatial? diagram? observation).toFiniteSource.encode
      enumeration)

def SpiroRowValid (policy : P93SpiroAuthorityPolicy)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : NativeSpiroAuthorityObservation policy V) : Prop :=
  SourceSpiroAuthorityObservation.ValidFor
    ((spiroSatellite policy graph spatial? diagram? observation).toFiniteSource.encode enumeration)
    (spiroDecoded enumeration observation)

def FullereneRowValid (policy : P93FullereneAuthorityPolicy)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : NativeFullereneAuthorityObservationFamily V) : Prop :=
  (fullereneDecoded policy enumeration spatial? observation).ValidFor
    ((fullereneSatellite policy graph spatial? diagram? observation).toFiniteSource.encode
      enumeration)

def FullereneRowMoleculeBound (policy : P93FullereneAuthorityPolicy)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : NativeFullereneAuthorityObservationFamily V) : Prop :=
  (fullereneDecoded policy enumeration spatial? observation).MoleculeBoundTo
    ((fullereneSatellite policy graph spatial? diagram? observation).toFiniteSource.encode
      enumeration)

def RelationalRowValid (policy : P93RelationalFullereneAuthorityPolicy)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : NativeRelationalFullereneObservation V enumeration policy) : Prop :=
  (relationalDecoded policy enumeration spatial? observation).ValidFor policy
    ((relationalSatellite policy graph spatial? diagram? enumeration observation).toFiniteSource.encode
      enumeration)

def CoupledRowValid (policy : P93CoupledRingChainAuthorityPolicy)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : SuppliedNativeCoupledRingChainObservation V policy) : Prop :=
  (coupledDecoded enumeration observation).ValidFor policy
    ((coupledSatellite policy graph spatial? diagram? observation).toFiniteSource.encode enumeration)

/-! ## The raw entries: actual raw single observations at their designated sources -/

/-- One raw source-family entry over the common core and enumeration.  Every constructor stores one
actual raw observation, the family's genuine source binding and `ValidFor` predicate, and the
explicit identifiers of the designated source. -/
inductive RawWholeSourceEntry {V : Type} [DecidableEq V] [Fintype V]
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) : Type 1 where
  /-- The accepted legacy P-93 physical-frame raw source with one frame. -/
  | legacy
      (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
      (enumeration_eq : binding.enumeration = enumeration)
      (graph_eq : binding.shared.graph = core.graph)
      (spatial_eq : binding.shared.spatial? = core.rationalPositions?)
      (diagram_eq : binding.shared.diagram? = core.diagram?)
      (frame : SourcePhysicalFrame)
      (valid : frame.ValidFor binding.source) :
      RawWholeSourceEntry core enumeration
  /-- Full P-94 raw authority observation at its actual designated certified source.  The source is
  tied to the common graph only; its optional geometry and drawing are genuinely its own, so a P-94
  row may carry a different conformer source geometry at the same graph. -/
  | p94
      (source : CertifiedAuthoritativeChemicalInput)
      (graph_eq : source.input.molecule = core.graph.encode enumeration)
      (policy : P94AuthorityPolicy)
      (observation : P94AuthorityObservation policy)
      (valid : observation.ValidFor policy source.input) :
      RawWholeSourceEntry core enumeration
  /-- P-93 acyclic raw authority observation. -/
  | acyclic
      (policy : P93AcyclicAuthorityPolicy)
      (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
      (enumeration_eq : binding.enumeration = enumeration)
      (graph_eq : binding.shared.graph = core.graph)
      (spatial_eq : binding.shared.spatial? = core.rationalPositions?)
      (diagram_eq : binding.shared.diagram? = core.diagram?)
      (observation : SourceAcyclicObservation policy)
      (valid : observation.ValidFor binding.source) :
      RawWholeSourceEntry core enumeration
  /-- P-93 noncarbon tetrahedral raw authority observation. -/
  | noncarbon
      (policy : P93NoncarbonTetrahedralAuthorityPolicy)
      (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
      (enumeration_eq : binding.enumeration = enumeration)
      (graph_eq : binding.shared.graph = core.graph)
      (spatial_eq : binding.shared.spatial? = core.rationalPositions?)
      (diagram_eq : binding.shared.diagram? = core.diagram?)
      (observation : SourceNoncarbonObservation policy)
      (valid : SourceNoncarbonObservation.ValidFor policy binding.source observation) :
      RawWholeSourceEntry core enumeration
  /-- The unified monocyclic/ring-assembly raw observation. -/
  | unifiedMonoRing
      (monocyclicPolicy : P93MonocyclicAuthorityPolicy)
      (assemblyPolicy : P93RingAssemblyAuthorityPolicy)
      (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
      (enumeration_eq : binding.enumeration = enumeration)
      (graph_eq : binding.shared.graph = core.graph)
      (spatial_eq : binding.shared.spatial? = core.rationalPositions?)
      (diagram_eq : binding.shared.diagram? = core.diagram?)
      (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
      (observation : SourceCyclicObservation monocyclicPolicy assemblyPolicy)
      (valid : observation.ValidFor binding.source) :
      RawWholeSourceEntry core enumeration
  /-- P-93 fused/von Baeyer raw authority observation. -/
  | fusedVonBaeyer
      (fusedPolicy : P93FusedAuthorityPolicy)
      (vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy)
      (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
      (enumeration_eq : binding.enumeration = enumeration)
      (graph_eq : binding.shared.graph = core.graph)
      (spatial_eq : binding.shared.spatial? = core.rationalPositions?)
      (diagram_eq : binding.shared.diagram? = core.diagram?)
      (observation : SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy)
      (valid : observation.ValidFor binding.source) :
      RawWholeSourceEntry core enumeration
  /-- P-93 cyclophane raw authority observation. -/
  | cyclophane
      (policy : P93CyclophaneAuthorityPolicy)
      (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
      (enumeration_eq : binding.enumeration = enumeration)
      (graph_eq : binding.shared.graph = core.graph)
      (spatial_eq : binding.shared.spatial? = core.rationalPositions?)
      (diagram_eq : binding.shared.diagram? = core.diagram?)
      (observation : SourceCyclophaneAuthorityObservation policy)
      (valid : observation.ValidFor binding.source) :
      RawWholeSourceEntry core enumeration
  /-- P-93 spiro raw authority observation. -/
  | spiro
      (policy : P93SpiroAuthorityPolicy)
      (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
      (enumeration_eq : binding.enumeration = enumeration)
      (graph_eq : binding.shared.graph = core.graph)
      (spatial_eq : binding.shared.spatial? = core.rationalPositions?)
      (diagram_eq : binding.shared.diagram? = core.diagram?)
      (observation : SourceSpiroAuthorityObservation policy)
      (valid : SourceSpiroAuthorityObservation.ValidFor binding.source observation) :
      RawWholeSourceEntry core enumeration
  /-- The native whole-molecule fullerene raw authority observation. -/
  | fullereneAuthority
      (policy : P93FullereneAuthorityPolicy)
      (common : OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource V)
      (enumeration_eq : common.binding.enumeration = enumeration)
      (graph_eq : common.binding.shared.graph = core.graph)
      (spatial_eq : common.binding.shared.spatial? = core.rationalPositions?)
      (diagram_eq : common.binding.shared.diagram? = core.diagram?)
      (observation : SourceFullereneAuthorityObservation policy)
      (valid : observation.ValidFor common.binding.source)
      (moleculeBound : observation.MoleculeBoundTo common.binding.source) :
      RawWholeSourceEntry core enumeration
  /-- The relational fullerene raw authority observation. -/
  | relationalFullerene
      (policy : P93RelationalFullereneAuthorityPolicy)
      (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
      (enumeration_eq : binding.enumeration = enumeration)
      (graph_eq : binding.shared.graph = core.graph)
      (spatial_eq : binding.shared.spatial? = core.rationalPositions?)
      (diagram_eq : binding.shared.diagram? = core.diagram?)
      (observation : P93RelationalFullereneAuthorityObservation policy)
      (valid : observation.ValidFor policy binding.source) :
      RawWholeSourceEntry core enumeration
  /-- The coupled ring-chain raw authority observation with native axes. -/
  | coupledRingChain
      (policy : P93CoupledRingChainAuthorityPolicy)
      (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
      (enumeration_eq : binding.enumeration = enumeration)
      (graph_eq : binding.shared.graph = core.graph)
      (spatial_eq : binding.shared.spatial? = core.rationalPositions?)
      (diagram_eq : binding.shared.diagram? = core.diagram?)
      (observation : P93CoupledRingChainAuthorityObservation policy)
      (valid : observation.ValidFor policy binding.source) :
      RawWholeSourceEntry core enumeration

/-! ## The native entries: actual encoded single observations -/

/-- One native source-family entry over the common core and enumeration.  Every constructor stores
the family's actual encoded native observation, the native graph/coordinate/drawing context, and the
validity certificate at the reconstructed native source.  No raw observation record, whole request,
certified source or pre-assembled state is stored. -/
inductive NativeWholeSourceEntry {V : Type} [DecidableEq V] [Fintype V]
    (core : OrganicMolecularEvidence V)
    (enumeration : V ≃ Fin (Fintype.card V)) : Type 1 where
  /-- The accepted legacy P-93 physical-frame native observation. -/
  | legacy
      (graph : FiniteAtomInteractionHypergraph V)
      (spatial? : Option (V → CartesianPoint3))
      (diagram? : Option (OrganicDiagramSource V))
      (frame : PhysicalFrame V)
      (graph_eq : graph = core.graph)
      (spatial_eq : spatial? = core.rationalPositions?)
      (diagram_eq : diagram? = core.diagram?)
      (valid : LegacyRowValid enumeration graph spatial? diagram? frame) :
      NativeWholeSourceEntry core enumeration
  /-- Full P-94 native authority observation: the source-free reconstructed context, the encoded
  payload indexed by the reconstructed source, and the validity of the decoded observation.  No
  certified source is stored. -/
  | p94
      (policy : P94AuthorityPolicy)
      (native : OrganicStereoNativeP94SourceContext.NativeAuthorityObservation
        core.graph enumeration policy) :
      NativeWholeSourceEntry core enumeration
  /-- P-93 acyclic native authority observation. -/
  | acyclic
      (policy : P93AcyclicAuthorityPolicy)
      (graph : FiniteAtomInteractionHypergraph V)
      (spatial? : Option (V → CartesianPoint3))
      (diagram? : Option (OrganicDiagramSource V))
      (observation : AcyclicObservation V policy)
      (graph_eq : graph = core.graph)
      (spatial_eq : spatial? = core.rationalPositions?)
      (diagram_eq : diagram? = core.diagram?)
      (valid : AcyclicRowValid policy enumeration graph spatial? diagram? observation) :
      NativeWholeSourceEntry core enumeration
  /-- P-93 noncarbon tetrahedral native authority observation. -/
  | noncarbon
      (policy : P93NoncarbonTetrahedralAuthorityPolicy)
      (graph : FiniteAtomInteractionHypergraph V)
      (spatial? : Option (V → CartesianPoint3))
      (diagram? : Option (OrganicDiagramSource V))
      (observation : NativeNoncarbonObservation V policy.Descriptor)
      (graph_eq : graph = core.graph)
      (spatial_eq : spatial? = core.rationalPositions?)
      (diagram_eq : diagram? = core.diagram?)
      (valid : NoncarbonRowValid policy enumeration graph spatial? diagram? observation) :
      NativeWholeSourceEntry core enumeration
  /-- The unified monocyclic/ring-assembly native observation. -/
  | unifiedMonoRing
      (monocyclicPolicy : P93MonocyclicAuthorityPolicy)
      (assemblyPolicy : P93RingAssemblyAuthorityPolicy)
      (graph : FiniteAtomInteractionHypergraph V)
      (spatial? : Option (V → CartesianPoint3))
      (diagram? : Option (OrganicDiagramSource V))
      (observation : CyclicObservation V monocyclicPolicy assemblyPolicy)
      (graph_eq : graph = core.graph)
      (spatial_eq : spatial? = core.rationalPositions?)
      (diagram_eq : diagram? = core.diagram?)
      (valid : CyclicRowValid monocyclicPolicy assemblyPolicy enumeration graph spatial? diagram?
        observation)
      (structurallyWellFormed :
        ((cyclicSatellite monocyclicPolicy assemblyPolicy graph spatial? diagram?
          observation).toFiniteSource.encode enumeration).molecule.StructurallyWellFormed) :
      NativeWholeSourceEntry core enumeration
  /-- P-93 fused/von Baeyer native authority observation. -/
  | fusedVonBaeyer
      (fusedPolicy : P93FusedAuthorityPolicy)
      (vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy)
      (graph : FiniteAtomInteractionHypergraph V)
      (spatial? : Option (V → CartesianPoint3))
      (diagram? : Option (OrganicDiagramSource V))
      (observation : SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy)
      (graph_eq : graph = core.graph)
      (spatial_eq : spatial? = core.rationalPositions?)
      (diagram_eq : diagram? = core.diagram?)
      (valid : FusedRowValid fusedPolicy vonBaeyerPolicy enumeration graph spatial? diagram?
        observation) :
      NativeWholeSourceEntry core enumeration
  /-- P-93 cyclophane native authority observation. -/
  | cyclophane
      (policy : P93CyclophaneAuthorityPolicy)
      (graph : FiniteAtomInteractionHypergraph V)
      (spatial? : Option (V → CartesianPoint3))
      (diagram? : Option (OrganicDiagramSource V))
      (observation : NativeCyclophaneAuthorityObservation V policy)
      (graph_eq : graph = core.graph)
      (spatial_eq : spatial? = core.rationalPositions?)
      (diagram_eq : diagram? = core.diagram?)
      (valid : CyclophaneRowValid policy enumeration graph spatial? diagram? observation) :
      NativeWholeSourceEntry core enumeration
  /-- P-93 spiro native authority observation. -/
  | spiro
      (policy : P93SpiroAuthorityPolicy)
      (graph : FiniteAtomInteractionHypergraph V)
      (spatial? : Option (V → CartesianPoint3))
      (diagram? : Option (OrganicDiagramSource V))
      (observation : NativeSpiroAuthorityObservation policy V)
      (graph_eq : graph = core.graph)
      (spatial_eq : spatial? = core.rationalPositions?)
      (diagram_eq : diagram? = core.diagram?)
      (valid : SpiroRowValid policy enumeration graph spatial? diagram? observation) :
      NativeWholeSourceEntry core enumeration
  /-- The native whole-molecule fullerene observation, with the common molecule and its conversion
  as necessary native provenance (the accepted native codec explicitly does not carry them). -/
  | fullereneAuthority
      (policy : P93FullereneAuthorityPolicy)
      (graph : FiniteAtomInteractionHypergraph V)
      (spatial? : Option (V → CartesianPoint3))
      (diagram? : Option (OrganicDiagramSource V))
      (observation : NativeFullereneAuthorityObservationFamily V)
      (graph_eq : graph = core.graph)
      (spatial_eq : spatial? = core.rationalPositions?)
      (diagram_eq : diagram? = core.diagram?)
      (molecule : RawMolecule)
      (conversion_eq : molecule.toSemanticMolecule? =
        some ((fullereneSatellite policy graph spatial? diagram?
          observation).toFiniteSource.encode enumeration).molecule)
      (valid : FullereneRowValid policy enumeration graph spatial? diagram? observation)
      (moleculeBound : FullereneRowMoleculeBound policy enumeration graph spatial? diagram?
        observation) :
      NativeWholeSourceEntry core enumeration
  /-- The relational fullerene native authority observation (successor input codec). -/
  | relationalFullerene
      (policy : P93RelationalFullereneAuthorityPolicy)
      (graph : FiniteAtomInteractionHypergraph V)
      (spatial? : Option (V → CartesianPoint3))
      (diagram? : Option (OrganicDiagramSource V))
      (observation : NativeRelationalFullereneObservation V enumeration policy)
      (graph_eq : graph = core.graph)
      (spatial_eq : spatial? = core.rationalPositions?)
      (diagram_eq : diagram? = core.diagram?)
      (valid : RelationalRowValid policy enumeration graph spatial? diagram? observation) :
      NativeWholeSourceEntry core enumeration
  /-- The coupled ring-chain native authority observation (successor native-axes codec). -/
  | coupledRingChain
      (policy : P93CoupledRingChainAuthorityPolicy)
      (graph : FiniteAtomInteractionHypergraph V)
      (spatial? : Option (V → CartesianPoint3))
      (diagram? : Option (OrganicDiagramSource V))
      (observation : SuppliedNativeCoupledRingChainObservation V policy)
      (graph_eq : graph = core.graph)
      (spatial_eq : spatial? = core.rationalPositions?)
      (diagram_eq : diagram? = core.diagram?)
      (valid : CoupledRowValid policy enumeration graph spatial? diagram? observation) :
      NativeWholeSourceEntry core enumeration

/-! ## The actual concrete encoders -/

def encodeLegacyFrame (enumeration : V ≃ Fin (Fintype.card V))
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (frame : SourcePhysicalFrame) (valid : frame.ValidFor binding.source) : PhysicalFrame V :=
  OrganicStereoP93PhysicalFrameIngress.relabelFrame enumeration frame
    (SourcePhysicalFrame.boundedIn_of_validFor binding frame valid)

def encodeAcyclicObservation (enumeration : V ≃ Fin (Fintype.card V))
    (policy : P93AcyclicAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : SourceAcyclicObservation policy)
    (valid : observation.ValidFor binding.source) : AcyclicObservation V policy :=
  OrganicStereoP93AcyclicIngress.relabelObservation enumeration observation
    (SourceAcyclicObservation.boundedIn_of_validFor_binding binding observation valid)

def encodeNoncarbonObservation (enumeration : V ≃ Fin (Fintype.card V))
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : SourceNoncarbonObservation policy)
    (valid : SourceNoncarbonObservation.ValidFor policy binding.source observation) :
    NativeNoncarbonObservation V policy.Descriptor :=
  OrganicStereoNoncarbonTetrahedralIngress.toNativeObservation enumeration policy observation
    (SourceNoncarbonObservation.boundedIn_of_validFor_binding binding observation valid)

def encodeCyclicObservation (enumeration : V ≃ Fin (Fintype.card V))
    (monocyclicPolicy : P93MonocyclicAuthorityPolicy)
    (assemblyPolicy : P93RingAssemblyAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (observation : SourceCyclicObservation monocyclicPolicy assemblyPolicy)
    (valid : observation.ValidFor binding.source) :
    CyclicObservation V monocyclicPolicy assemblyPolicy :=
  OrganicStereoMonocyclicRingAssemblyIngress.relabelCyclicObservation enumeration observation
    (SourceCyclicObservation.boundedIn_of_validFor_binding binding structurallyWellFormed observation
      valid)

def encodeFusedObservation (enumeration : V ≃ Fin (Fintype.card V))
    (fusedPolicy : P93FusedAuthorityPolicy)
    (vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy)
    (valid : observation.ValidFor binding.source) :
    SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy :=
  OrganicStereoFusedVonBaeyerIngress.relabelObservation enumeration observation
    (SourceFusedVonBaeyerObservation.boundedIn_of_validFor_binding binding observation valid)

def encodeCyclophaneObservation (enumeration : V ≃ Fin (Fintype.card V))
    (policy : P93CyclophaneAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : SourceCyclophaneAuthorityObservation policy)
    (valid : observation.ValidFor binding.source) :
    NativeCyclophaneAuthorityObservation V policy :=
  OrganicStereoCyclophaneAuthorityIngress.relabelObservation enumeration observation
    (SourceCyclophaneAuthorityObservation.boundedIn_of_validFor_binding binding observation valid)

def encodeSpiroObservation (enumeration : V ≃ Fin (Fintype.card V))
    (policy : P93SpiroAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : SourceSpiroAuthorityObservation policy)
    (valid : SourceSpiroAuthorityObservation.ValidFor binding.source observation) :
    NativeSpiroAuthorityObservation policy V :=
  OrganicStereoSpiroAuthorityIngress.relabelObservation enumeration observation
    (SourceSpiroAuthorityObservation.boundedIn_of_validFor policy binding observation valid)

def encodeRelationalObservation (enumeration : V ≃ Fin (Fintype.card V))
    (policy : P93RelationalFullereneAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : P93RelationalFullereneAuthorityObservation policy)
    (valid : observation.ValidFor policy binding.source) :
    NativeRelationalFullereneObservation V enumeration policy :=
  OrganicStereoRelationalFullereneInputEncoding.relabelObservation enumeration policy observation
    (relationalObservationBoundedIn_of_validFor
      (relationalObservationAtomCount_eq binding observation valid) valid)

def encodeCoupledObservation (enumeration : V ≃ Fin (Fintype.card V))
    (policy : P93CoupledRingChainAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : P93CoupledRingChainAuthorityObservation policy)
    (valid : observation.ValidFor policy binding.source) :
    SuppliedNativeCoupledRingChainObservation V policy :=
  OrganicStereoCoupledRingChainNativeAxes.relabelNativeObservation enumeration observation
    (OrganicStereoCoupledRingChainNativeAxes.NativeObservationBoundedIn.of_validFor_binding binding
      observation valid)

/-! ## Exact per-row decoder inverses -/

theorem legacyDecoded_encodeLegacyFrame (enumeration : V ≃ Fin (Fintype.card V))
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (h : binding.enumeration = enumeration)
    (frame : SourcePhysicalFrame) (valid : frame.ValidFor binding.source) :
    legacyDecoded enumeration binding.shared.graph binding.shared.spatial?
        binding.shared.diagram? (encodeLegacyFrame enumeration binding frame valid) = frame := by
  cases frame with
  | helix path frame =>
      exact decodeFrame_relabelFrame_helix enumeration binding.source
        ((legacySatellite binding.shared.graph binding.shared.spatial? binding.shared.diagram?
          (encodeLegacyFrame enumeration binding (.helix path frame) valid)).spatialConfiguration
            enumeration) path frame valid
        (SourcePhysicalFrame.boundedIn_of_validFor binding (.helix path frame) valid)
  | plane members frame =>
      exact decodeFrame_relabelFrame_plane enumeration binding.source
        ((legacySatellite binding.shared.graph binding.shared.spatial? binding.shared.diagram?
          (encodeLegacyFrame enumeration binding (.plane members frame) valid)).spatialConfiguration
            enumeration) members frame valid
        (SourcePhysicalFrame.boundedIn_of_validFor binding (.plane members frame) valid)
  | polyhedral center ligands geometry frame =>
      let native : PhysicalFrame V :=
        encodeLegacyFrame enumeration binding (.polyhedral center ligands geometry frame) valid
      have validCopy := valid
      rcases validCopy with
        ⟨_centerEq, _ligandSetEq, _ligandNodup, _geometryEq, _recognized, sourceSpatial,
          _centerPointAt, _positionsAt, _arity, _incidence, _roles, _orientation⟩
      have hspatial :
          OrganicFiniteSource.encodeSpatial? enumeration binding.shared.spatial? =
            binding.source.spatial? := by
        rw [← h, binding.spatial_eq]
      have spatialConfigEq :
          ((legacySatellite binding.shared.graph binding.shared.spatial?
            binding.shared.diagram? native).spatialConfiguration enumeration) = frame.spatial := by
        unfold OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSatellite.spatialConfiguration
          OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSatellite.sharedSpatial?
        change (OrganicFiniteSource.encodeSpatial? enumeration binding.shared.spatial?).getD
          { positions := [] } = frame.spatial
        rw [hspatial, sourceSpatial]
        rfl
      have spatialObserved : binding.source.spatial? =
          some ((legacySatellite binding.shared.graph binding.shared.spatial?
            binding.shared.diagram? native).spatialConfiguration enumeration) := by
        rw [spatialConfigEq]
        exact sourceSpatial
      exact decodeFrame_relabelFrame_polyhedral enumeration binding.source
        ((legacySatellite binding.shared.graph binding.shared.spatial? binding.shared.diagram?
          native).spatialConfiguration enumeration)
        center ligands geometry frame valid
        (SourcePhysicalFrame.boundedIn_of_validFor binding
          (.polyhedral center ligands geometry frame) valid) spatialObserved

theorem acyclicDecoded_encodeAcyclicObservation (enumeration : V ≃ Fin (Fintype.card V))
    (policy : P93AcyclicAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : SourceAcyclicObservation policy)
    (valid : observation.ValidFor binding.source) :
    acyclicDecoded enumeration
        (encodeAcyclicObservation enumeration policy binding observation valid) = observation := by
  unfold acyclicDecoded encodeAcyclicObservation
  exact OrganicStereoP93AcyclicIngress.unrelabelObservation_relabelObservation enumeration
    observation
    (SourceAcyclicObservation.boundedIn_of_validFor_binding binding observation valid)

theorem noncarbonDecoded_encodeNoncarbonObservation (enumeration : V ≃ Fin (Fintype.card V))
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : SourceNoncarbonObservation policy)
    (valid : SourceNoncarbonObservation.ValidFor policy binding.source observation) :
    noncarbonDecoded enumeration policy
        (encodeNoncarbonObservation enumeration policy binding observation valid) = observation := by
  unfold noncarbonDecoded encodeNoncarbonObservation
  exact OrganicStereoNoncarbonTetrahedralIngress.ofNativeObservation_toNativeObservation
    enumeration policy observation
    (SourceNoncarbonObservation.boundedIn_of_validFor_binding binding observation valid)

theorem cyclicDecoded_encodeCyclicObservation (enumeration : V ≃ Fin (Fintype.card V))
    (monocyclicPolicy : P93MonocyclicAuthorityPolicy)
    (assemblyPolicy : P93RingAssemblyAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (observation : SourceCyclicObservation monocyclicPolicy assemblyPolicy)
    (valid : observation.ValidFor binding.source) :
    cyclicDecoded enumeration
        (encodeCyclicObservation enumeration monocyclicPolicy assemblyPolicy binding
          structurallyWellFormed observation valid) = observation := by
  unfold cyclicDecoded encodeCyclicObservation
  exact OrganicStereoMonocyclicRingAssemblyIngress.unrelabelCyclicObservation_relabelCyclicObservation
    enumeration observation
    (SourceCyclicObservation.boundedIn_of_validFor_binding binding structurallyWellFormed
      observation valid)
    (SourceCyclicObservation.normalizationFixed_of_validFor binding.source observation valid)

theorem fusedDecoded_encodeFusedObservation (enumeration : V ≃ Fin (Fintype.card V))
    (fusedPolicy : P93FusedAuthorityPolicy)
    (vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy)
    (valid : observation.ValidFor binding.source) :
    fusedDecoded enumeration
        (encodeFusedObservation enumeration fusedPolicy vonBaeyerPolicy binding observation
          valid) = observation := by
  unfold fusedDecoded encodeFusedObservation
  exact OrganicStereoFusedVonBaeyerIngress.unrelabelObservation_relabelObservation enumeration
    observation
    (SourceFusedVonBaeyerObservation.boundedIn_of_validFor_binding binding observation valid)

theorem cyclophaneDecoded_encodeCyclophaneObservation
    (enumeration : V ≃ Fin (Fintype.card V))
    (policy : P93CyclophaneAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : SourceCyclophaneAuthorityObservation policy)
    (valid : observation.ValidFor binding.source) :
    cyclophaneDecoded enumeration
        (encodeCyclophaneObservation enumeration policy binding observation valid) =
      observation := by
  unfold cyclophaneDecoded encodeCyclophaneObservation
  exact OrganicStereoCyclophaneAuthorityIngress.unrelabelObservation_relabelObservation
    enumeration observation
    (SourceCyclophaneAuthorityObservation.boundedIn_of_validFor_binding binding observation valid)

theorem spiroDecoded_encodeSpiroObservation (enumeration : V ≃ Fin (Fintype.card V))
    (policy : P93SpiroAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : SourceSpiroAuthorityObservation policy)
    (valid : SourceSpiroAuthorityObservation.ValidFor binding.source observation) :
    spiroDecoded enumeration
        (encodeSpiroObservation enumeration policy binding observation valid) = observation := by
  unfold spiroDecoded encodeSpiroObservation
  exact OrganicStereoSpiroAuthorityIngress.decodeObservation_relabelObservation enumeration
    observation
    (SourceSpiroAuthorityObservation.boundedIn_of_validFor policy binding observation valid)

theorem relationalDecoded_encodeRelationalObservation (enumeration : V ≃ Fin (Fintype.card V))
    (policy : P93RelationalFullereneAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : P93RelationalFullereneAuthorityObservation policy)
    (valid : observation.ValidFor policy binding.source)
    (spatialExact : observation.spatial? =
      OrganicFiniteSource.encodeSpatial? enumeration binding.shared.spatial?) :
    relationalDecoded policy enumeration binding.shared.spatial?
        (encodeRelationalObservation enumeration policy binding observation valid) =
      observation := by
  unfold relationalDecoded encodeRelationalObservation
  exact OrganicStereoRelationalFullereneInputEncoding.unrelabelObservation_relabelObservation
    enumeration policy observation
    (OrganicStereoRelationalFullereneIngress.relationalObservationBoundedIn_of_validFor
      (OrganicStereoRelationalFullereneIngress.relationalObservationAtomCount_eq binding observation
        valid) valid)
    (OrganicFiniteSource.encodeSpatial? enumeration binding.shared.spatial?) spatialExact

theorem coupledDecoded_encodeCoupledObservation (enumeration : V ≃ Fin (Fintype.card V))
    (policy : P93CoupledRingChainAuthorityPolicy)
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : P93CoupledRingChainAuthorityObservation policy)
    (valid : observation.ValidFor policy binding.source) :
    coupledDecoded enumeration
        (encodeCoupledObservation enumeration policy binding observation valid) = observation := by
  unfold coupledDecoded encodeCoupledObservation
  exact OrganicStereoCoupledRingChainNativeAxes.unrelabelNativeObservation_relabelNativeObservation
    enumeration observation
    (OrganicStereoCoupledRingChainNativeAxes.NativeObservationBoundedIn.of_validFor_binding binding
      observation valid)
    (OrganicStereoCoupledRingChainNativeAxes.nativeObservationNormalizationFixed_of_validFor
      binding.source observation valid)

/-! ## The whole-entry codec -/

/-- Encode one raw whole-source entry.  Every branch is the family's actual native encoder applied
to the row's individual observation, followed by the reconstructed native context and the validity
certificate transported to the native source. -/
def encodeWholeEntry {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    (entry : RawWholeSourceEntry core enumeration) :
    NativeWholeSourceEntry core enumeration :=
  match entry with
  | .legacy binding enumeration_eq graph_eq spatial_eq diagram_eq frame valid =>
      let native := encodeLegacyFrame enumeration binding frame valid
      .legacy binding.shared.graph binding.shared.spatial? binding.shared.diagram? native
        graph_eq spatial_eq diagram_eq
        (by
          unfold LegacyRowValid
          simp only [native, legacySatellite_toFiniteSource]
          rw [shared_encode_eq_source binding enumeration enumeration_eq]
          rw [legacyDecoded_encodeLegacyFrame enumeration binding enumeration_eq frame valid]
          exact valid)
  | .p94 source graph_eq policy observation valid =>
      let resolver :=
        OrganicStereoNativeP94SourceContext.nativeSourceAtomResolver
          core.graph enumeration source graph_eq
      let encoded := EncodedP94AuthorityObservation.ofAuthorityValid
        resolver observation valid
      .p94 policy
        (OrganicStereoNativeP94SourceContext.encodeNativeAuthorityObservation
          core.graph enumeration source graph_eq encoded (by
            simp only [encoded]
            rw [EncodedP94AuthorityObservation.toAuthority_ofAuthorityValid]
            exact valid))
  | .acyclic policy binding enumeration_eq graph_eq spatial_eq diagram_eq observation valid =>
      let native := encodeAcyclicObservation enumeration policy binding observation valid
      .acyclic policy binding.shared.graph binding.shared.spatial? binding.shared.diagram? native
        graph_eq spatial_eq diagram_eq
        (by
          unfold AcyclicRowValid
          simp only [native, acyclicSatellite_toFiniteSource]
          rw [shared_encode_eq_source binding enumeration enumeration_eq]
          rw [acyclicDecoded_encodeAcyclicObservation]
          exact valid)
  | .noncarbon policy binding enumeration_eq graph_eq spatial_eq diagram_eq observation valid =>
      let native := encodeNoncarbonObservation enumeration policy binding observation valid
      .noncarbon policy binding.shared.graph binding.shared.spatial? binding.shared.diagram? native
        graph_eq spatial_eq diagram_eq
        (by
          unfold NoncarbonRowValid
          simp only [native, noncarbonSatellite_toFiniteSource]
          rw [shared_encode_eq_source binding enumeration enumeration_eq]
          rw [noncarbonDecoded_encodeNoncarbonObservation]
          exact valid)
  | .unifiedMonoRing monocyclicPolicy assemblyPolicy binding enumeration_eq graph_eq spatial_eq
      diagram_eq structurallyWellFormed observation valid =>
      let native := encodeCyclicObservation enumeration monocyclicPolicy assemblyPolicy binding
        structurallyWellFormed observation valid
      .unifiedMonoRing monocyclicPolicy assemblyPolicy binding.shared.graph
        binding.shared.spatial? binding.shared.diagram? native graph_eq spatial_eq diagram_eq
        (by
          unfold CyclicRowValid
          simp only [native, cyclicSatellite_toFiniteSource]
          rw [shared_encode_eq_source binding enumeration enumeration_eq]
          rw [cyclicDecoded_encodeCyclicObservation]
          exact valid)
        (by
          have hsrc : (cyclicSatellite monocyclicPolicy assemblyPolicy binding.shared.graph
              binding.shared.spatial? binding.shared.diagram? native).toFiniteSource.encode
                enumeration = binding.source :=
            shared_encode_eq_source binding enumeration enumeration_eq
          rw [hsrc]
          exact structurallyWellFormed)
  | .fusedVonBaeyer fusedPolicy vonBaeyerPolicy binding enumeration_eq graph_eq spatial_eq
      diagram_eq observation valid =>
      let native := encodeFusedObservation enumeration fusedPolicy vonBaeyerPolicy binding
        observation valid
      .fusedVonBaeyer fusedPolicy vonBaeyerPolicy binding.shared.graph binding.shared.spatial?
        binding.shared.diagram? native graph_eq spatial_eq diagram_eq
        (by
          unfold FusedRowValid
          simp only [native, fusedSatellite_toFiniteSource]
          rw [shared_encode_eq_source binding enumeration enumeration_eq]
          rw [fusedDecoded_encodeFusedObservation]
          exact valid)
  | .cyclophane policy binding enumeration_eq graph_eq spatial_eq diagram_eq observation valid =>
      let native := encodeCyclophaneObservation enumeration policy binding observation valid
      .cyclophane policy binding.shared.graph binding.shared.spatial? binding.shared.diagram? native
        graph_eq spatial_eq diagram_eq
        (by
          unfold CyclophaneRowValid
          simp only [native, cyclophaneSatellite_toFiniteSource]
          rw [shared_encode_eq_source binding enumeration enumeration_eq]
          rw [cyclophaneDecoded_encodeCyclophaneObservation]
          exact valid)
  | .spiro policy binding enumeration_eq graph_eq spatial_eq diagram_eq observation valid =>
      let native := encodeSpiroObservation enumeration policy binding observation valid
      .spiro policy binding.shared.graph binding.shared.spatial? binding.shared.diagram? native
        graph_eq spatial_eq diagram_eq
        (by
          unfold SpiroRowValid
          simp only [native, spiroSatellite_toFiniteSource]
          rw [shared_encode_eq_source binding enumeration enumeration_eq]
          rw [spiroDecoded_encodeSpiroObservation]
          exact valid)
  | .fullereneAuthority policy common enumeration_eq graph_eq spatial_eq diagram_eq observation
      valid moleculeBound =>
      let native := common.encodeFamily policy observation
      .fullereneAuthority policy common.binding.shared.graph common.binding.shared.spatial?
        common.binding.shared.diagram? native graph_eq spatial_eq diagram_eq common.molecule
        (by
          simp only [fullereneSatellite_toFiniteSource]
          rw [shared_encode_eq_source common.binding enumeration enumeration_eq]
          exact common.conversion_eq)
        (by
          unfold FullereneRowValid fullereneDecoded
          have contextEq :
              OrganicStereoFullereneAuthorityIngress.FullereneAuthorityDecodeContext.ofEnumeration
                  enumeration common.binding.shared.spatial? =
                OrganicStereoFullereneAuthorityIngress.FullereneAuthorityDecodeContext.ofSource
                  common := by
            cases enumeration_eq
            rfl
          rw [contextEq, FullereneAuthorityDecodeContext.decodeFamily_ofSource]
          simp only [native]
          rw [common.decodeFamily_encodeFamily_of_validFor policy observation valid]
          simp only [fullereneSatellite_toFiniteSource]
          rw [shared_encode_eq_source common.binding enumeration enumeration_eq]
          exact valid)
        (by
          unfold FullereneRowMoleculeBound fullereneDecoded
          have contextEq :
              OrganicStereoFullereneAuthorityIngress.FullereneAuthorityDecodeContext.ofEnumeration
                  enumeration common.binding.shared.spatial? =
                OrganicStereoFullereneAuthorityIngress.FullereneAuthorityDecodeContext.ofSource
                  common := by
            cases enumeration_eq
            rfl
          rw [contextEq, FullereneAuthorityDecodeContext.decodeFamily_ofSource]
          simp only [native]
          rw [common.decodeFamily_encodeFamily_of_validFor policy observation valid]
          simp only [fullereneSatellite_toFiniteSource]
          rw [shared_encode_eq_source common.binding enumeration enumeration_eq]
          exact moleculeBound)
  | .relationalFullerene policy binding enumeration_eq graph_eq spatial_eq diagram_eq observation
      valid =>
      let native := encodeRelationalObservation enumeration policy binding observation valid
      .relationalFullerene policy binding.shared.graph binding.shared.spatial?
        binding.shared.diagram? native graph_eq spatial_eq diagram_eq
        (by
          unfold RelationalRowValid
          simp only [native, relationalSatellite_toFiniteSource]
          rw [shared_encode_eq_source binding enumeration enumeration_eq]
          have spatialExact : observation.spatial? =
              OrganicFiniteSource.encodeSpatial? enumeration binding.shared.spatial? := by
            rw [valid.structureAgreement.2.1.symm]
            rw [← binding.spatial_eq]
            rw [enumeration_eq]
          rw [relationalDecoded_encodeRelationalObservation enumeration policy binding observation
            valid spatialExact]
          exact valid)
  | .coupledRingChain policy binding enumeration_eq graph_eq spatial_eq diagram_eq observation
      valid =>
      let native := encodeCoupledObservation enumeration policy binding observation valid
      .coupledRingChain policy binding.shared.graph binding.shared.spatial? binding.shared.diagram?
        native graph_eq spatial_eq diagram_eq
        (by
          unfold CoupledRowValid
          simp only [native, coupledSatellite_toFiniteSource]
          rw [shared_encode_eq_source binding enumeration enumeration_eq]
          rw [coupledDecoded_encodeCoupledObservation]
          exact valid)

/-! ## The actual concrete decoders -/

/-- Decode one native whole-source entry.  Every branch reconstructs the family source binding from
the native context and the kept enumeration, applies the family's actual native decoder to the
individual observation, and uses the stored validity certificate at the reconstructed source. -/
def decodeWholeEntry {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    (entry : NativeWholeSourceEntry core enumeration) :
    RawWholeSourceEntry core enumeration :=
  match entry with
  | .legacy graph spatial? diagram? frame graph_eq spatial_eq diagram_eq valid =>
      .legacy (reconstructedBinding
          (legacySatellite graph spatial? diagram? frame).toFiniteSource enumeration)
        rfl graph_eq spatial_eq diagram_eq
        (legacyDecoded enumeration graph spatial? diagram? frame) valid
  | .p94 policy native =>
      let recovered :=
        OrganicStereoNativeP94SourceContext.decodeNativeAuthorityObservation
          core.graph enumeration native
      .p94 recovered.source rfl policy recovered.observation recovered.valid
  | .acyclic policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq valid =>
      .acyclic policy (reconstructedBinding
          (acyclicSatellite policy graph spatial? diagram? observation).toFiniteSource enumeration)
        rfl graph_eq spatial_eq diagram_eq
        (acyclicDecoded enumeration observation) valid
  | .noncarbon policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq valid =>
      .noncarbon policy (reconstructedBinding
          (noncarbonSatellite policy graph spatial? diagram? observation).toFiniteSource
          enumeration)
        rfl graph_eq spatial_eq diagram_eq
        (noncarbonDecoded enumeration policy observation) valid
  | .unifiedMonoRing monocyclicPolicy assemblyPolicy graph spatial? diagram? observation graph_eq
      spatial_eq diagram_eq valid structurallyWellFormed =>
      .unifiedMonoRing monocyclicPolicy assemblyPolicy (reconstructedBinding
          (cyclicSatellite monocyclicPolicy assemblyPolicy graph spatial? diagram?
            observation).toFiniteSource enumeration)
        rfl graph_eq spatial_eq diagram_eq structurallyWellFormed
        (cyclicDecoded enumeration observation) valid
  | .fusedVonBaeyer fusedPolicy vonBaeyerPolicy graph spatial? diagram? observation graph_eq
      spatial_eq diagram_eq valid =>
      .fusedVonBaeyer fusedPolicy vonBaeyerPolicy (reconstructedBinding
          (fusedSatellite fusedPolicy vonBaeyerPolicy graph spatial? diagram?
            observation).toFiniteSource enumeration)
        rfl graph_eq spatial_eq diagram_eq
        (fusedDecoded enumeration observation) valid
  | .cyclophane policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq valid =>
      .cyclophane policy (reconstructedBinding
          (cyclophaneSatellite policy graph spatial? diagram? observation).toFiniteSource
          enumeration)
        rfl graph_eq spatial_eq diagram_eq
        (cyclophaneDecoded enumeration observation) valid
  | .spiro policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq valid =>
      .spiro policy (reconstructedBinding
          (spiroSatellite policy graph spatial? diagram? observation).toFiniteSource enumeration)
        rfl graph_eq spatial_eq diagram_eq
        (spiroDecoded enumeration observation) valid
  | .fullereneAuthority policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq
      molecule conversion_eq valid moleculeBound =>
      .fullereneAuthority policy
        { binding := reconstructedBinding
            (fullereneSatellite policy graph spatial? diagram? observation).toFiniteSource
            enumeration
          molecule := molecule
          conversion_eq := conversion_eq }
        rfl graph_eq spatial_eq diagram_eq
        (fullereneDecoded policy enumeration spatial? observation)
        valid moleculeBound
  | .relationalFullerene policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq
      valid =>
      .relationalFullerene policy (reconstructedBinding
          (relationalSatellite policy graph spatial? diagram? enumeration observation).toFiniteSource
          enumeration)
        rfl graph_eq spatial_eq diagram_eq
        (relationalDecoded policy enumeration spatial? observation) valid
  | .coupledRingChain policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq
      valid =>
      .coupledRingChain policy (reconstructedBinding
          (coupledSatellite policy graph spatial? diagram? observation).toFiniteSource enumeration)
        rfl graph_eq spatial_eq diagram_eq
        (coupledDecoded enumeration observation) valid

/-! ## Family tags and native source-channel projections of the native rows

Every native row is one actual encoded observation of one family.  The projections below read the
row's own native source channels: for the P-94 family that is the reconstructed source-free context;
for every other family it is the stored graph/coordinate/drawing context. -/

def NativeWholeSourceEntry.family {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)} :
    NativeWholeSourceEntry core enumeration → SourceFamily
  | .legacy .. => .legacy
  | .p94 .. => .p94
  | .acyclic .. => .acyclic
  | .noncarbon .. => .noncarbon
  | .unifiedMonoRing .. => .unifiedMonoRing
  | .fusedVonBaeyer .. => .fusedVonBaeyer
  | .cyclophane .. => .cyclophane
  | .spiro .. => .spiro
  | .fullereneAuthority .. => .fullereneAuthority
  | .relationalFullerene .. => .relationalFullerene
  | .coupledRingChain .. => .coupledRingChain

def RawWholeSourceEntry.family {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)} :
    RawWholeSourceEntry core enumeration → SourceFamily
  | .legacy .. => .legacy
  | .p94 .. => .p94
  | .acyclic .. => .acyclic
  | .noncarbon .. => .noncarbon
  | .unifiedMonoRing .. => .unifiedMonoRing
  | .fusedVonBaeyer .. => .fusedVonBaeyer
  | .cyclophane .. => .cyclophane
  | .spiro .. => .spiro
  | .fullereneAuthority .. => .fullereneAuthority
  | .relationalFullerene .. => .relationalFullerene
  | .coupledRingChain .. => .coupledRingChain

def NativeWholeSourceEntry.sourceGraph {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)} :
    NativeWholeSourceEntry core enumeration → FiniteAtomInteractionHypergraph V
  | .legacy graph .. => graph
  | .p94 _ native => native.context.toFiniteSource.graph
  | .acyclic _ graph .. => graph
  | .noncarbon _ graph .. => graph
  | .unifiedMonoRing _ _ graph .. => graph
  | .fusedVonBaeyer _ _ graph .. => graph
  | .cyclophane _ graph .. => graph
  | .spiro _ graph .. => graph
  | .fullereneAuthority _ graph .. => graph
  | .relationalFullerene _ graph .. => graph
  | .coupledRingChain _ graph .. => graph

def NativeWholeSourceEntry.sourceSpatial? {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)} :
    NativeWholeSourceEntry core enumeration → Option (V → CartesianPoint3)
  | .legacy _ spatial? .. => spatial?
  | .p94 _ native => native.context.toFiniteSource.spatial?
  | .acyclic _ _ spatial? .. => spatial?
  | .noncarbon _ _ spatial? .. => spatial?
  | .unifiedMonoRing _ _ _ spatial? .. => spatial?
  | .fusedVonBaeyer _ _ _ spatial? .. => spatial?
  | .cyclophane _ _ spatial? .. => spatial?
  | .spiro _ _ spatial? .. => spatial?
  | .fullereneAuthority _ _ spatial? .. => spatial?
  | .relationalFullerene _ _ spatial? .. => spatial?
  | .coupledRingChain _ _ spatial? .. => spatial?

def NativeWholeSourceEntry.sourceDiagram? {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)} :
    NativeWholeSourceEntry core enumeration → Option (OrganicDiagramSource V)
  | .legacy _ _ diagram? .. => diagram?
  | .p94 _ native => native.context.toFiniteSource.diagram?
  | .acyclic _ _ _ diagram? .. => diagram?
  | .noncarbon _ _ _ diagram? .. => diagram?
  | .unifiedMonoRing _ _ _ _ diagram? .. => diagram?
  | .fusedVonBaeyer _ _ _ _ diagram? .. => diagram?
  | .cyclophane _ _ _ diagram? .. => diagram?
  | .spiro _ _ _ diagram? .. => diagram?
  | .fullereneAuthority _ _ _ diagram? .. => diagram?
  | .relationalFullerene _ _ _ diagram? .. => diagram?
  | .coupledRingChain _ _ _ diagram? .. => diagram?

/-- The graph of every native row is the common decoded-output graph: all families store this tie,
including the P-94 family whose reconstructed context is indexed by the common graph. -/
theorem NativeWholeSourceEntry.sourceGraph_eq_core
    {core : OrganicMolecularEvidence V} {enumeration : V ≃ Fin (Fintype.card V)}
    (entry : NativeWholeSourceEntry core enumeration) :
    entry.sourceGraph = core.graph := by
  cases entry with
  | legacy graph spatial? diagram? frame graph_eq spatial_eq diagram_eq valid => exact graph_eq
  | p94 policy native =>
      exact OrganicStereoNativeP94SourceContext.NativeSourceContext.toFiniteSource_graph
        native.context
  | acyclic policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq valid =>
      exact graph_eq
  | noncarbon policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq valid =>
      exact graph_eq
  | unifiedMonoRing monocyclicPolicy assemblyPolicy graph spatial? diagram? observation graph_eq
      spatial_eq diagram_eq valid structurallyWellFormed => exact graph_eq
  | fusedVonBaeyer fusedPolicy vonBaeyerPolicy graph spatial? diagram? observation graph_eq
      spatial_eq diagram_eq valid => exact graph_eq
  | cyclophane policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq valid =>
      exact graph_eq
  | spiro policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq valid =>
      exact graph_eq
  | fullereneAuthority policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq
      molecule conversion_eq valid moleculeBound => exact graph_eq
  | relationalFullerene policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq
      valid => exact graph_eq
  | coupledRingChain policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq
      valid => exact graph_eq

/-- Every non-P-94 native row stores the exact equality of its coordinate channel to the common
decoded core.  The P-94 family is deliberately excluded: its reconstructed source carries its own
conformer geometry at the same graph, and no equality to the core coordinates is stored or claimed. -/
theorem NativeWholeSourceEntry.sourceSpatial?_eq_core_of_ne_p94
    {core : OrganicMolecularEvidence V} {enumeration : V ≃ Fin (Fintype.card V)}
    (entry : NativeWholeSourceEntry core enumeration) (hfamily : entry.family ≠ .p94) :
    entry.sourceSpatial? = core.rationalPositions? := by
  cases entry with
  | legacy graph spatial? diagram? frame graph_eq spatial_eq diagram_eq valid => exact spatial_eq
  | p94 policy native => exact (hfamily rfl).elim
  | acyclic policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq valid =>
      exact spatial_eq
  | noncarbon policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq valid =>
      exact spatial_eq
  | unifiedMonoRing monocyclicPolicy assemblyPolicy graph spatial? diagram? observation graph_eq
      spatial_eq diagram_eq valid structurallyWellFormed => exact spatial_eq
  | fusedVonBaeyer fusedPolicy vonBaeyerPolicy graph spatial? diagram? observation graph_eq
      spatial_eq diagram_eq valid => exact spatial_eq
  | cyclophane policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq valid =>
      exact spatial_eq
  | spiro policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq valid =>
      exact spatial_eq
  | fullereneAuthority policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq
      molecule conversion_eq valid moleculeBound => exact spatial_eq
  | relationalFullerene policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq
      valid => exact spatial_eq
  | coupledRingChain policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq
      valid => exact spatial_eq

theorem NativeWholeSourceEntry.sourceDiagram?_eq_core_of_ne_p94
    {core : OrganicMolecularEvidence V} {enumeration : V ≃ Fin (Fintype.card V)}
    (entry : NativeWholeSourceEntry core enumeration) (hfamily : entry.family ≠ .p94) :
    entry.sourceDiagram? = core.diagram? := by
  cases entry with
  | legacy graph spatial? diagram? frame graph_eq spatial_eq diagram_eq valid => exact diagram_eq
  | p94 policy native => exact (hfamily rfl).elim
  | acyclic policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq valid =>
      exact diagram_eq
  | noncarbon policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq valid =>
      exact diagram_eq
  | unifiedMonoRing monocyclicPolicy assemblyPolicy graph spatial? diagram? observation graph_eq
      spatial_eq diagram_eq valid structurallyWellFormed => exact diagram_eq
  | fusedVonBaeyer fusedPolicy vonBaeyerPolicy graph spatial? diagram? observation graph_eq
      spatial_eq diagram_eq valid => exact diagram_eq
  | cyclophane policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq valid =>
      exact diagram_eq
  | spiro policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq valid =>
      exact diagram_eq
  | fullereneAuthority policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq
      molecule conversion_eq valid moleculeBound => exact diagram_eq
  | relationalFullerene policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq
      valid => exact diagram_eq
  | coupledRingChain policy graph spatial? diagram? observation graph_eq spatial_eq diagram_eq
      valid => exact diagram_eq

/-! ## The whole request and its native representation -/

/-- The whole independent request: one independently supplied core, one explicit enumeration, and
one ordered list of individual raw family observations.  The list retains cross-family order,
repetitions and every payload. -/
structure WholeSourceRequest (V : Type) [DecidableEq V] [Fintype V] where
  core : OrganicMolecularEvidence V
  enumeration : V ≃ Fin (Fintype.card V)
  entries : List (RawWholeSourceEntry (V := V) core enumeration)

/-- The actual assembled representation.  It stores the actual upstream assembled molecular
representation, the retained enumeration, its canonical finite representation together with the
actual equality relating the two, and one ordered list of actual encoded native rows indexed by the
decoded output core.  No raw request, raw observation, certified source or pre-assembled copy of the
original input is stored. -/
structure WholeSourceRepresentation (V : Type) [DecidableEq V] [Fintype V] where
  assembled : OrganicMolecularRepresentation V
  enumeration : V ≃ Fin (Fintype.card V)
  canonical : CanonicalOrganicMolecularRepresentation V
  canonical_eq : canonical = canonicalizeFin assembled enumeration
  entries : List (NativeWholeSourceEntry (V := V) (decodeEvidence assembled) enumeration)

def assembleWhole (request : WholeSourceRequest V) : WholeSourceRepresentation V where
  assembled := assembleEvidence request.core
  enumeration := request.enumeration
  canonical := canonicalizeFin (assembleEvidence request.core) request.enumeration
  canonical_eq := rfl
  entries := (decodeEvidence_assembleEvidence request.core).symm ▸
    request.entries.map (fun entry => encodeWholeEntry entry)

def decodeWhole (representation : WholeSourceRepresentation V) : WholeSourceRequest V where
  core := decodeEvidence representation.assembled
  enumeration := representation.enumeration
  entries := representation.entries.map (fun entry => decodeWholeEntry entry)

@[simp] theorem assembleWhole_assembled (request : WholeSourceRequest V) :
    (assembleWhole request).assembled = assembleEvidence request.core := rfl

@[simp] theorem assembleWhole_enumeration (request : WholeSourceRequest V) :
    (assembleWhole request).enumeration = request.enumeration := rfl

@[simp] theorem assembleWhole_canonical (request : WholeSourceRequest V) :
    (assembleWhole request).canonical =
      canonicalizeFin (assembleEvidence request.core) request.enumeration := rfl

@[simp] theorem assembleWhole_canonical_eq (request : WholeSourceRequest V) :
    (assembleWhole request).canonical_eq =
      (rfl : canonicalizeFin (assembleEvidence request.core) request.enumeration =
        canonicalizeFin (assembleEvidence request.core) request.enumeration) := rfl

/-- The stored canonical finite representation decodes exactly to the actual assembled
representation. -/
theorem assembleWhole_canonical_decodes (request : WholeSourceRequest V) :
    canonicalDecode (assembleWhole request).canonical =
      (assembleWhole request).assembled := by
  rw [assembleWhole_canonical, assembleWhole_assembled]
  exact canonicalDecode_canonicalizeFin (assembleEvidence request.core) request.enumeration

/-! ## Exact per-branch raw-to-native inverse

Each ext lemma is stated over variables only, so the source reconstruction is substituted in a
well-typed context.  The whole-entry inverse below then applies these lemmas to the actual decoded
constructor forms. -/

theorem rawLegacy_ext {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    {binding₁ binding₂ : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V}
    {enumeration_eq₁ : binding₁.enumeration = enumeration}
    {enumeration_eq₂ : binding₂.enumeration = enumeration}
    {graph_eq₁ : binding₁.shared.graph = core.graph}
    {graph_eq₂ : binding₂.shared.graph = core.graph}
    {spatial_eq₁ : binding₁.shared.spatial? = core.rationalPositions?}
    {spatial_eq₂ : binding₂.shared.spatial? = core.rationalPositions?}
    {diagram_eq₁ : binding₁.shared.diagram? = core.diagram?}
    {diagram_eq₂ : binding₂.shared.diagram? = core.diagram?}
    {frame₁ frame₂ : SourcePhysicalFrame}
    {valid₁ : frame₁.ValidFor binding₁.source}
    {valid₂ : frame₂.ValidFor binding₂.source}
    (hb : binding₁ = binding₂) (hf : frame₁ = frame₂) :
    RawWholeSourceEntry.legacy binding₁ enumeration_eq₁ graph_eq₁ spatial_eq₁ diagram_eq₁ frame₁
        valid₁ =
      RawWholeSourceEntry.legacy binding₂ enumeration_eq₂ graph_eq₂ spatial_eq₂ diagram_eq₂ frame₂
        valid₂ := by
  subst hb
  subst hf
  rw [Subsingleton.elim enumeration_eq₁ enumeration_eq₂,
    Subsingleton.elim graph_eq₁ graph_eq₂,
    Subsingleton.elim spatial_eq₁ spatial_eq₂,
    Subsingleton.elim diagram_eq₁ diagram_eq₂,
    Subsingleton.elim valid₁ valid₂]

theorem rawAcyclic_ext {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)} {policy : P93AcyclicAuthorityPolicy}
    {binding₁ binding₂ : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V}
    {enumeration_eq₁ : binding₁.enumeration = enumeration}
    {enumeration_eq₂ : binding₂.enumeration = enumeration}
    {graph_eq₁ : binding₁.shared.graph = core.graph}
    {graph_eq₂ : binding₂.shared.graph = core.graph}
    {spatial_eq₁ : binding₁.shared.spatial? = core.rationalPositions?}
    {spatial_eq₂ : binding₂.shared.spatial? = core.rationalPositions?}
    {diagram_eq₁ : binding₁.shared.diagram? = core.diagram?}
    {diagram_eq₂ : binding₂.shared.diagram? = core.diagram?}
    {observation₁ observation₂ : SourceAcyclicObservation policy}
    {valid₁ : observation₁.ValidFor binding₁.source}
    {valid₂ : observation₂.ValidFor binding₂.source}
    (hb : binding₁ = binding₂) (ho : observation₁ = observation₂) :
    RawWholeSourceEntry.acyclic policy binding₁ enumeration_eq₁ graph_eq₁ spatial_eq₁ diagram_eq₁
        observation₁ valid₁ =
      RawWholeSourceEntry.acyclic policy binding₂ enumeration_eq₂ graph_eq₂ spatial_eq₂ diagram_eq₂
        observation₂ valid₂ := by
  subst hb
  subst ho
  rw [Subsingleton.elim enumeration_eq₁ enumeration_eq₂,
    Subsingleton.elim graph_eq₁ graph_eq₂,
    Subsingleton.elim spatial_eq₁ spatial_eq₂,
    Subsingleton.elim diagram_eq₁ diagram_eq₂,
    Subsingleton.elim valid₁ valid₂]

theorem rawNoncarbon_ext {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    {policy : P93NoncarbonTetrahedralAuthorityPolicy}
    {binding₁ binding₂ : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V}
    {enumeration_eq₁ : binding₁.enumeration = enumeration}
    {enumeration_eq₂ : binding₂.enumeration = enumeration}
    {graph_eq₁ : binding₁.shared.graph = core.graph}
    {graph_eq₂ : binding₂.shared.graph = core.graph}
    {spatial_eq₁ : binding₁.shared.spatial? = core.rationalPositions?}
    {spatial_eq₂ : binding₂.shared.spatial? = core.rationalPositions?}
    {diagram_eq₁ : binding₁.shared.diagram? = core.diagram?}
    {diagram_eq₂ : binding₂.shared.diagram? = core.diagram?}
    {observation₁ observation₂ : SourceNoncarbonObservation policy}
    {valid₁ : SourceNoncarbonObservation.ValidFor policy binding₁.source observation₁}
    {valid₂ : SourceNoncarbonObservation.ValidFor policy binding₂.source observation₂}
    (hb : binding₁ = binding₂) (ho : observation₁ = observation₂) :
    RawWholeSourceEntry.noncarbon policy binding₁ enumeration_eq₁ graph_eq₁ spatial_eq₁ diagram_eq₁
        observation₁ valid₁ =
      RawWholeSourceEntry.noncarbon policy binding₂ enumeration_eq₂ graph_eq₂ spatial_eq₂
        diagram_eq₂ observation₂ valid₂ := by
  subst hb
  subst ho
  rw [Subsingleton.elim enumeration_eq₁ enumeration_eq₂,
    Subsingleton.elim graph_eq₁ graph_eq₂,
    Subsingleton.elim spatial_eq₁ spatial_eq₂,
    Subsingleton.elim diagram_eq₁ diagram_eq₂,
    Subsingleton.elim valid₁ valid₂]

theorem rawUnifiedMonoRing_ext {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy}
    {binding₁ binding₂ : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V}
    {enumeration_eq₁ : binding₁.enumeration = enumeration}
    {enumeration_eq₂ : binding₂.enumeration = enumeration}
    {graph_eq₁ : binding₁.shared.graph = core.graph}
    {graph_eq₂ : binding₂.shared.graph = core.graph}
    {spatial_eq₁ : binding₁.shared.spatial? = core.rationalPositions?}
    {spatial_eq₂ : binding₂.shared.spatial? = core.rationalPositions?}
    {diagram_eq₁ : binding₁.shared.diagram? = core.diagram?}
    {diagram_eq₂ : binding₂.shared.diagram? = core.diagram?}
    {structurallyWellFormed₁ : binding₁.source.molecule.StructurallyWellFormed}
    {structurallyWellFormed₂ : binding₂.source.molecule.StructurallyWellFormed}
    {observation₁ observation₂ : SourceCyclicObservation monocyclicPolicy assemblyPolicy}
    {valid₁ : observation₁.ValidFor binding₁.source}
    {valid₂ : observation₂.ValidFor binding₂.source}
    (hb : binding₁ = binding₂) (ho : observation₁ = observation₂) :
    RawWholeSourceEntry.unifiedMonoRing monocyclicPolicy assemblyPolicy binding₁ enumeration_eq₁
        graph_eq₁ spatial_eq₁ diagram_eq₁ structurallyWellFormed₁ observation₁ valid₁ =
      RawWholeSourceEntry.unifiedMonoRing monocyclicPolicy assemblyPolicy binding₂ enumeration_eq₂
        graph_eq₂ spatial_eq₂ diagram_eq₂ structurallyWellFormed₂ observation₂ valid₂ := by
  subst hb
  subst ho
  rw [Subsingleton.elim enumeration_eq₁ enumeration_eq₂,
    Subsingleton.elim graph_eq₁ graph_eq₂,
    Subsingleton.elim spatial_eq₁ spatial_eq₂,
    Subsingleton.elim diagram_eq₁ diagram_eq₂,
    Subsingleton.elim structurallyWellFormed₁ structurallyWellFormed₂,
    Subsingleton.elim valid₁ valid₂]

theorem rawFused_ext {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    {fusedPolicy : P93FusedAuthorityPolicy}
    {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    {binding₁ binding₂ : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V}
    {enumeration_eq₁ : binding₁.enumeration = enumeration}
    {enumeration_eq₂ : binding₂.enumeration = enumeration}
    {graph_eq₁ : binding₁.shared.graph = core.graph}
    {graph_eq₂ : binding₂.shared.graph = core.graph}
    {spatial_eq₁ : binding₁.shared.spatial? = core.rationalPositions?}
    {spatial_eq₂ : binding₂.shared.spatial? = core.rationalPositions?}
    {diagram_eq₁ : binding₁.shared.diagram? = core.diagram?}
    {diagram_eq₂ : binding₂.shared.diagram? = core.diagram?}
    {observation₁ observation₂ : SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy}
    {valid₁ : observation₁.ValidFor binding₁.source}
    {valid₂ : observation₂.ValidFor binding₂.source}
    (hb : binding₁ = binding₂) (ho : observation₁ = observation₂) :
    RawWholeSourceEntry.fusedVonBaeyer fusedPolicy vonBaeyerPolicy binding₁ enumeration_eq₁
        graph_eq₁ spatial_eq₁ diagram_eq₁ observation₁ valid₁ =
      RawWholeSourceEntry.fusedVonBaeyer fusedPolicy vonBaeyerPolicy binding₂ enumeration_eq₂
        graph_eq₂ spatial_eq₂ diagram_eq₂ observation₂ valid₂ := by
  subst hb
  subst ho
  rw [Subsingleton.elim enumeration_eq₁ enumeration_eq₂,
    Subsingleton.elim graph_eq₁ graph_eq₂,
    Subsingleton.elim spatial_eq₁ spatial_eq₂,
    Subsingleton.elim diagram_eq₁ diagram_eq₂,
    Subsingleton.elim valid₁ valid₂]

theorem rawCyclophane_ext {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)} {policy : P93CyclophaneAuthorityPolicy}
    {binding₁ binding₂ : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V}
    {enumeration_eq₁ : binding₁.enumeration = enumeration}
    {enumeration_eq₂ : binding₂.enumeration = enumeration}
    {graph_eq₁ : binding₁.shared.graph = core.graph}
    {graph_eq₂ : binding₂.shared.graph = core.graph}
    {spatial_eq₁ : binding₁.shared.spatial? = core.rationalPositions?}
    {spatial_eq₂ : binding₂.shared.spatial? = core.rationalPositions?}
    {diagram_eq₁ : binding₁.shared.diagram? = core.diagram?}
    {diagram_eq₂ : binding₂.shared.diagram? = core.diagram?}
    {observation₁ observation₂ : SourceCyclophaneAuthorityObservation policy}
    {valid₁ : observation₁.ValidFor binding₁.source}
    {valid₂ : observation₂.ValidFor binding₂.source}
    (hb : binding₁ = binding₂) (ho : observation₁ = observation₂) :
    RawWholeSourceEntry.cyclophane policy binding₁ enumeration_eq₁ graph_eq₁ spatial_eq₁
        diagram_eq₁ observation₁ valid₁ =
      RawWholeSourceEntry.cyclophane policy binding₂ enumeration_eq₂ graph_eq₂ spatial_eq₂
        diagram_eq₂ observation₂ valid₂ := by
  subst hb
  subst ho
  rw [Subsingleton.elim enumeration_eq₁ enumeration_eq₂,
    Subsingleton.elim graph_eq₁ graph_eq₂,
    Subsingleton.elim spatial_eq₁ spatial_eq₂,
    Subsingleton.elim diagram_eq₁ diagram_eq₂,
    Subsingleton.elim valid₁ valid₂]

theorem rawSpiro_ext {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)} {policy : P93SpiroAuthorityPolicy}
    {binding₁ binding₂ : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V}
    {enumeration_eq₁ : binding₁.enumeration = enumeration}
    {enumeration_eq₂ : binding₂.enumeration = enumeration}
    {graph_eq₁ : binding₁.shared.graph = core.graph}
    {graph_eq₂ : binding₂.shared.graph = core.graph}
    {spatial_eq₁ : binding₁.shared.spatial? = core.rationalPositions?}
    {spatial_eq₂ : binding₂.shared.spatial? = core.rationalPositions?}
    {diagram_eq₁ : binding₁.shared.diagram? = core.diagram?}
    {diagram_eq₂ : binding₂.shared.diagram? = core.diagram?}
    {observation₁ observation₂ : SourceSpiroAuthorityObservation policy}
    {valid₁ : SourceSpiroAuthorityObservation.ValidFor binding₁.source observation₁}
    {valid₂ : SourceSpiroAuthorityObservation.ValidFor binding₂.source observation₂}
    (hb : binding₁ = binding₂) (ho : observation₁ = observation₂) :
    RawWholeSourceEntry.spiro policy binding₁ enumeration_eq₁ graph_eq₁ spatial_eq₁ diagram_eq₁
        observation₁ valid₁ =
      RawWholeSourceEntry.spiro policy binding₂ enumeration_eq₂ graph_eq₂ spatial_eq₂ diagram_eq₂
        observation₂ valid₂ := by
  subst hb
  subst ho
  rw [Subsingleton.elim enumeration_eq₁ enumeration_eq₂,
    Subsingleton.elim graph_eq₁ graph_eq₂,
    Subsingleton.elim spatial_eq₁ spatial_eq₂,
    Subsingleton.elim diagram_eq₁ diagram_eq₂,
    Subsingleton.elim valid₁ valid₂]

/-- Two common fullerene sources with the same binding and molecule are equal; the conversion
certificate is a proposition and is proof-irrelevant. -/
theorem fullereneCommon_ext
    {first second : OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource V}
    (hbinding : first.binding = second.binding)
    (hmolecule : first.molecule = second.molecule) : first = second := by
  obtain ⟨firstBinding, firstMolecule, firstConversion⟩ := first
  obtain ⟨secondBinding, secondMolecule, secondConversion⟩ := second
  dsimp only at hbinding hmolecule
  subst hbinding
  subst hmolecule
  have conversionEq : firstConversion = secondConversion := Subsingleton.elim _ _
  rw [conversionEq]

theorem rawFullerene_ext {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)} {policy : P93FullereneAuthorityPolicy}
    {common₁ common₂ :
      OrganicStereoFullereneAuthorityIngress.FullereneAuthorityCommonSource V}
    {enumeration_eq₁ : common₁.binding.enumeration = enumeration}
    {enumeration_eq₂ : common₂.binding.enumeration = enumeration}
    {graph_eq₁ : common₁.binding.shared.graph = core.graph}
    {graph_eq₂ : common₂.binding.shared.graph = core.graph}
    {spatial_eq₁ : common₁.binding.shared.spatial? = core.rationalPositions?}
    {spatial_eq₂ : common₂.binding.shared.spatial? = core.rationalPositions?}
    {diagram_eq₁ : common₁.binding.shared.diagram? = core.diagram?}
    {diagram_eq₂ : common₂.binding.shared.diagram? = core.diagram?}
    {observation₁ observation₂ : SourceFullereneAuthorityObservation policy}
    {valid₁ : observation₁.ValidFor common₁.binding.source}
    {valid₂ : observation₂.ValidFor common₂.binding.source}
    {moleculeBound₁ : observation₁.MoleculeBoundTo common₁.binding.source}
    {moleculeBound₂ : observation₂.MoleculeBoundTo common₂.binding.source}
    (hc : common₁ = common₂) (ho : observation₁ = observation₂) :
    RawWholeSourceEntry.fullereneAuthority policy common₁ enumeration_eq₁ graph_eq₁ spatial_eq₁
        diagram_eq₁ observation₁ valid₁ moleculeBound₁ =
      RawWholeSourceEntry.fullereneAuthority policy common₂ enumeration_eq₂ graph_eq₂ spatial_eq₂
        diagram_eq₂ observation₂ valid₂ moleculeBound₂ := by
  subst hc
  subst ho
  rw [Subsingleton.elim enumeration_eq₁ enumeration_eq₂,
    Subsingleton.elim graph_eq₁ graph_eq₂,
    Subsingleton.elim spatial_eq₁ spatial_eq₂,
    Subsingleton.elim diagram_eq₁ diagram_eq₂,
    Subsingleton.elim valid₁ valid₂,
    Subsingleton.elim moleculeBound₁ moleculeBound₂]

theorem rawRelational_ext {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    {policy : P93RelationalFullereneAuthorityPolicy}
    {binding₁ binding₂ : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V}
    {enumeration_eq₁ : binding₁.enumeration = enumeration}
    {enumeration_eq₂ : binding₂.enumeration = enumeration}
    {graph_eq₁ : binding₁.shared.graph = core.graph}
    {graph_eq₂ : binding₂.shared.graph = core.graph}
    {spatial_eq₁ : binding₁.shared.spatial? = core.rationalPositions?}
    {spatial_eq₂ : binding₂.shared.spatial? = core.rationalPositions?}
    {diagram_eq₁ : binding₁.shared.diagram? = core.diagram?}
    {diagram_eq₂ : binding₂.shared.diagram? = core.diagram?}
    {observation₁ observation₂ : P93RelationalFullereneAuthorityObservation policy}
    {valid₁ : observation₁.ValidFor policy binding₁.source}
    {valid₂ : observation₂.ValidFor policy binding₂.source}
    (hb : binding₁ = binding₂) (ho : observation₁ = observation₂) :
    RawWholeSourceEntry.relationalFullerene policy binding₁ enumeration_eq₁ graph_eq₁ spatial_eq₁
        diagram_eq₁ observation₁ valid₁ =
      RawWholeSourceEntry.relationalFullerene policy binding₂ enumeration_eq₂ graph_eq₂ spatial_eq₂
        diagram_eq₂ observation₂ valid₂ := by
  subst hb
  subst ho
  rw [Subsingleton.elim enumeration_eq₁ enumeration_eq₂,
    Subsingleton.elim graph_eq₁ graph_eq₂,
    Subsingleton.elim spatial_eq₁ spatial_eq₂,
    Subsingleton.elim diagram_eq₁ diagram_eq₂,
    Subsingleton.elim valid₁ valid₂]

theorem rawCoupled_ext {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    {policy : P93CoupledRingChainAuthorityPolicy}
    {binding₁ binding₂ : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V}
    {enumeration_eq₁ : binding₁.enumeration = enumeration}
    {enumeration_eq₂ : binding₂.enumeration = enumeration}
    {graph_eq₁ : binding₁.shared.graph = core.graph}
    {graph_eq₂ : binding₂.shared.graph = core.graph}
    {spatial_eq₁ : binding₁.shared.spatial? = core.rationalPositions?}
    {spatial_eq₂ : binding₂.shared.spatial? = core.rationalPositions?}
    {diagram_eq₁ : binding₁.shared.diagram? = core.diagram?}
    {diagram_eq₂ : binding₂.shared.diagram? = core.diagram?}
    {observation₁ observation₂ : P93CoupledRingChainAuthorityObservation policy}
    {valid₁ : observation₁.ValidFor policy binding₁.source}
    {valid₂ : observation₂.ValidFor policy binding₂.source}
    (hb : binding₁ = binding₂) (ho : observation₁ = observation₂) :
    RawWholeSourceEntry.coupledRingChain policy binding₁ enumeration_eq₁ graph_eq₁ spatial_eq₁
        diagram_eq₁ observation₁ valid₁ =
      RawWholeSourceEntry.coupledRingChain policy binding₂ enumeration_eq₂ graph_eq₂ spatial_eq₂
        diagram_eq₂ observation₂ valid₂ := by
  subst hb
  subst ho
  rw [Subsingleton.elim enumeration_eq₁ enumeration_eq₂,
    Subsingleton.elim graph_eq₁ graph_eq₂,
    Subsingleton.elim spatial_eq₁ spatial_eq₂,
    Subsingleton.elim diagram_eq₁ diagram_eq₂,
    Subsingleton.elim valid₁ valid₂]

theorem rawP94_ext {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    {source₁ source₂ : CertifiedAuthoritativeChemicalInput}
    {graph_eq₁ : source₁.input.molecule = core.graph.encode enumeration}
    {graph_eq₂ : source₂.input.molecule = core.graph.encode enumeration}
    {policy : P94AuthorityPolicy}
    {observation₁ observation₂ : P94AuthorityObservation policy}
    {valid₁ : observation₁.ValidFor policy source₁.input}
    {valid₂ : observation₂.ValidFor policy source₂.input}
    (hs : source₁ = source₂) (ho : observation₁ = observation₂) :
    RawWholeSourceEntry.p94 source₁ graph_eq₁ policy observation₁ valid₁ =
      RawWholeSourceEntry.p94 source₂ graph_eq₂ policy observation₂ valid₂ := by
  subst hs
  subst ho
  rw [Subsingleton.elim graph_eq₁ graph_eq₂,
    Subsingleton.elim valid₁ valid₂]

/-- The exact whole-entry inverse: decoding the actual native encoding of one raw individual
observation returns that observation literally, including the reconstructed source binding, the
family payload and every validity proof. -/
theorem decodeWholeEntry_encodeWholeEntry {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    (entry : RawWholeSourceEntry core enumeration) :
    decodeWholeEntry (encodeWholeEntry entry) = entry := by
  cases entry with
  | legacy binding enumeration_eq graph_eq spatial_eq diagram_eq frame valid =>
      dsimp only [encodeWholeEntry, decodeWholeEntry]
      refine rawLegacy_ext (hb := ?_)
        (hf := legacyDecoded_encodeLegacyFrame enumeration binding enumeration_eq frame valid)
      simp only [legacySatellite_toFiniteSource]
      exact reconstructedBinding_eq binding enumeration enumeration_eq
  | p94 source graph_eq policy observation valid =>
      dsimp only [encodeWholeEntry, decodeWholeEntry]
      let resolver :=
        OrganicStereoNativeP94SourceContext.nativeSourceAtomResolver
          core.graph enumeration source graph_eq
      let encoded := EncodedP94AuthorityObservation.ofAuthorityValid resolver observation valid
      let validEncoded : (EncodedP94AuthorityObservation.toAuthority resolver encoded).ValidFor
          policy source.input := by
        rw [EncodedP94AuthorityObservation.toAuthority_ofAuthorityValid]
        exact valid
      have recovered :=
        OrganicStereoNativeP94SourceContext.decodeNativeAuthorityObservation_encodeNativeAuthorityObservation
          core.graph enumeration source graph_eq encoded validEncoded
      refine rawP94_ext (hs := recovered.1) (ho := ?_)
      exact recovered.2.trans
        (EncodedP94AuthorityObservation.toAuthority_ofAuthorityValid resolver observation valid)
  | acyclic policy binding enumeration_eq graph_eq spatial_eq diagram_eq observation valid =>
      dsimp only [encodeWholeEntry, decodeWholeEntry]
      refine rawAcyclic_ext (hb := ?_)
        (ho := acyclicDecoded_encodeAcyclicObservation enumeration policy binding observation valid)
      simp only [acyclicSatellite_toFiniteSource]
      exact reconstructedBinding_eq binding enumeration enumeration_eq
  | noncarbon policy binding enumeration_eq graph_eq spatial_eq diagram_eq observation valid =>
      dsimp only [encodeWholeEntry, decodeWholeEntry]
      refine rawNoncarbon_ext (hb := ?_)
        (ho := noncarbonDecoded_encodeNoncarbonObservation enumeration policy binding observation
          valid)
      simp only [noncarbonSatellite_toFiniteSource]
      exact reconstructedBinding_eq binding enumeration enumeration_eq
  | unifiedMonoRing monocyclicPolicy assemblyPolicy binding enumeration_eq graph_eq spatial_eq
      diagram_eq structurallyWellFormed observation valid =>
      dsimp only [encodeWholeEntry, decodeWholeEntry]
      refine rawUnifiedMonoRing_ext (hb := ?_)
        (ho := cyclicDecoded_encodeCyclicObservation enumeration monocyclicPolicy assemblyPolicy
          binding structurallyWellFormed observation valid)
      simp only [cyclicSatellite_toFiniteSource]
      exact reconstructedBinding_eq binding enumeration enumeration_eq
  | fusedVonBaeyer fusedPolicy vonBaeyerPolicy binding enumeration_eq graph_eq spatial_eq diagram_eq
      observation valid =>
      dsimp only [encodeWholeEntry, decodeWholeEntry]
      refine rawFused_ext (hb := ?_)
        (ho := fusedDecoded_encodeFusedObservation enumeration fusedPolicy vonBaeyerPolicy binding
          observation valid)
      simp only [fusedSatellite_toFiniteSource]
      exact reconstructedBinding_eq binding enumeration enumeration_eq
  | cyclophane policy binding enumeration_eq graph_eq spatial_eq diagram_eq observation valid =>
      dsimp only [encodeWholeEntry, decodeWholeEntry]
      refine rawCyclophane_ext (hb := ?_)
        (ho := cyclophaneDecoded_encodeCyclophaneObservation enumeration policy binding observation
          valid)
      simp only [cyclophaneSatellite_toFiniteSource]
      exact reconstructedBinding_eq binding enumeration enumeration_eq
  | spiro policy binding enumeration_eq graph_eq spatial_eq diagram_eq observation valid =>
      dsimp only [encodeWholeEntry, decodeWholeEntry]
      refine rawSpiro_ext (hb := ?_)
        (ho := spiroDecoded_encodeSpiroObservation enumeration policy binding observation valid)
      simp only [spiroSatellite_toFiniteSource]
      exact reconstructedBinding_eq binding enumeration enumeration_eq
  | fullereneAuthority policy common enumeration_eq graph_eq spatial_eq diagram_eq observation valid
      moleculeBound =>
      dsimp only [encodeWholeEntry, decodeWholeEntry]
      refine rawFullerene_ext (hc := ?_) (ho := ?_)
      · apply fullereneCommon_ext
        · simp only [fullereneSatellite_toFiniteSource]
          exact reconstructedBinding_eq common.binding enumeration enumeration_eq
        · rfl
      · unfold fullereneDecoded
        have contextEq :
            OrganicStereoFullereneAuthorityIngress.FullereneAuthorityDecodeContext.ofEnumeration
                enumeration common.binding.shared.spatial? =
              OrganicStereoFullereneAuthorityIngress.FullereneAuthorityDecodeContext.ofSource
                common := by
          cases enumeration_eq
          rfl
        rw [contextEq, FullereneAuthorityDecodeContext.decodeFamily_ofSource]
        exact common.decodeFamily_encodeFamily_of_validFor policy observation valid
  | relationalFullerene policy binding enumeration_eq graph_eq spatial_eq diagram_eq observation
      valid =>
      dsimp only [encodeWholeEntry, decodeWholeEntry]
      have spatialExact : observation.spatial? =
          OrganicFiniteSource.encodeSpatial? enumeration binding.shared.spatial? := by
        rw [valid.structureAgreement.2.1.symm]
        rw [← binding.spatial_eq]
        rw [enumeration_eq]
      refine rawRelational_ext (hb := ?_)
        (ho := relationalDecoded_encodeRelationalObservation enumeration policy binding observation
          valid spatialExact)
      simp only [relationalSatellite_toFiniteSource]
      exact reconstructedBinding_eq binding enumeration enumeration_eq
  | coupledRingChain policy binding enumeration_eq graph_eq spatial_eq diagram_eq observation valid =>
      dsimp only [encodeWholeEntry, decodeWholeEntry]
      refine rawCoupled_ext (hb := ?_)
        (ho := coupledDecoded_encodeCoupledObservation enumeration policy binding observation valid)
      simp only [coupledSatellite_toFiniteSource]
      exact reconstructedBinding_eq binding enumeration enumeration_eq

/-! ## Exact whole-list and whole-request inverse -/

theorem map_decode_encode_eq_id {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    (entries : List (RawWholeSourceEntry core enumeration)) :
    entries.map (fun entry => decodeWholeEntry (encodeWholeEntry entry)) = entries := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      simp [decodeWholeEntry_encodeWholeEntry, ih]

theorem transport_map_decode_encode_heq {core decoded : OrganicMolecularEvidence V}
    (h : decoded = core) (enumeration : V ≃ Fin (Fintype.card V))
    (entries : List (RawWholeSourceEntry core enumeration)) :
    HEq ((h.symm ▸ entries.map (fun entry => encodeWholeEntry entry)).map
        (fun entry => decodeWholeEntry entry)) entries := by
  cases h
  rw [List.map_map]
  change HEq (entries.map (fun entry : RawWholeSourceEntry core enumeration =>
    decodeWholeEntry (encodeWholeEntry entry))) entries
  rw [map_decode_encode_eq_id]

theorem transport_map_decode_encode_length {core decoded : OrganicMolecularEvidence V}
    (h : decoded = core) (enumeration : V ≃ Fin (Fintype.card V))
    (entries : List (RawWholeSourceEntry core enumeration)) :
    ((h.symm ▸ entries.map (fun entry => encodeWholeEntry entry)).map
        (fun entry => decodeWholeEntry entry)).length = entries.length := by
  cases h
  rw [List.map_map]
  change (entries.map (fun entry : RawWholeSourceEntry core enumeration =>
    decodeWholeEntry (encodeWholeEntry entry))).length = entries.length
  rw [map_decode_encode_eq_id]

theorem transport_map_decode_encode_getElem?_heq {core decoded : OrganicMolecularEvidence V}
    (h : decoded = core) (enumeration : V ≃ Fin (Fintype.card V))
    (entries : List (RawWholeSourceEntry core enumeration)) (index : Nat) :
    HEq (((h.symm ▸ entries.map (fun entry => encodeWholeEntry entry)).map
        (fun entry => decodeWholeEntry entry))[index]?) (entries[index]?) := by
  cases h
  rw [List.map_map]
  change HEq ((entries.map (fun entry : RawWholeSourceEntry core enumeration =>
    decodeWholeEntry (encodeWholeEntry entry)))[index]?) (entries[index]?)
  rw [map_decode_encode_eq_id]

theorem WholeSourceRequest.extEq {first second : WholeSourceRequest V}
    (core : first.core = second.core)
    (enumeration : first.enumeration = second.enumeration)
    (entries : HEq first.entries second.entries) : first = second := by
  obtain ⟨firstCore, firstEnumeration, firstEntries⟩ := first
  obtain ⟨secondCore, secondEnumeration, secondEntries⟩ := second
  cases core
  cases enumeration
  have entriesEq : firstEntries = secondEntries := eq_of_heq entries
  rw [entriesEq]

theorem decodeWhole_entries_heq (request : WholeSourceRequest V) :
    HEq (decodeWhole (assembleWhole request)).entries request.entries :=
  transport_map_decode_encode_heq (decodeEvidence_assembleEvidence request.core)
    request.enumeration request.entries

theorem decodeWhole_entries_length (request : WholeSourceRequest V) :
    (decodeWhole (assembleWhole request)).entries.length = request.entries.length :=
  transport_map_decode_encode_length (decodeEvidence_assembleEvidence request.core)
    request.enumeration request.entries

theorem decodeWhole_getElem?_heq (request : WholeSourceRequest V) (index : Nat) :
    HEq ((decodeWhole (assembleWhole request)).entries[index]?)
      (request.entries[index]?) :=
  transport_map_decode_encode_getElem?_heq (decodeEvidence_assembleEvidence request.core)
    request.enumeration request.entries index

/-- **Main inverse.**  Decoding the actual whole assembly returns the whole independent request
literally: the same core, the same enumeration, and the same ordered individual raw entry list. -/
theorem decodeWhole_assembleWhole (request : WholeSourceRequest V) :
    decodeWhole (assembleWhole request) = request := by
  apply WholeSourceRequest.extEq
  · exact decodeEvidence_assembleEvidence request.core
  · rfl
  · exact decodeWhole_entries_heq request

theorem assembleWhole_injective : Function.Injective (assembleWhole : WholeSourceRequest V →
    WholeSourceRepresentation V) := by
  intro first second equal
  have applied : decodeWhole (assembleWhole first) = decodeWhole (assembleWhole second) :=
    congrArg decodeWhole equal
  rwa [decodeWhole_assembleWhole, decodeWhole_assembleWhole] at applied

/-! ## Output projections and their exact source ties -/

/-- The actual assembled graph is the core graph. -/
theorem assembleWhole_stateGraph_eq_core (request : WholeSourceRequest V) :
    (assembleWhole request).assembled.stateGraph = request.core.graph :=
  OrganicStereoMolecularAssemblyProjections.assemble_stateGraph request.core

/-- The actual assembled rational-coordinate channel is the core channel. -/
theorem assembleWhole_stateRationalPositions?_eq_core (request : WholeSourceRequest V) :
    (assembleWhole request).assembled.stateRationalPositions? = request.core.rationalPositions? :=
  OrganicStereoMolecularAssemblyProjections.assemble_stateRationalPositions? request.core

/-- The actual assembled drawing channel is the core channel. -/
theorem assembleWhole_stateDiagram?_eq_core (request : WholeSourceRequest V) :
    (assembleWhole request).assembled.stateDiagram? = request.core.diagram? :=
  OrganicStereoMolecularAssemblyProjections.assemble_stateDiagram? request.core

/-- The actual assembled real conformation is the core conformation. -/
theorem assembleWhole_stateConformation_eq_core (request : WholeSourceRequest V) :
    (assembleWhole request).assembled.stateConformation = request.core.conformation :=
  OrganicStereoMolecularAssemblyProjections.assemble_stateConformation request.core

theorem NativeWholeSourceEntry.sourceGraph_eq_output
    (assembled : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entry : NativeWholeSourceEntry (decodeEvidence assembled) enumeration) :
    entry.sourceGraph = assembled.stateGraph :=
  (NativeWholeSourceEntry.sourceGraph_eq_core entry).trans (decodeEvidence_graph assembled)

theorem NativeWholeSourceEntry.sourceSpatial?_eq_output_of_ne_p94
    (assembled : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entry : NativeWholeSourceEntry (decodeEvidence assembled) enumeration)
    (hfamily : entry.family ≠ .p94) :
    entry.sourceSpatial? = assembled.stateRationalPositions? :=
  (NativeWholeSourceEntry.sourceSpatial?_eq_core_of_ne_p94 entry hfamily).trans
    (decodeEvidence_rationalPositions? assembled)

theorem NativeWholeSourceEntry.sourceDiagram?_eq_output_of_ne_p94
    (assembled : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entry : NativeWholeSourceEntry (decodeEvidence assembled) enumeration)
    (hfamily : entry.family ≠ .p94) :
    entry.sourceDiagram? = assembled.stateDiagram? :=
  (NativeWholeSourceEntry.sourceDiagram?_eq_core_of_ne_p94 entry hfamily).trans
    (decodeEvidence_diagram? assembled)

/-- The actual output source tie of every native row.  Every row's native source graph is the
actual assembled output graph.  For every family other than P-94 the stored coordinate and drawing
channels are the actual output channels; the P-94 row is explicitly allowed to carry its own
conformer geometry at the same graph, which is why it is marked by the left disjunct rather than
silently identified with the core geometry. -/
theorem NativeWholeSourceEntry.source_ties_at_output
    (assembled : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entry : NativeWholeSourceEntry (decodeEvidence assembled) enumeration) :
    entry.sourceGraph = assembled.stateGraph ∧
      (entry.family = .p94 ∨
        (entry.sourceSpatial? = assembled.stateRationalPositions? ∧
          entry.sourceDiagram? = assembled.stateDiagram?)) := by
  refine ⟨NativeWholeSourceEntry.sourceGraph_eq_output assembled enumeration entry, ?_⟩
  by_cases hfamily : entry.family = .p94
  · exact Or.inl hfamily
  · exact Or.inr
      ⟨NativeWholeSourceEntry.sourceSpatial?_eq_output_of_ne_p94 assembled enumeration entry hfamily,
        NativeWholeSourceEntry.sourceDiagram?_eq_output_of_ne_p94 assembled enumeration entry
          hfamily⟩

theorem nativeSourceContext_ext {first second : NativeSourceContext V}
    (graph : first.graph = second.graph)
    (spatial : first.spatial? = second.spatial?)
    (diagram : first.diagram? = second.diagram?) : first = second := by
  cases first
  cases second
  simp_all

/-- The source context read from an actual assembled output and its entry-native provenance: the
graph is the actual output graph, and the optional channels are the assembled output channels. -/
def representationSourceContext (representation : OrganicMolecularRepresentation V) :
    NativeSourceContext V where
  graph := representation.stateGraph
  spatial? := representation.stateRationalPositions?
  diagram? := representation.stateDiagram?

def NativeWholeSourceEntry.sourceContext {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    (entry : NativeWholeSourceEntry core enumeration) : NativeSourceContext V where
  graph := entry.sourceGraph
  spatial? := entry.sourceSpatial?
  diagram? := entry.sourceDiagram?

def NativeWholeSourceEntry.sourceContextAt? {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    (entry : NativeWholeSourceEntry core enumeration) : Option (NativeSourceContext V) :=
  some entry.sourceContext

theorem NativeWholeSourceEntry.sourceContext_eq_representation_of_ne_p94
    (assembled : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entry : NativeWholeSourceEntry (decodeEvidence assembled) enumeration)
    (hfamily : entry.family ≠ .p94) :
    entry.sourceContext = representationSourceContext assembled := by
  apply nativeSourceContext_ext
  · exact NativeWholeSourceEntry.sourceGraph_eq_output assembled enumeration entry
  · exact NativeWholeSourceEntry.sourceSpatial?_eq_output_of_ne_p94 assembled enumeration entry
      hfamily
  · exact NativeWholeSourceEntry.sourceDiagram?_eq_output_of_ne_p94 assembled enumeration entry
      hfamily

/-- The actual source context reconstructed from the output and the entry-native provenance ties
the graph exactly.  Every non-P-94 family additionally ties both optional channels; the P-94 row
keeps its own native geometry at the common graph. -/
theorem NativeWholeSourceEntry.sourceContextAt?_ties
    (assembled : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (entry : NativeWholeSourceEntry (decodeEvidence assembled) enumeration) :
    entry.sourceContextAt? = some entry.sourceContext ∧
      entry.sourceContext.graph = assembled.stateGraph ∧
        (entry.family = .p94 ∨
          entry.sourceContext = representationSourceContext assembled) := by
  refine ⟨rfl, NativeWholeSourceEntry.sourceGraph_eq_output assembled enumeration entry, ?_⟩
  by_cases hfamily : entry.family = .p94
  · exact Or.inl hfamily
  · exact Or.inr
      (NativeWholeSourceEntry.sourceContext_eq_representation_of_ne_p94 assembled enumeration entry
        hfamily)

/-! ### Per-family tie corollaries -/

theorem legacy_entry_ties (assembled : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (frame : PhysicalFrame V)
    (graph_eq : graph = (decodeEvidence assembled).graph)
    (spatial_eq : spatial? = (decodeEvidence assembled).rationalPositions?)
    (diagram_eq : diagram? = (decodeEvidence assembled).diagram?)
    (valid : LegacyRowValid enumeration graph spatial? diagram? frame) :
    graph = assembled.stateGraph ∧
      spatial? = assembled.stateRationalPositions? ∧
      diagram? = assembled.stateDiagram? := by
  have h := NativeWholeSourceEntry.source_ties_at_output assembled enumeration
    (NativeWholeSourceEntry.legacy graph spatial? diagram? frame graph_eq spatial_eq diagram_eq valid)
  rcases h with ⟨hg, hrest⟩
  rcases hrest with hfamily | ⟨hs, hd⟩
  · simp [NativeWholeSourceEntry.family] at hfamily
  · exact ⟨hg, hs, hd⟩

theorem acyclic_entry_ties (assembled : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V)) (policy : P93AcyclicAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : AcyclicObservation V policy)
    (graph_eq : graph = (decodeEvidence assembled).graph)
    (spatial_eq : spatial? = (decodeEvidence assembled).rationalPositions?)
    (diagram_eq : diagram? = (decodeEvidence assembled).diagram?)
    (valid : AcyclicRowValid policy enumeration graph spatial? diagram? observation) :
    graph = assembled.stateGraph ∧
      spatial? = assembled.stateRationalPositions? ∧
      diagram? = assembled.stateDiagram? := by
  have h := NativeWholeSourceEntry.source_ties_at_output assembled enumeration
    (NativeWholeSourceEntry.acyclic policy graph spatial? diagram? observation graph_eq spatial_eq
      diagram_eq valid)
  rcases h with ⟨hg, hrest⟩
  rcases hrest with hfamily | ⟨hs, hd⟩
  · simp [NativeWholeSourceEntry.family] at hfamily
  · exact ⟨hg, hs, hd⟩

theorem noncarbon_entry_ties (assembled : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : NativeNoncarbonObservation V policy.Descriptor)
    (graph_eq : graph = (decodeEvidence assembled).graph)
    (spatial_eq : spatial? = (decodeEvidence assembled).rationalPositions?)
    (diagram_eq : diagram? = (decodeEvidence assembled).diagram?)
    (valid : NoncarbonRowValid policy enumeration graph spatial? diagram? observation) :
    graph = assembled.stateGraph ∧
      spatial? = assembled.stateRationalPositions? ∧
      diagram? = assembled.stateDiagram? := by
  have h := NativeWholeSourceEntry.source_ties_at_output assembled enumeration
    (NativeWholeSourceEntry.noncarbon policy graph spatial? diagram? observation graph_eq spatial_eq
      diagram_eq valid)
  rcases h with ⟨hg, hrest⟩
  rcases hrest with hfamily | ⟨hs, hd⟩
  · simp [NativeWholeSourceEntry.family] at hfamily
  · exact ⟨hg, hs, hd⟩

theorem unifiedMonoRing_entry_ties (assembled : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (monocyclicPolicy : P93MonocyclicAuthorityPolicy)
    (assemblyPolicy : P93RingAssemblyAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : CyclicObservation V monocyclicPolicy assemblyPolicy)
    (graph_eq : graph = (decodeEvidence assembled).graph)
    (spatial_eq : spatial? = (decodeEvidence assembled).rationalPositions?)
    (diagram_eq : diagram? = (decodeEvidence assembled).diagram?)
    (valid : CyclicRowValid monocyclicPolicy assemblyPolicy enumeration graph spatial? diagram?
      observation)
    (structurallyWellFormed :
      ((cyclicSatellite monocyclicPolicy assemblyPolicy graph spatial? diagram?
        observation).toFiniteSource.encode enumeration).molecule.StructurallyWellFormed) :
    graph = assembled.stateGraph ∧
      spatial? = assembled.stateRationalPositions? ∧
      diagram? = assembled.stateDiagram? := by
  have h := NativeWholeSourceEntry.source_ties_at_output assembled enumeration
    (NativeWholeSourceEntry.unifiedMonoRing monocyclicPolicy assemblyPolicy graph spatial? diagram?
      observation graph_eq spatial_eq diagram_eq valid structurallyWellFormed)
  rcases h with ⟨hg, hrest⟩
  rcases hrest with hfamily | ⟨hs, hd⟩
  · simp [NativeWholeSourceEntry.family] at hfamily
  · exact ⟨hg, hs, hd⟩

theorem fusedVonBaeyer_entry_ties (assembled : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (fusedPolicy : P93FusedAuthorityPolicy)
    (vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy)
    (graph_eq : graph = (decodeEvidence assembled).graph)
    (spatial_eq : spatial? = (decodeEvidence assembled).rationalPositions?)
    (diagram_eq : diagram? = (decodeEvidence assembled).diagram?)
    (valid : FusedRowValid fusedPolicy vonBaeyerPolicy enumeration graph spatial? diagram?
      observation) :
    graph = assembled.stateGraph ∧
      spatial? = assembled.stateRationalPositions? ∧
      diagram? = assembled.stateDiagram? := by
  have h := NativeWholeSourceEntry.source_ties_at_output assembled enumeration
    (NativeWholeSourceEntry.fusedVonBaeyer fusedPolicy vonBaeyerPolicy graph spatial? diagram?
      observation graph_eq spatial_eq diagram_eq valid)
  rcases h with ⟨hg, hrest⟩
  rcases hrest with hfamily | ⟨hs, hd⟩
  · simp [NativeWholeSourceEntry.family] at hfamily
  · exact ⟨hg, hs, hd⟩

theorem cyclophane_entry_ties (assembled : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V)) (policy : P93CyclophaneAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : NativeCyclophaneAuthorityObservation V policy)
    (graph_eq : graph = (decodeEvidence assembled).graph)
    (spatial_eq : spatial? = (decodeEvidence assembled).rationalPositions?)
    (diagram_eq : diagram? = (decodeEvidence assembled).diagram?)
    (valid : CyclophaneRowValid policy enumeration graph spatial? diagram? observation) :
    graph = assembled.stateGraph ∧
      spatial? = assembled.stateRationalPositions? ∧
      diagram? = assembled.stateDiagram? := by
  have h := NativeWholeSourceEntry.source_ties_at_output assembled enumeration
    (NativeWholeSourceEntry.cyclophane policy graph spatial? diagram? observation graph_eq
      spatial_eq diagram_eq valid)
  rcases h with ⟨hg, hrest⟩
  rcases hrest with hfamily | ⟨hs, hd⟩
  · simp [NativeWholeSourceEntry.family] at hfamily
  · exact ⟨hg, hs, hd⟩

theorem spiro_entry_ties (assembled : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V)) (policy : P93SpiroAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : NativeSpiroAuthorityObservation policy V)
    (graph_eq : graph = (decodeEvidence assembled).graph)
    (spatial_eq : spatial? = (decodeEvidence assembled).rationalPositions?)
    (diagram_eq : diagram? = (decodeEvidence assembled).diagram?)
    (valid : SpiroRowValid policy enumeration graph spatial? diagram? observation) :
    graph = assembled.stateGraph ∧
      spatial? = assembled.stateRationalPositions? ∧
      diagram? = assembled.stateDiagram? := by
  have h := NativeWholeSourceEntry.source_ties_at_output assembled enumeration
    (NativeWholeSourceEntry.spiro policy graph spatial? diagram? observation graph_eq spatial_eq
      diagram_eq valid)
  rcases h with ⟨hg, hrest⟩
  rcases hrest with hfamily | ⟨hs, hd⟩
  · simp [NativeWholeSourceEntry.family] at hfamily
  · exact ⟨hg, hs, hd⟩

theorem fullereneAuthority_entry_ties (assembled : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V)) (policy : P93FullereneAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : NativeFullereneAuthorityObservationFamily V)
    (graph_eq : graph = (decodeEvidence assembled).graph)
    (spatial_eq : spatial? = (decodeEvidence assembled).rationalPositions?)
    (diagram_eq : diagram? = (decodeEvidence assembled).diagram?)
    (molecule : RawMolecule)
    (conversion_eq : molecule.toSemanticMolecule? =
      some ((fullereneSatellite policy graph spatial? diagram?
        observation).toFiniteSource.encode enumeration).molecule)
    (valid : FullereneRowValid policy enumeration graph spatial? diagram? observation)
    (moleculeBound : FullereneRowMoleculeBound policy enumeration graph spatial? diagram?
      observation) :
    graph = assembled.stateGraph ∧
      spatial? = assembled.stateRationalPositions? ∧
      diagram? = assembled.stateDiagram? := by
  have h := NativeWholeSourceEntry.source_ties_at_output assembled enumeration
    (NativeWholeSourceEntry.fullereneAuthority policy graph spatial? diagram? observation graph_eq
      spatial_eq diagram_eq molecule conversion_eq valid moleculeBound)
  rcases h with ⟨hg, hrest⟩
  rcases hrest with hfamily | ⟨hs, hd⟩
  · simp [NativeWholeSourceEntry.family] at hfamily
  · exact ⟨hg, hs, hd⟩

theorem relationalFullerene_entry_ties (assembled : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (policy : P93RelationalFullereneAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : NativeRelationalFullereneObservation V enumeration policy)
    (graph_eq : graph = (decodeEvidence assembled).graph)
    (spatial_eq : spatial? = (decodeEvidence assembled).rationalPositions?)
    (diagram_eq : diagram? = (decodeEvidence assembled).diagram?)
    (valid : RelationalRowValid policy enumeration graph spatial? diagram? observation) :
    graph = assembled.stateGraph ∧
      spatial? = assembled.stateRationalPositions? ∧
      diagram? = assembled.stateDiagram? := by
  have h := NativeWholeSourceEntry.source_ties_at_output assembled enumeration
    (NativeWholeSourceEntry.relationalFullerene policy graph spatial? diagram? observation graph_eq
      spatial_eq diagram_eq valid)
  rcases h with ⟨hg, hrest⟩
  rcases hrest with hfamily | ⟨hs, hd⟩
  · simp [NativeWholeSourceEntry.family] at hfamily
  · exact ⟨hg, hs, hd⟩

theorem coupledRingChain_entry_ties (assembled : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (policy : P93CoupledRingChainAuthorityPolicy)
    (graph : FiniteAtomInteractionHypergraph V)
    (spatial? : Option (V → CartesianPoint3))
    (diagram? : Option (OrganicDiagramSource V))
    (observation : SuppliedNativeCoupledRingChainObservation V policy)
    (graph_eq : graph = (decodeEvidence assembled).graph)
    (spatial_eq : spatial? = (decodeEvidence assembled).rationalPositions?)
    (diagram_eq : diagram? = (decodeEvidence assembled).diagram?)
    (valid : CoupledRowValid policy enumeration graph spatial? diagram? observation) :
    graph = assembled.stateGraph ∧
      spatial? = assembled.stateRationalPositions? ∧
      diagram? = assembled.stateDiagram? := by
  have h := NativeWholeSourceEntry.source_ties_at_output assembled enumeration
    (NativeWholeSourceEntry.coupledRingChain policy graph spatial? diagram? observation graph_eq
      spatial_eq diagram_eq valid)
  rcases h with ⟨hg, hrest⟩
  rcases hrest with hfamily | ⟨hs, hd⟩
  · simp [NativeWholeSourceEntry.family] at hfamily
  · exact ⟨hg, hs, hd⟩

/-- The P-94 row ties its graph to the actual output.  Its native coordinate and drawing channels
are its own reconstructed source geometry, not the core channels; they are read from the row's
`OrganicStereoNativeP94SourceContext` context exactly as stored. -/
theorem p94_entry_ties (assembled : OrganicMolecularRepresentation V)
    (enumeration : V ≃ Fin (Fintype.card V)) (policy : P94AuthorityPolicy)
    (native : OrganicStereoNativeP94SourceContext.NativeAuthorityObservation
      (decodeEvidence assembled).graph enumeration policy) :
    (NativeWholeSourceEntry.p94 policy native).sourceGraph = assembled.stateGraph ∧
      (NativeWholeSourceEntry.p94 policy native).sourceSpatial? =
        native.context.toFiniteSource.spatial? ∧
      (NativeWholeSourceEntry.p94 policy native).sourceDiagram? =
        native.context.toFiniteSource.diagram? :=
  ⟨NativeWholeSourceEntry.sourceGraph_eq_output assembled enumeration
      (NativeWholeSourceEntry.p94 policy native), rfl, rfl⟩

/-! ## Correlated sets of whole requests -/

theorem decodeWhole_image_assembleWhole_image (requests : Set (WholeSourceRequest V)) :
    decodeWhole '' (assembleWhole '' requests) = requests := by
  ext request
  constructor
  · rintro ⟨representation, ⟨original, member, rfl⟩, decoded⟩
    rw [← decoded, decodeWhole_assembleWhole]
    exact member
  · intro member
    exact ⟨assembleWhole request, ⟨request, member, rfl⟩, decodeWhole_assembleWhole request⟩

/-- The fixed arbitrary-label form: at any atom-label type `V`, the actual assembled graph and
conformation carry the original labels, not an encoded `Fin` replacement, and the decoded core is
the supplied one. -/
theorem fixedLabel_retains_labels (request : WholeSourceRequest V) :
    (assembleWhole request).enumeration = request.enumeration ∧
      (assembleWhole request).assembled.stateGraph = request.core.graph ∧
      (∀ atom : V,
        ((assembleWhole request).assembled.stateGraph.atomData atom) =
          (request.core.graph.atomData atom)) ∧
      (decodeWhole (assembleWhole request)).core = request.core := by
  refine ⟨rfl, assembleWhole_stateGraph_eq_core request, ?_, decodeEvidence_assembleEvidence
    request.core⟩
  intro atom
  rw [assembleWhole_stateGraph_eq_core request]

/-! ## Varying atom counts: the `Σ n` whole-request endpoint

The atom label type is not fixed: the endpoint below quantifies over the actual finite atom count
`n` and a whole request on the exact labels `Fin n`.  The encoder and decoder are the actual whole
encoder and decoder above, not a count-erasing wrapper. -/

def assembleFinWhole (request : Σ n, WholeSourceRequest (Fin n)) :
    Σ n, WholeSourceRepresentation (Fin n) :=
  ⟨request.1, assembleWhole request.2⟩

def decodeFinWhole (representation : Σ n, WholeSourceRepresentation (Fin n)) :
    Σ n, WholeSourceRequest (Fin n) :=
  ⟨representation.1, decodeWhole representation.2⟩

theorem decodeFinWhole_assembleFinWhole (request : Σ n, WholeSourceRequest (Fin n)) :
    decodeFinWhole (assembleFinWhole request) = request := by
  obtain ⟨n, request⟩ := request
  simp [decodeFinWhole, assembleFinWhole, decodeWhole_assembleWhole]

theorem assembleFinWhole_injective :
    Function.Injective (assembleFinWhole :
      (Σ n, WholeSourceRequest (Fin n)) → Σ n, WholeSourceRepresentation (Fin n)) := by
  intro first second equal
  obtain ⟨n, first⟩ := first
  obtain ⟨m, second⟩ := second
  have equal' : (⟨n, assembleWhole first⟩ :
      Σ n, WholeSourceRepresentation (Fin n)) = ⟨m, assembleWhole second⟩ := equal
  have parts := Sigma.ext_iff.mp equal'
  have count : n = m := parts.1
  have observations : HEq (assembleWhole first) (assembleWhole second) := parts.2
  subst count
  rw [assembleWhole_injective (eq_of_heq observations)]

theorem decodeFinWhole_image_assembleFinWhole_image
    (requests : Set (Σ n, WholeSourceRequest (Fin n))) :
    decodeFinWhole '' (assembleFinWhole '' requests) = requests := by
  ext request
  constructor
  · rintro ⟨representation, ⟨original, member, rfl⟩, decoded⟩
    rw [← decoded, decodeFinWhole_assembleFinWhole]
    exact member
  · intro member
    exact ⟨assembleFinWhole request, ⟨request, member, rfl⟩,
      decodeFinWhole_assembleFinWhole request⟩

/-! ## A concrete correlated uncertainty set with genuinely different atom counts -/

def carbonAtom : SemanticAtom where
  element := { atomicNumber := 6, positive := by decide, atMost118 := by decide }

def emptyGraph (V : Type) [DecidableEq V] [Fintype V] :
    FiniteAtomInteractionHypergraph V where
  atomData := fun _ => carbonAtom
  interactions := []
  arity_ge_two := by simp
  participants_nodup := by simp

/-- A fully explicit evidence record with an empty interaction graph and the origin conformation. -/
def emptyEvidence (n : Nat) : OrganicMolecularEvidence (Fin n) where
  graph := emptyGraph (Fin n)
  conformation := fun _ => 0
  rationalPositions? := none
  rationalPositions_valid := by intro positions present; simp at present
  electronic? := none
  electronic_unpaired := by intro evidence present; simp at present
  paths? := none
  paths_graph_eq := by intro family present; simp at present
  paths_conformation_eq := by intro family present; simp at present
  bands? := none
  bands_graph_eq := by intro bands present; simp at present
  bands_conformation_eq := by intro bands present; simp at present
  roles := []
  role_valid := by intro annotation member; simp at member
  diagram? := none
  diagramPartial? := none
  diagramIncidence := []
  diagram_valid := by intro row member; simp at member
  fragments := []
  conventions := []
  cages := []
  residueLedger? := none
  frames := []

/-- An empty whole request at an exact atom count. -/
def emptyRequest (n : Nat) : WholeSourceRequest (Fin n) where
  core := emptyEvidence n
  enumeration := Fintype.equivFin (Fin n)
  entries := []

/-- A concrete uncertainty set containing two whole requests with actually different atom counts
(0 and 1) and otherwise no observations. -/
def uncertaintySet : Set (Σ n, WholeSourceRequest (Fin n)) :=
  {⟨0, emptyRequest 0⟩, ⟨1, emptyRequest 1⟩}

theorem uncertaintySet_distinct_atom_counts :
    (⟨0, emptyRequest 0⟩ : Σ n, WholeSourceRequest (Fin n)) ≠
      ⟨1, emptyRequest 1⟩ := by
  intro equal
  exact Nat.zero_ne_one (congrArg Sigma.fst equal)

theorem uncertaintySet_endpoints :
    (⟨0, emptyRequest 0⟩ : Σ n, WholeSourceRequest (Fin n)) ∈ uncertaintySet ∧
      (⟨1, emptyRequest 1⟩ : Σ n, WholeSourceRequest (Fin n)) ∈ uncertaintySet :=
  ⟨by simp [uncertaintySet], by simp [uncertaintySet]⟩

theorem uncertaintySet_image :
    decodeFinWhole '' (assembleFinWhole '' uncertaintySet) = uncertaintySet :=
  decodeFinWhole_image_assembleFinWhole_image uncertaintySet

/-! ## Ordered cross-family witnesses over one common core

The pair request stores exactly two individual raw observations in order over the same core and
enumeration.  The decoder is proved to return two entries, occurrence zero heterogeneously equal to
the first raw observation and occurrence one to the second, so arbitrary cross-family order and
repetition are preserved as individual rows rather than as family blocks. -/

def pairRequest {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    (first second : RawWholeSourceEntry core enumeration) : WholeSourceRequest V where
  core := core
  enumeration := enumeration
  entries := [first, second]

@[simp] theorem pairRequest_entries {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    (first second : RawWholeSourceEntry core enumeration) :
    (pairRequest first second).entries = [first, second] := rfl

theorem pairRequest_decoded_length {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    (first second : RawWholeSourceEntry core enumeration) :
    (decodeWhole (assembleWhole (pairRequest first second))).entries.length = 2 := by
  rw [decodeWhole_entries_length]
  rfl

theorem pairRequest_decoded_getElem?_zero {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    (first second : RawWholeSourceEntry core enumeration) :
    HEq ((decodeWhole (assembleWhole (pairRequest first second))).entries[0]?) (some first) := by
  simpa [pairRequest] using decodeWhole_getElem?_heq (pairRequest first second) 0

theorem pairRequest_decoded_getElem?_one {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    (first second : RawWholeSourceEntry core enumeration) :
    HEq ((decodeWhole (assembleWhole (pairRequest first second))).entries[1]?) (some second) := by
  simpa [pairRequest] using decodeWhole_getElem?_heq (pairRequest first second) 1

/-- Any two individual raw observations with genuinely different family tags, placed in order into
one whole request, are decoded in that exact order and retain their distinct families. -/
theorem crossFamily_ordered_witness {core : OrganicMolecularEvidence V}
    {enumeration : V ≃ Fin (Fintype.card V)}
    (first second : RawWholeSourceEntry core enumeration)
    (different : first.family ≠ second.family) :
    ∃ decoded : WholeSourceRequest V,
      decoded.entries.length = 2 ∧
        HEq (decoded.entries[0]?) (some first) ∧
        HEq (decoded.entries[1]?) (some second) ∧
        first.family ≠ second.family :=
  ⟨decodeWhole (assembleWhole (pairRequest first second)),
    pairRequest_decoded_length first second,
    pairRequest_decoded_getElem?_zero first second,
    pairRequest_decoded_getElem?_one first second,
    different⟩

/-! ## Kernel checks on selected whole endpoints -/

assert_kernel_only decodeWhole_assembleWhole
assert_kernel_only assembleWhole_injective
assert_kernel_only decodeWhole_image_assembleWhole_image
assert_kernel_only fixedLabel_retains_labels
assert_kernel_only decodeFinWhole_assembleFinWhole
assert_kernel_only assembleFinWhole_injective
assert_kernel_only decodeFinWhole_image_assembleFinWhole_image
assert_kernel_only uncertaintySet_distinct_atom_counts
assert_kernel_only crossFamily_ordered_witness

end

end OrganicStereoWholeAuthorityMolecularAssembly
end TetraStereo.OneCenter
