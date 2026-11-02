/-
# Constructive coverage kernel-authority certificate

This module is a transitive kernel-authority certificate for the accepted constructive coverage
modules

* `OrganicStereoFiniteGraphEmbedding` — construction of one global continuous injective embedding
  for every finite loopless multigraph;
* `OrganicStereoMomentCurveSeparation` — exact moment-curve segment separation and affine
  independence;
* `OrganicStereoEmbeddedCycleRealization` — continuous injective realized cycle maps, closed
  embeddings, exact cycle images and exact two-cycle intersections;
* `OrganicStereoEmbeddedSpiroCoverage` — the actual mechanically valid spiro carrier and its two
  embedded ring walks meeting exactly at the embedded center;
* `OrganicStereoConformationTrajectoryObstruction` — the oriented-volume sign change under a
  genuine ambient homeomorphism motion, together with a coplanar crossing without collision;
* `OrganicStereoUniversalMixtureSamples` — exact variable-shape whole-record encoding/decoding,
  exact set-image inverses, and the faithful species-weighted observable;
* `LocalizedWrittenPhantomCandidates` — the computed written phantom-candidate membership
  characterization and its descriptor routing;
* `OrganicStereoInventoryImplicitHMaterialization` — implicit-protium expansion, exact graph
  restore, introduced-slot recovery, and the concrete CHBrClF detector/CIP fixture;
* `OrganicStereoFiniteGraphMolecularInhabitance` (already compiled) — universal molecular
  inhabitance for every finite atom interaction hypergraph.

The `assert_kernel_only` commands check that the closures of the decisive endpoints use only the
standard logical principles `propext`, `Classical.choice` and `Quot.sound`.  The type-explicit
theorems below restate the universal endpoints at their strongest assumptions and are themselves
certified at the end of the file.

## Scope and preserved premises

These are representation, exact-recovery and structural-inhabitance results.

* The finite-graph construction produces one canonical embedding; it does not match prescribed
  atom coordinates or prescribed arcs, and it does not assert physical realizability or chemical
  admissibility of an arbitrary molecule.
* The spiro coverage result consumes an independently supplied global embedding `G` and an
  independently supplied `MechanicallyValidFor` witness.  It constructs neither.
* The mixture fixtures are formal structural fixtures.  Their empty-shell states use the
  all-at-zero conformation; per-constituent possibility sets are `Set.univ`, while the sample
  record is the outer joint state/amount record.  No probability, energy, chemical realizability
  or descriptor semantics is asserted.
* Written phantom-candidate membership is exactly nonemptiness of the written configuration
  frame.  It is not the existence of a descriptor outcome.
* The inventory module proves exact restore and slot recovery for the implicit-protium expansion;
  full inventory recovery of a separate complete source bundle remains separate work.
-/

import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OrganicStereoFiniteGraphEmbedding
import TetraStereo.OneCenter.OrganicStereoMomentCurveSeparation
import TetraStereo.OneCenter.OrganicStereoEmbeddedCycleRealization
import TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage
import TetraStereo.OneCenter.OrganicStereoConformationTrajectoryObstruction
import TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples
import TetraStereo.OneCenter.LocalizedWrittenPhantomCandidates
import TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization
import TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate

open scoped unitInterval

open TetraStereo.OneCenter
open TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization
open TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage
open TetraStereo.OneCenter.OrganicStereoMomentCurveSeparation
open TetraStereo.OneCenter.OrganicStereoEmbeddedCycleRealization
open TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples
open TetraStereo.OneCenter.OrganicStereoHeterogeneousSamples
open TetraStereo.OneCenter.BlueBookP93.TrigonalPyramidal
open TetraStereo.OneCenter.OrganicStereoElectronicSites
open TetraStereo.OneCenter.OrganicStereoIndependentElectronicEncoding
open TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization
open TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance

noncomputable section

universe u v

/-! ## Arbitrary finite loopless graphs: constructed global embedding

The theorem below takes only a finite vertex type, a finite edge type, endpoint maps and the
per-edge non-loop condition.  The global map, its continuity, its injectivity, injective atom
positions, injective arcs and the exact common-endpoint intersection law are all produced by the
accepted construction.  No global map, arc, geometric law or embedding hypothesis is an input. -/

theorem finiteGraphEmbedding_certificate
    {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    (src dst : E → V) (noLoops : ∀ e, src e ≠ dst e) :
    (let G : EmbeddedGraph src dst :=
      OrganicStereoFiniteGraphEmbedding.finiteGraphEmbedded src dst noLoops;
      Function.Injective G.map ∧ Continuous G.map ∧ Function.Injective G.conformation ∧
        (∀ e : E, Function.Injective (G.arc e)) ∧
        (∀ (e f : E) (t s : I), e ≠ f → G.arc e t = G.arc f s →
          ∃ atom : V,
            sourceEndpointAt? src dst e t = some atom ∧
              sourceEndpointAt? src dst f s = some atom)) := by
  dsimp only
  exact
    ⟨(OrganicStereoFiniteGraphEmbedding.finiteGraphEmbedded src dst noLoops).injective,
     (OrganicStereoFiniteGraphEmbedding.finiteGraphEmbedded src dst noLoops).map.continuous,
     OrganicStereoFiniteGraphEmbedding.finiteGraphEmbedded_atom_injective src dst noLoops,
     fun e =>
       OrganicStereoFiniteGraphEmbedding.finiteGraphEmbedded_arc_injective src dst noLoops e,
     fun e f t s hne h =>
       OrganicStereoFiniteGraphEmbedding.finiteGraphEmbedded_intersects_only_at_common_endpoints
         src dst noLoops hne h⟩

/-! ## Moment-curve segment separation and affine independence -/

/-- Exact segment-hitting criterion: two chord points on the moment curve coincide exactly at an
endpoint collision. -/
theorem momentCurveSeparatedSegments_certificate
    {x y u v : ℝ} (hxy : x ≠ y) (huv : u ≠ v)
    (hpair : ¬ SameUnorderedPair x y u v) (s t : I) :
    segmentPoint x y s = segmentPoint u v t ↔ EndpointCollision x y u v s t :=
  segmentPoint_eq_iff_endpointCollision hxy huv hpair

/-- Four distinct moment-curve chord endpoints give disjoint open-and-closed chord segments. -/
theorem momentCurveDisjointSegments_certificate
    {x y u v : ℝ} (hxy : x ≠ y) (huv : u ≠ v)
    (hxu : x ≠ u) (hxv : x ≠ v) (hyu : y ≠ u) (hyv : y ≠ v) (s t : I) :
    segmentPoint x y s ≠ segmentPoint u v t :=
  segmentPoint_ne_of_disjoint_endpoints hxy huv hxu hxv hyu hyv s t

/-- A chord point is a moment-curve point exactly at an endpoint of the chord. -/
theorem momentCurveSegmentEndpoint_certificate
    {x y z : ℝ} (hxy : x ≠ y) (s : I) :
    segmentPoint x y s = momentCurve z ↔ (s = 0 ∧ z = x) ∨ (s = 1 ∧ z = y) :=
  segmentPoint_eq_momentCurve_iff hxy

/-- Any at most four distinct moment-curve samples are affinely independent. -/
theorem momentCurveAffineIndependent_certificate
    {n : ℕ} (hn : n ≤ 4) {t : Fin n → ℝ} (ht : Function.Injective t) :
    AffineIndependent ℝ (fun i : Fin n => momentCurve (t i)) :=
  momentCurve_affineIndependent_fin hn ht

/-! ## Realized cycles: injection, closed embedding, image and intersection -/

/-- A combinatorial cycle walk in an arbitrary multigraph yields a continuous injective
realization, and under one global embedding its spatial map is a closed embedding whose range is
exactly the cycle image and whose vertex values are the embedded atom positions. -/
theorem embeddedCycle_certificate
    {V : Type u} {E : Type v} {src dst : E → V}
    (W : CycleWalk src dst) (G : EmbeddedGraph src dst) :
    Function.Injective (cycleMap W) ∧
      Continuous (cycleMap W) ∧
      Function.Injective (cycleSpatialMap W G) ∧
      Topology.IsClosedEmbedding (cycleSpatialMap W G) ∧
      Set.range (cycleSpatialMap W G) = cycleImage W G ∧
      (∀ i : Fin W.n,
        cycleSpatialMap W G (Realization.vertex i) = G.conformation (W.vertices i)) :=
  ⟨cycleMap_injective W, cycleMap_continuous W, cycleSpatialMap_injective W G,
   cycleSpatialMap_isClosedEmbedding W G, cycleSpatialMap_range W G,
   fun i => cycleSpatialMap_vertex W G i⟩

/-- Two cycles with pairwise-disjoint edge-interior images meet exactly at the images of their
common vertices. -/
theorem embeddedCycleCommonVertexImages_certificate
    {V : Type u} {E : Type v} {src dst : E → V}
    (W₁ W₂ : CycleWalk src dst) (G : EmbeddedGraph src dst)
    (hdisj : ∀ (i : Fin W₁.n) (j : Fin W₂.n),
      Disjoint (G.arc (W₁.edges i) '' intervalInterior)
        (G.arc (W₂.edges j) '' intervalInterior)) :
    cycleImage W₁ G ∩ cycleImage W₂ G =
      G.conformation '' (Set.range W₁.vertices ∩ Set.range W₂.vertices) :=
  cycleImage_inter_eq_commonVertexImages W₁ W₂ G hdisj

/-- Edge-disjoint cycle walks sharing exactly one vertex have spatial images meeting exactly at
that vertex's embedded position. -/
theorem embeddedCycleSoleCommonVertex_certificate
    {V : Type u} {E : Type v} {src dst : E → V}
    (W₁ W₂ : CycleWalk src dst) (G : EmbeddedGraph src dst)
    (hedges : ∀ (i : Fin W₁.n) (j : Fin W₂.n), W₁.edges i ≠ W₂.edges j)
    (v₀ : V) (hcommon : Set.range W₁.vertices ∩ Set.range W₂.vertices = {v₀}) :
    cycleImage W₁ G ∩ cycleImage W₂ G = {G.conformation v₀} :=
  cycleImage_inter_eq_singleton_of_sole_common_vertex W₁ W₂ G hedges v₀ hcommon

/-! ## Spiro coverage from the actual mechanically valid carrier -/

/-- The two actually constructed ring walks of a supplied mechanically valid spiro system have
the declared ring lengths, ring-bounded vertices, genuine source binary bonds on every cyclic
edge, exact embedded vertex positions, and spatial ranges meeting exactly at the embedded center.
The mechanical-validity witness and the global embedding are supplied inputs. -/
theorem spiroCoverage_certificate
    (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (G : EmbeddedGraph
      (selectedSource (OrganicStereoEmbeddedSpiroCoverage.sourceGraph certified))
      (selectedTarget (OrganicStereoEmbeddedSpiroCoverage.sourceGraph certified))) :
    (OrganicStereoEmbeddedSpiroCoverage.firstRingWalk certified system valid).n =
        OrganicStereoEmbeddedSpiroCoverage.ringN system.firstRingInternal ∧
      (OrganicStereoEmbeddedSpiroCoverage.secondRingWalk certified system valid).n =
        OrganicStereoEmbeddedSpiroCoverage.ringN system.secondRingInternal ∧
      (∀ i : Fin (OrganicStereoEmbeddedSpiroCoverage.ringN system.firstRingInternal),
        ((OrganicStereoEmbeddedSpiroCoverage.firstRingWalk certified system valid).vertices
          i).val ∈ system.firstRing) ∧
      (∀ j : Fin (OrganicStereoEmbeddedSpiroCoverage.ringN system.secondRingInternal),
        ((OrganicStereoEmbeddedSpiroCoverage.secondRingWalk certified system valid).vertices
          j).val ∈ system.secondRing) ∧
      (∀ i : Fin (OrganicStereoEmbeddedSpiroCoverage.ringN system.firstRingInternal),
        P93AuthorityBinaryBond certified.input
          ((OrganicStereoEmbeddedSpiroCoverage.firstRingWalk certified system valid).vertices
            i).val
          ((OrganicStereoEmbeddedSpiroCoverage.firstRingWalk certified system valid).vertices
            (OrganicStereoEmbeddedSpiroCoverage.cycleSucc i)).val) ∧
      (∀ j : Fin (OrganicStereoEmbeddedSpiroCoverage.ringN system.secondRingInternal),
        P93AuthorityBinaryBond certified.input
          ((OrganicStereoEmbeddedSpiroCoverage.secondRingWalk certified system valid).vertices
            j).val
          ((OrganicStereoEmbeddedSpiroCoverage.secondRingWalk certified system valid).vertices
            (OrganicStereoEmbeddedSpiroCoverage.cycleSucc j)).val) ∧
      (∀ i : Fin (OrganicStereoEmbeddedSpiroCoverage.firstRingWalk certified system valid).n,
        (OrganicStereoEmbeddedSpiroCoverage.firstRingWalk certified system valid).map G
            (Realization.vertex i) =
          G.conformation
            ((OrganicStereoEmbeddedSpiroCoverage.firstRingWalk certified system valid).vertices
              i)) ∧
      (∀ j : Fin (OrganicStereoEmbeddedSpiroCoverage.secondRingWalk certified system valid).n,
        (OrganicStereoEmbeddedSpiroCoverage.secondRingWalk certified system valid).map G
            (Realization.vertex j) =
          G.conformation
            ((OrganicStereoEmbeddedSpiroCoverage.secondRingWalk certified system valid).vertices
              j)) ∧
      Set.range
          ((OrganicStereoEmbeddedSpiroCoverage.firstRingWalk certified system valid).mapFun G) ∩
        Set.range
          ((OrganicStereoEmbeddedSpiroCoverage.secondRingWalk certified system valid).mapFun G) =
          {G.conformation
            (OrganicStereoEmbeddedSpiroCoverage.centerAtom certified system valid)} := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact OrganicStereoEmbeddedSpiroCoverage.firstRingWalk_vertex_mem
      certified system valid i
  · intro j
    exact OrganicStereoEmbeddedSpiroCoverage.secondRingWalk_vertex_mem
      certified system valid j
  · intro i
    exact OrganicStereoEmbeddedSpiroCoverage.firstRingWalk_bond certified system valid i
  · intro j
    exact OrganicStereoEmbeddedSpiroCoverage.secondRingWalk_bond certified system valid j
  · intro i
    exact OrganicStereoEmbeddedSpiroCoverage.firstRingWalk_map_vertex
      certified system valid G i
  · intro j
    exact OrganicStereoEmbeddedSpiroCoverage.secondRingWalk_map_vertex
      certified system valid G j
  · exact OrganicStereoEmbeddedSpiroCoverage.firstRingWalk_inter_secondRingWalk_eq_center
      certified system valid G

/-! ## Ambient motion, determinant sign, coplanarity and zero crossing -/

/-- The shear motion is a genuine ambient motion: it starts at the identity and both evaluation
maps are jointly continuous. -/
theorem shearMotionAmbient_certificate :
    (shearMotion.map 0 = Homeomorph.refl Real3) ∧
      Continuous (fun pair : unitInterval × Real3 => shearMotion.map pair.1 pair.2) ∧
      Continuous (fun pair : unitInterval × Real3 => (shearMotion.map pair.1).symm pair.2) :=
  ⟨shearMotion.starts_identity, shearMotion.continuous_uncurried,
   shearMotion.continuous_uncurried_inv⟩

/-- At the half-time the four labelled atoms are distinct and coplanar, the oriented volume is
zero, and the ambient-motion endpoint reverses the sign of the discrete oriented volume while the
initial configuration is positively oriented. -/
theorem shearTrajectoryObstruction_certificate :
    Function.Injective (shearTrajectory.trajectory halfTime) ∧
      shearTrajectory.volume 0 1 2 3 halfTime = 0 ∧
      (∀ i : Fin 4, (shearTrajectory.trajectory halfTime i) 2 = 0) ∧
      TetrahedralGeometry.orientedVolume
          (tetrahedron (shearMotion.endpoint fixtureInitialP0)
            fixtureP1 fixtureP2 fixtureP3) = -1 ∧
      TetrahedralGeometry.orientedVolume
          (tetrahedron fixtureInitialP0 fixtureP1 fixtureP2 fixtureP3) = 1 ∧
      Real.sign
          (TetrahedralGeometry.orientedVolume
            (tetrahedron (shearMotion.endpoint fixtureInitialP0)
              fixtureP1 fixtureP2 fixtureP3)) = -1 ∧
      Real.sign
          (TetrahedralGeometry.orientedVolume
            (tetrahedron fixtureInitialP0 fixtureP1 fixtureP2 fixtureP3)) = 1 := by
  obtain ⟨hinjective, hvolume, hcoplanar⟩ :=
    shearTrajectory_crosses_coplanar_without_collision
  obtain ⟨hendpoint, hinitial⟩ :=
    shearMotion_endpoint_reverses_four_point_volume
  obtain ⟨hsignEndpoint, hsignInitial⟩ :=
    shearMotion_endpoint_reverses_real_sign
  exact ⟨hinjective, hvolume, hcoplanar, hendpoint, hinitial,
    hsignEndpoint, hsignInitial⟩

/-- There exists a genuine ambient homeomorphism motion, starting at the identity, whose endpoint
maps a positively oriented labelled quadruple of distinct points to a negatively oriented one. -/
theorem ambientMotionEndpoint_certificate :
    ∃ motion : AmbientMotion,
      TetrahedralGeometry.orientedVolume
          (tetrahedron (motion.endpoint fixtureInitialP0)
            fixtureP1 fixtureP2 fixtureP3) = -1 ∧
        TetrahedralGeometry.orientedVolume
          (tetrahedron fixtureInitialP0 fixtureP1 fixtureP2 fixtureP3) = 1 :=
  exists_ambient_motion_endpoint_reversing_four_point_volume

/-- Along the shear trajectory the oriented volume vanishes exactly at the half-time. -/
theorem shearTrajectoryZeroTime_certificate (t : unitInterval) :
    shearTrajectory.volume 0 1 2 3 t = 0 ↔ t = halfTime :=
  shearTrajectory_volume_eq_zero_iff t

/-- The fixture trajectory has opposite endpoint signs and therefore crosses zero volume at an
intermediate time. -/
theorem fixtureTrajectorySign_certificate :
    fixtureTrajectory.volume 0 1 2 3 0 * fixtureTrajectory.volume 0 1 2 3 1 < 0 ∧
      ∃ t : unitInterval, fixtureTrajectory.volume 0 1 2 3 t = 0 :=
  ⟨fixtureTrajectory_opposite_endpoint_signs, fixtureTrajectory_exists_zero_volume⟩

/-! ## Variable-shape mixture records: exact whole-record and set inverses -/

/-- On the full dependent-sum domain of variable shapes, encode/decode are mutual inverses of the
whole record (shape witness included), the encoding is bijective, and both whole-set image
constructions are exact inverses. -/
theorem universalMixtureEncoding_certificate :
    (∀ x : UniversalSample, decodeUniversal (encodeUniversal x) = x) ∧
      (∀ c : UniversalCanonical, encodeUniversal (decodeUniversal c) = c) ∧
      Function.Bijective encodeUniversal ∧
      (∀ U : Set UniversalSample, decodeSet (encodeSet U) = U) ∧
      (∀ V : Set UniversalCanonical, encodeSet (decodeSet V) = V) :=
  ⟨decodeUniversal_encodeUniversal, encodeUniversal_decodeUniversal,
   encodeUniversal_bijective, decodeSet_encodeSet, encodeSet_decodeSet⟩

/-- The faithful species-weighted observable separates occurrences: the index indicator reads the
amount of exactly the selected occurrence, even when states coincide. -/
theorem speciesWeightedObservable_certificate
    (U : UniversalShape) (s : HeterogeneousSample U.I U.shape) (i0 : U.I) :
    speciesWeighted U s (indexIndicator U i0) = s.val.amount i0 :=
  speciesWeighted_indexIndicator U s i0

/-- The observable is pushed forward exactly along the existing whole-record encoding. -/
theorem speciesWeightedPushforward_certificate
    (U : UniversalShape) (s : HeterogeneousSample U.I U.shape)
    (φ : ConstituentCarrier U → ℝ) :
    canonicalSpeciesWeighted U
        (OrganicStereoHeterogeneousSamples.encode U.shape U.indexing s)
        (fun p => φ (carrierDecode U p)) = speciesWeighted U s φ :=
  canonicalSpeciesWeighted_encode U s φ

/-- The mixed uncertainty set contains a two-constituent and a three-constituent whole sample,
they are distinct, and the set is recovered exactly. -/
theorem mixedUncertainty_certificate :
    mixedTwo ∈ mixedUncertainty ∧
      mixedThree ∈ mixedUncertainty ∧
      constituentCount mixedTwo.1 = 2 ∧
      constituentCount mixedThree.1 = 3 ∧
      mixedTwo ≠ mixedThree ∧
      decodeSet (encodeSet mixedUncertainty) = mixedUncertainty :=
  ⟨mixedTwo_mem, mixedThree_mem, constituentCount_mixedTwo, constituentCount_mixedThree,
   mixedTwo_ne_mixedThree, mixedUncertainty_recovery⟩

/-- The atom/edge uncertainty set contains two one-constituent records with different atom and
edge counts, and is recovered exactly. -/
theorem atomEdgeUncertainty_certificate :
    singleRichSample ∈ atomEdgeUncertainty ∧
      singlePoorSample ∈ atomEdgeUncertainty ∧
      totalAtomCount singleRichSample.1 = 2 ∧
      totalAtomCount singlePoorSample.1 = 3 ∧
      totalEdgeCount singleRichSample.1 = 1 ∧
      totalEdgeCount singlePoorSample.1 = 0 ∧
      decodeSet (encodeSet atomEdgeUncertainty) = atomEdgeUncertainty :=
  ⟨singleRich_mem, singlePoor_mem, totalAtomCount_singleRich, totalAtomCount_singlePoor,
   totalEdgeCount_singleRich, totalEdgeCount_singlePoor, atomEdgeUncertainty_recovery⟩

/-- The correlated uncertainty set retains two distinct records with equal component marginals but
different occurrence amounts, and the joint pairing is preserved exactly. -/
theorem correlatedUncertainty_certificate :
    mixedTwo ∈ correlatedUncertainty ∧
      swappedTwo ∈ correlatedUncertainty ∧
      mixedTwo ≠ swappedTwo ∧
      speciesWeighted mixedTwoShape MarginalSeparation.sampleA
          (indexIndicator mixedTwoShape (0 : Fin 2)) = 2 ∧
      speciesWeighted mixedTwoShape MarginalSeparation.sampleB
          (indexIndicator mixedTwoShape (0 : Fin 2)) = 1 ∧
      decodeSet (encodeSet correlatedUncertainty) = correlatedUncertainty :=
  ⟨mixedTwo_mem_correlated, swappedTwo_mem_correlated, mixedTwo_ne_swappedTwo,
   correlated_joint_pairing.1, correlated_joint_pairing.2, correlatedUncertainty_recovery⟩

/-- The specified count-preserving fixed-index embedding is not surjective.  This is a strictness
statement about that specified map only. -/
theorem fixedIndexEmbedding_certificate :
    ¬ Function.Surjective
        (fixedIndexEmbed (Fin 2) twoAtomShape twoAtomIndexing) :=
  fixedIndexEmbed_not_surjective

/-! ## Computed written phantom candidates -/

/-- Computed written phantom admission is exactly nonemptiness of the written configuration
frame.  This is a frame-membership characterization, not a descriptor-existence claim. -/
theorem writtenPhantomMembership_certificate (mol : RawMolecule) (center : Nat) :
    center ∈ writtenPhantomCandidates mol ↔
      Nonempty (WrittenConfigurationFrame mol center) :=
  mem_writtenPhantomCandidates_iff mol center

/-- The computed candidate enumeration is duplicate-free and the phantom sentinel is outside the
physical atom indices and outside the candidate list. -/
theorem writtenPhantomEnumeration_certificate (mol : RawMolecule) :
    (writtenPhantomCandidates mol).Nodup ∧
      mol.atomCount ∉ writtenPhantomCandidates mol ∧
      mol.atomAt? mol.atomCount = none :=
  ⟨writtenPhantomCandidates_nodup mol,
   (phantom_sentinel_not_real_atom mol).1,
   (phantom_sentinel_not_real_atom mol).2⟩

/-- A computed candidate routes through the existing tetrahedral assignment machinery as a
tetrahedral stereo unit, under the accepted parsed-atom and non-extended hypotheses. -/
theorem writtenPhantomDescriptorRouting_certificate
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (parsed_eq : result.parsed.atomAt? center = mol.atomAt? center)
    (not_extended : mol.isExtendedTetrahedralParityCarrier center = false)
    (mem : center ∈ writtenPhantomCandidates mol) :
    (∃ outcome,
        tetrahedralAssignment? result mol state fuel center =
          some { unit := StereoUnit.tetrahedral center, outcome := outcome }) ∧
      (∃ outcome,
        { unit := StereoUnit.tetrahedral center, outcome := outcome } ∈
          tetrahedralAssignments result mol state fuel) :=
  ⟨tetrahedralAssignment?_eq_some_of_candidate result mol state fuel center
      parsed_eq not_extended mem,
   mem_tetrahedralAssignments_of_candidate result mol state fuel center
      parsed_eq not_extended mem⟩

/-- The concrete ethyl methyl sulfoxide fixture computes exactly the sulfur center as its written
phantom candidate, the sulfur center has a nonempty frame and the existing notional certificate,
and the sentinel is not a candidate. -/
theorem ethylMethylSulfoxide_fixture_certificate :
    writtenPhantomCandidates ethylMethylSulfoxide = [0] ∧
      0 ∈ writtenPhantomCandidates ethylMethylSulfoxide ∧
      Nonempty (WrittenConfigurationFrame ethylMethylSulfoxide 0) ∧
      NotionalTetrahedralFrameCertificate ethylMethylSulfoxide 0 ∧
      ethylMethylSulfoxide.atomCount ∉
        writtenPhantomCandidates ethylMethylSulfoxide :=
  ⟨ethylMethylSulfoxide_writtenPhantomCandidates,
   ethylMethylSulfoxide_center_mem_writtenPhantomCandidates,
   ethylMethylSulfoxide_nonempty_frame,
   ethylMethylSulfoxide_certificate,
   ethylMethylSulfoxide_phantom_not_candidate⟩

/-! ## Implicit-protium materialization and exact restore -/

/-- Expansion materializes one tagged protium atom and one selected covalent pair interaction for
every supplied slot. -/
theorem implicitHSlotMaterialization_certificate
    {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ)
    (h : HydrogenSlot count) :
    (expand graph count).atomData (Sum.inr h) = materializedHydrogenAtom ∧
      hydrogenBond count h ∈ (expand graph count).interactions ∧
      (hydrogenBond count h).1 = [(Sum.inl h.1 : ExpandedLabel count), Sum.inr h] ∧
      (hydrogenBond count h).2 = SemanticInteractionKind.covalent 1 :=
  expand_materializes_slot graph count h

/-- Restriction after expansion recovers the exact source graph, and the introduced slot family is
the entire duplicate-free canonical slot enumeration. -/
theorem implicitHMaterialization_certificate
    {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ) :
    restore count (expand graph count) = graph ∧
      (introducedSlots count (expand graph count)).Nodup ∧
      (∀ h : HydrogenSlot count, h ∈ introducedSlots count (expand graph count)) ∧
      introducedSlots count (expand graph count) = hydrogenOccurrences count := by
  obtain ⟨hnodup, hcomplete, hexact⟩ := introducedSlots_expand_exact graph count
  exact ⟨restore_expand graph count, hnodup, hcomplete, hexact⟩

/-- Every supplied slot yields an injective site identity of electronic kind `implicitProtium`, and
every identity of that kind is realized by a supplied slot. -/
theorem implicitHSiteIdentity_certificate
    {V : Type u} [DecidableEq V] [Fintype V]
    {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph) :
    Function.Injective (materializedSiteIdentity siteSource) ∧
      (∀ (identity : IndependentSiteIdentity siteSource.siteCounts),
        identity.kind = SiteKind.electronic ElectronicSiteKind.implicitProtium →
        ∃ h : HydrogenSlot (siteImplicitCount siteSource),
          materializedSiteIdentity siteSource h = identity) :=
  ⟨materializedSiteIdentity_injective siteSource,
   fun identity kindEq =>
     materializedSiteIdentity_surjective siteSource identity kindEq⟩

/-- Existing old-old pair bonds are preserved exactly and every introduced old-hydrogen pair bond
has positive order. -/
theorem implicitHPairBond_certificate
    {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ)
    (a b : V) (h : HydrogenSlot count) :
    pairBond (expand graph count) (Sum.inl a) (Sum.inl b) = pairBond graph a b ∧
      0 < pairBond (expand graph count) (Sum.inl h.1) (Sum.inr h) :=
  ⟨pairBond_expand_inl_inl graph count a b,
   pairBond_expand_selected_pos graph count h⟩

/-- Concrete CHBrClF materialization fixture: five expanded atoms, the expanded carbon is an actual
tetrahedral center, the heavy graph alone has no detected center, restore recovers the source, and
the four direct CIP priority labels are the four distinct halogen/hydrogen labels. -/
theorem chbrclfMaterialization_fixture_certificate :
    Fintype.card (ExpandedLabel fixtureImplicitCount) = 5 ∧
      fixtureExpandedMoleculeGraph.IsTetrahedralCenter (Sum.inl (0 : Fin 4)) ∧
      Sum.inl (0 : Fin 4) ∈ fixtureExpandedMoleculeGraph.tetrahedralCenterSet ∧
      fixtureHeavyGraph.tetrahedralCenterSet = (∅ : Finset (Fin 4)) ∧
      restore fixtureImplicitCount
          (OrganicStereoInventoryImplicitHMaterialization.fixtureExpandedGraph) =
        OrganicStereoInventoryImplicitHMaterialization.fixtureGraph ∧
      (fixtureCarbonNeighbors.map
          (MoleculeGraph.rawCIPAtomLabel fixtureExpandedMoleculeGraph)) =
        [toLex ((35 : ℕ), 0), toLex ((17 : ℕ), 0), toLex ((9 : ℕ), 0),
          toLex ((1 : ℕ), 0)] ∧
      (fixtureCarbonNeighbors.map fun w =>
          MoleculeGraph.cipKeyFrom fixtureExpandedMoleculeGraph
            (Sum.inl (0 : Fin 4)) w).Nodup :=
  ⟨fixtureExpanded_five_atoms,
   fixtureExpanded_center_tetrahedral,
   fixtureExpanded_center_mem_detected,
   fixtureHeavyGraph_no_detected_center,
   fixture_restore_expanded,
   expanded_direct_priority_labels,
   expanded_cipKeys_nodup⟩

/-- The expanded CHBrClF one-center molecule is stereogenic by CIP because its four CIP keys on
the carbon neighbors are injective. -/
theorem chbrclfCIP_fixture_certificate :
    OneCenterMolecule.StereogenicByCIP fixtureOneCenterMolecule :=
  fixtureOneCenter_stereogenicByCIP

/-- Explicit injectivity form of the CHBrClF neighbor CIP keys. -/
theorem chbrclfCIPKeyInjective_certificate
    {x y : ExpandedLabel fixtureImplicitCount}
    (hx : x ∈ fixtureCarbonNeighbors) (hy : y ∈ fixtureCarbonNeighbors)
    (hkey :
      MoleculeGraph.cipKeyFrom fixtureExpandedMoleculeGraph (Sum.inl (0 : Fin 4)) x =
        MoleculeGraph.cipKeyFrom fixtureExpandedMoleculeGraph (Sum.inl (0 : Fin 4)) y) :
    x = y :=
  fixture_cipKeyFrom_inj_on_neighbors hx hy hkey

/-! ## Universal finite-graph molecular inhabitance -/

/-- For every finite atom interaction hypergraph and every atom enumeration, the constructed
inhabitant retains the exact source graph and interaction list, the structural selected endpoints
and occurrence indices, injective positions, derived completeness, the exact molecular-evidence
request, and exact assembled/canonical recovery.  No map, arc, geometric law, coverage hypothesis
or inhabitance hypothesis is an input. -/
theorem finiteGraphMolecularInhabitance_certificate
    {V : Type} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (constructedInhabitant graph enumeration).data.graph = graph ∧
      (constructedInhabitant graph enumeration).data.graph.interactions = graph.interactions ∧
      (∀ edge : SelectedBondIndex graph,
        (constructedInhabitant graph enumeration).data.source edge = selectedSource graph edge) ∧
      (∀ edge : SelectedBondIndex graph,
        (constructedInhabitant graph enumeration).data.target edge = selectedTarget graph edge) ∧
      (∀ edge : SelectedBondIndex graph,
        (constructedInhabitant graph enumeration).data.interactionOccurrence edge =
          selectedOccurrence graph edge) ∧
      Function.Injective
        (constructedInhabitant graph enumeration).data.interactionOccurrence ∧
      Function.Injective
        (constructedInhabitant graph enumeration).data.conformation ∧
      (constructedInhabitant graph enumeration).data.CompleteForSourcePairBonds enumeration ∧
      (constructedInhabitant graph enumeration).evidence.graph = graph ∧
      (OrganicStereoMolecularEvidenceAssembly.assemble
          (constructedInhabitant graph enumeration).evidence).stateGraph = graph ∧
      OrganicStereoMolecularEvidenceAssembly.decodedPaths?
          (OrganicStereoMolecularEvidenceAssembly.assemble
            (constructedInhabitant graph enumeration).evidence) =
        some (independentPathFamily (constructedInhabitant graph enumeration).data) ∧
      OrganicStereoMolecularEvidenceAssembly.decode
          (OrganicStereoMolecularCanonicalTransport.canonicalDecode
            (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
              (constructedInhabitant graph enumeration).evidence)) =
        (constructedInhabitant graph enumeration).evidence :=
  universal_finiteGraph_molecular_inhabitance graph enumeration

/-- Nonempty actual structural geometry fixture: the one-bond source graph has exactly one
selected occurrence, the constructed data is complete and retains the source, the documented table
has cardinality one, the oriented endpoints are `false`/`true`, and the constructed arc starts and
ends at the constructed atom positions. -/
theorem nonemptyInhabitanceFixture_certificate :
    Fintype.card (SelectedBondIndex toySourceGraph) = 1 ∧
      (inhabitedData toySourceGraph).graph = toySourceGraph ∧
      (inhabitedData toySourceGraph).CompleteForSourcePairBonds (Fintype.equivFin Bool) ∧
      ((inhabitedData toySourceGraph).toBondPathTable
        (Fintype.equivFin Bool)).documented.card = 1 ∧
      (∀ edge : SelectedBondIndex toySourceGraph,
        (inhabitedData toySourceGraph).source edge = false) ∧
      (∀ edge : SelectedBondIndex toySourceGraph,
        (inhabitedData toySourceGraph).target edge = true) ∧
      (∀ edge : SelectedBondIndex toySourceGraph,
        (inhabitedData toySourceGraph).arc edge 0 =
          (inhabitedEmbedding toySourceGraph).conformation false) ∧
      (∀ edge : SelectedBondIndex toySourceGraph,
        (inhabitedData toySourceGraph).arc edge 1 =
          (inhabitedEmbedding toySourceGraph).conformation true) :=
  toy_inhabitance

/-- Unselected hyperedges are preserved verbatim, while completeness holds for every atom
enumeration of the mixed fixture. -/
theorem mixedFixturePreservation_certificate
    (enumeration : Fin 3 ≃ Fin (Fintype.card (Fin 3))) :
    ([0, 1, 2], SemanticInteractionKind.multicenter 4) ∈
        (inhabitedData mixedFixtureGraph).graph.interactions ∧
      (inhabitedData mixedFixtureGraph).CompleteForSourcePairBonds enumeration :=
  ⟨mixedFixture_unselected_preserved, mixedFixture_complete enumeration⟩

/-- Empty actual structural fixture: the interaction-free one-atom source has constructed data
retaining the source graph, vacuously complete path data, and an empty documented table. -/
theorem emptyInhabitanceFixture_certificate :
    (inhabitedData OrganicStereoEmbeddedMolecularGraphCoverage.fixtureGraph).graph =
        OrganicStereoEmbeddedMolecularGraphCoverage.fixtureGraph ∧
      (inhabitedData OrganicStereoEmbeddedMolecularGraphCoverage.fixtureGraph).CompleteForSourcePairBonds (Equiv.refl (Fin 1)) ∧
      ((inhabitedData OrganicStereoEmbeddedMolecularGraphCoverage.fixtureGraph).toBondPathTable
        (Equiv.refl (Fin 1))).documented.card = 0 :=
  fixture_inhabitance

/-! ## Transitive kernel-authority checks

Every declaration below is checked for closure under the standard logical axioms only. -/

/-! ### Finite loopless graph embedding -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphEmbedding.globalMap
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphEmbedding.globalMap_continuous
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphEmbedding.globalMap_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphEmbedding.finiteGraphEmbedded
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphEmbedding.finiteGraphEmbedded_map
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphEmbedding.finiteGraphEmbedded_conformation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphEmbedding.finiteGraphEmbedded_atom_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphEmbedding.finiteGraphEmbedded_arc_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphEmbedding.finiteGraphEmbedded_intersects_only_at_common_endpoints

/-! ### Moment-curve separation -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMomentCurveSeparation.momentCurve
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMomentCurveSeparation.momentCurve_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMomentCurveSeparation.momentCurve_eq_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMomentCurveSeparation.momentCurve_affineIndependent_fin
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMomentCurveSeparation.momentCurve_affineIndependent_finset
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMomentCurveSeparation.segmentPoint
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMomentCurveSeparation.segmentPath
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMomentCurveSeparation.segmentPoint_eq_iff_same_pair
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMomentCurveSeparation.segmentPoint_swap_eq_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMomentCurveSeparation.segmentPoint_eq_momentCurve_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMomentCurveSeparation.segmentPoint_eq_iff_endpointCollision
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMomentCurveSeparation.segmentPoint_ne_of_disjoint_endpoints
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMomentCurveSeparation.SameUnorderedPair
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMomentCurveSeparation.EndpointCollision

/-! ### Realized cycles -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedCycleRealization.CycleWalk.edges_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedCycleRealization.CycleWalk.src_ne_dst
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedCycleRealization.cycleMap
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedCycleRealization.cycleMap_continuous
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedCycleRealization.cycleMap_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedCycleRealization.cycleSpatialMap
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedCycleRealization.cycleSpatialMap_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedCycleRealization.cycleSpatialMap_isClosedEmbedding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedCycleRealization.cycleSpatialMap_range
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedCycleRealization.exists_continuous_injective_cycleMap
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedCycleRealization.cycleImage_inter_eq_commonVertexImages
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedCycleRealization.cycleImage_inter_eq_commonVertexImages_of_edgeDisjoint
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedCycleRealization.cycleImage_inter_eq_singleton_of_sole_common_vertex

/-! ### Spiro coverage from the mechanically valid carrier -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.firstRingWalk
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.secondRingWalk
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.firstRingWalk_vertex_mem
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.secondRingWalk_vertex_mem
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.firstRingWalk_bond
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.secondRingWalk_bond
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.firstRingWalk_map_vertex
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.secondRingWalk_map_vertex
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.ringWalk_edges_disjoint
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.firstRingWalk_inter_secondRingWalk_eq_center
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.spiro_embedded_cycle_coverage

/-! ### Ambient motion and oriented-volume obstruction -/

assert_kernel_only
  TetraStereo.OneCenter.shearHomeomorph
assert_kernel_only
  TetraStereo.OneCenter.shearMotion
assert_kernel_only
  TetraStereo.OneCenter.shearMotion_endpoint_volume
assert_kernel_only
  TetraStereo.OneCenter.shearMotion_endpoint_reverses_four_point_volume
assert_kernel_only
  TetraStereo.OneCenter.exists_ambient_motion_endpoint_reversing_four_point_volume
assert_kernel_only
  TetraStereo.OneCenter.shearMotion_endpoint_reverses_real_sign
assert_kernel_only
  TetraStereo.OneCenter.shearTrajectory_crosses_coplanar_without_collision
assert_kernel_only
  TetraStereo.OneCenter.shearTrajectory_volume_eq_zero_iff
assert_kernel_only
  TetraStereo.OneCenter.fixtureTrajectory_opposite_endpoint_signs
assert_kernel_only
  TetraStereo.OneCenter.fixtureTrajectory_exists_zero_volume

/-! ### Variable-shape mixture records -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.encodeUniversal
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.decodeUniversal
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.decodeUniversal_encodeUniversal
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.encodeUniversal_decodeUniversal
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.encodeUniversal_bijective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.encodeSet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.decodeSet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.decodeSet_encodeSet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.encodeSet_decodeSet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.speciesWeighted
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.speciesWeighted_eq_amountWeighted
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.canonicalSpeciesWeighted
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.speciesWeighted_indexIndicator
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.canonicalSpeciesWeighted_encode
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.speciesWeighted_decode
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.canonicalSpeciesWeighted_encoded_indexIndicator
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.mixedTwo
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.mixedThree
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.singleRichSample
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.singlePoorSample
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.mixedUncertainty
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.mixedTwo_mem
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.mixedThree_mem
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.singleRich_mem
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.singlePoor_mem
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.mixedUncertainty_recovery
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.atomEdgeUncertainty_recovery
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.correlatedUncertainty_recovery
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.correlated_joint_pairing
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.mixedTwo_ne_mixedThree
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.mixedTwo_ne_swappedTwo
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.repeated_states_occurrence_amounts
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.repeated_states_total
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoUniversalMixtureSamples.fixedIndexEmbed_not_surjective

/-! ### Computed written phantom candidates -/

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.TrigonalPyramidal.writtenPhantomCandidates
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.TrigonalPyramidal.mem_writtenPhantomCandidates_iff
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.TrigonalPyramidal.writtenPhantomCandidates_nodup
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.TrigonalPyramidal.phantom_sentinel_not_real_atom
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.TrigonalPyramidal.writtenPhantomCandidate_certificate
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.TrigonalPyramidal.tetrahedralAssignment?_eq_some_of_candidate
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.TrigonalPyramidal.mem_tetrahedralAssignments_of_candidate
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.TrigonalPyramidal.ethylMethylSulfoxide
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.TrigonalPyramidal.ethylMethylSulfoxide_writtenPhantomCandidates
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.TrigonalPyramidal.ethylMethylSulfoxide_center_mem_writtenPhantomCandidates
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.TrigonalPyramidal.ethylMethylSulfoxide_nonempty_frame
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.TrigonalPyramidal.ethylMethylSulfoxide_certificate
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.TrigonalPyramidal.ethylMethylSulfoxide_phantom_not_candidate

/-! ### Implicit-protium materialization -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.expand
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.restore
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.restore_expand
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.introducedSlots
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.introducedSlots_expand
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.introducedSlots_expand_exact
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.expand_materializes_slot
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.materializedSiteIdentity
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.materializedSiteIdentity_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.materializedSiteIdentity_surjective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.nonProtiumPayload_reconstruct
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.nonProtiumSiteCounts_reconstruct
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.pairBond_expand_inl_inl
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.pairBond_expand_selected_pos
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.fixtureExpanded_five_atoms
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.fixtureExpanded_center_tetrahedral
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.fixtureExpanded_center_mem_detected
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.fixtureHeavyGraph_no_detected_center
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.fixture_restore_expanded
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.expanded_direct_priority_labels
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.expanded_cipKeys_nodup
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.fixture_cipKeyFrom_inj_on_neighbors
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization.fixtureOneCenter_stereogenicByCIP

/-! ### Universal finite-graph molecular inhabitance -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.selectedNoLoops
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedEmbedding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedData
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedGeometry
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedEvidence
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedData_complete
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedData_documented_eq_selected_image
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedData_parallel_occurrences_distinct
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.constructedInhabitant
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.universal_finiteGraph_molecular_inhabitance
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.fixture_inhabitance
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.toy_inhabitance
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.mixedFixture_unselected_preserved
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.mixedFixture_complete

/-! ### The type-explicit certificate theorems of this module -/

assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.finiteGraphEmbedding_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.momentCurveSeparatedSegments_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.momentCurveDisjointSegments_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.momentCurveSegmentEndpoint_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.momentCurveAffineIndependent_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.embeddedCycle_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.embeddedCycleCommonVertexImages_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.embeddedCycleSoleCommonVertex_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.spiroCoverage_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.shearMotionAmbient_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.shearTrajectoryObstruction_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.ambientMotionEndpoint_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.shearTrajectoryZeroTime_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.fixtureTrajectorySign_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.universalMixtureEncoding_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.speciesWeightedObservable_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.speciesWeightedPushforward_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.mixedUncertainty_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.atomEdgeUncertainty_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.correlatedUncertainty_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.fixedIndexEmbedding_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.writtenPhantomMembership_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.writtenPhantomEnumeration_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.writtenPhantomDescriptorRouting_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.ethylMethylSulfoxide_fixture_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.implicitHSlotMaterialization_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.implicitHMaterialization_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.implicitHSiteIdentity_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.implicitHPairBond_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.chbrclfMaterialization_fixture_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.chbrclfCIP_fixture_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.chbrclfCIPKeyInjective_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.finiteGraphMolecularInhabitance_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.nonemptyInhabitanceFixture_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.mixedFixturePreservation_certificate
assert_kernel_only
  TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate.emptyInhabitanceFixture_certificate

end

end TetraStereo.Examples.OrganicStereoConstructiveCoverageKernelCertificate
