import TetraStereo.OneCenter.LocalizedRecursivePhysicalDecisionChecks
import TetraStereo.OneCenter.FinitePhysicalBranchSearch
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace TetraStereo.OneCenter.LocalizedPhysicalSearchChecks

open FinitePhysicalBranchSearch LocalizedActualPhysicalBranchDecision
open FinitePhysicalBranchTransport
open LocalizedRecursivePhysicalDecisionChecks

/-! ## Exact generic equivalence -/

/-- On an explicit complete vertex listing, the pruned search computes the accepted physical
pair count. The list is an execution input and is not an assumption narrowing the chemistry. -/
theorem computedPairCountPruned_exact {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center)
    (vertices : List V) (verticesNodup : vertices.Nodup)
    (verticesComplete : ∀ v, v ∈ vertices) :
    computedPairCountPruned m cfg c vertices = computedPairCount m cfg c :=
  FinitePhysicalBranchSearch.computedPairCountPruned_eq m cfg c vertices
    verticesNodup verticesComplete

/-- The pruned actual-coordinate count joins the accepted original calibrated/twin domain
directly to the physical count on the detected molecule. -/
theorem computedPairCountPruned_coordinateCfg_eq_physical
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center)
    (domain : LocalizedRecursiveAuxiliaryPhysicalDomain.RecursiveAuxiliaryPhysicalDomain
      input cfg root)
    (vertices : List input.Atom) (verticesNodup : vertices.Nodup)
    (verticesComplete : ∀ v, v ∈ vertices) :
    computedPairCountPruned (actualCanonicalMolecule input) (coordinateCfg input)
      ⟨root.1, root.2⟩ vertices =
      physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule cfg root := by
  calc
    _ = computedPairCount (actualCanonicalMolecule input) (coordinateCfg input)
        ⟨root.1, root.2⟩ :=
      computedPairCountPruned_eq _ _ _ vertices verticesNodup verticesComplete
    _ = physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule cfg root :=
      computedPairCount_coordinateCfg_eq_physical input cfg root domain

/-! ## Actual 21-atom decorated source -/

open LocalizedRecursiveAuxiliaryParityDecoration

def decoratedVertices : List decoratedCertified.Atom :=
  List.finRange decoratedCertified.certified.input.molecule.atomCount

def decoratedSearchRoot : (actualCanonicalMolecule decoratedCertified).Center :=
  ⟨decRoot.1, decRoot.2⟩

theorem decoratedVertices_nodup : decoratedVertices.Nodup := by
  exact List.nodup_finRange _

theorem decoratedVertices_complete (v : decoratedCertified.Atom) : v ∈ decoratedVertices := by
  simp [decoratedVertices]

/-- info: 0 -/
#guard_msgs in
#eval computedPairCountPruned (actualCanonicalMolecule decoratedCertified)
  (coordinateCfg decoratedCertified) decoratedSearchRoot decoratedVertices

/-! ## Actual 9-atom cyclic source -/

open LocalizedRecursiveCyclicSymmetricFixture

def symmetricVertices : List symmetricCertified.Atom :=
  List.finRange symmetricCertified.certified.input.molecule.atomCount

def symmetricSearchRoot : (actualCanonicalMolecule symmetricCertified).Center :=
  ⟨center0.1, center0.2⟩

def symmetricSearchRoot2 : (actualCanonicalMolecule symmetricCertified).Center :=
  ⟨center2.1, center2.2⟩

def symmetricSearchRoot4 : (actualCanonicalMolecule symmetricCertified).Center :=
  ⟨center4.1, center4.2⟩

theorem symmetricVertices_nodup : symmetricVertices.Nodup := by
  exact List.nodup_finRange _

theorem symmetricVertices_complete (v : symmetricCertified.Atom) : v ∈ symmetricVertices := by
  simp [symmetricVertices]

/-- info: 1 -/
#guard_msgs in
#eval computedPairCountPruned (actualCanonicalMolecule symmetricCertified)
  (coordinateCfg symmetricCertified) symmetricSearchRoot symmetricVertices

/-- info: 1 -/
#guard_msgs in
#eval computedPairCountPruned (actualCanonicalMolecule symmetricCertified)
  (coordinateCfg symmetricCertified) symmetricSearchRoot2 symmetricVertices

/-- info: 1 -/
#guard_msgs in
#eval computedPairCountPruned (actualCanonicalMolecule symmetricCertified)
  (coordinateCfg symmetricCertified) symmetricSearchRoot4 symmetricVertices

end TetraStereo.OneCenter.LocalizedPhysicalSearchChecks

assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalSearchChecks.computedPairCountPruned_exact
assert_kernel_only
  TetraStereo.OneCenter.LocalizedPhysicalSearchChecks.computedPairCountPruned_coordinateCfg_eq_physical
