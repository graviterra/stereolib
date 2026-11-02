import TetraStereo.OneCenter.CIPAuthoritativeExactExpansion
import TetraStereo.OneCenter.CIPAuthoritativeConstitutionalConformance
import TetraStereo.OneCenter.CIPMoleculeDigraphConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open DeclarativeCIP
open ProductionCIPOccurrenceDiscovery

namespace AuthoritativeCIPDiscovery

/-- All four width-unbounded authoritative branches of one molecule-derived final center. -/
structure CenterDiscovery (mol : RawMolecule) (root : Root mol) where
  branch : (slot : Fin 4) →
    CompleteBranchDiscovery mol (centerAtom root) (ligandAtom root slot)

def centerBranchesSucceeded? (mol : RawMolecule) (root : Root mol) : Bool :=
  (List.finRange 4).all fun slot =>
    (CompleteBranchDiscovery.discover? mol (centerAtom root) (ligandAtom root slot)).isSome

theorem centerBranch_isSome_of_succeeded (mol : RawMolecule) (root : Root mol)
    (accepted : centerBranchesSucceeded? mol root = true) (slot : Fin 4) :
    (CompleteBranchDiscovery.discover? mol (centerAtom root)
      (ligandAtom root slot)).isSome := by
  exact List.all_eq_true.mp accepted slot (by simp)

def discoverCenter? (mol : RawMolecule) (root : Root mol) :
    Option (CenterDiscovery mol root) :=
  if accepted : centerBranchesSucceeded? mol root = true then
    let discovered := fun slot =>
      Option.get
        (CompleteBranchDiscovery.discover? mol (centerAtom root) (ligandAtom root slot))
        (centerBranch_isSome_of_succeeded mol root accepted slot)
    some { branch := discovered }
  else none

@[simp] theorem discoverCenter?_isSome (mol : RawMolecule) (root : Root mol) :
    (discoverCenter? mol root).isSome = centerBranchesSucceeded? mol root := by
  unfold discoverCenter?
  split <;> simp_all

theorem CenterDiscovery.unique {mol : RawMolecule} {root : Root mol}
    (first second : CenterDiscovery mol root) : first = second := by
  cases first with
  | mk firstBranch =>
      cases second with
      | mk secondBranch =>
          congr
          funext slot
          exact CompleteBranchDiscovery.unique (firstBranch slot) (secondBranch slot)

theorem CenterDiscovery.branchesSucceeded {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) : centerBranchesSucceeded? mol root = true := by
  unfold centerBranchesSucceeded?
  rw [List.all_eq_true]
  intro slot _
  rw [CompleteBranchDiscovery.discover?_eq_some (discovery.branch slot)]
  rfl

@[simp] theorem CenterDiscovery.discovered {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) :
    discoverCenter? mol root = some discovery := by
  unfold discoverCenter?
  split
  · exact congrArg some (CenterDiscovery.unique _ _)
  · rename_i rejected
    exact (rejected discovery.branchesSucceeded).elim

/-- Exact structural completeness of the four authoritative ligand hierarchies at one center. -/
structure CompleteCenterHierarchy {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) : Prop where
  branchExact : ∀ slot,
    (discovery.branch slot).key.ChildrenExact mol

theorem completeCenterHierarchy {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) : CompleteCenterHierarchy discovery where
  branchExact := fun slot =>
    mol.branchCanonicalKeyAuthoritative?_childrenExact
      (centerAtom root).val (ligandAtom root slot) (discovery.branch slot).key
      (discovery.branch slot).accepted (discovery.branch slot).complete

/-- Exact constitutional comparison of every ordered pair of physical ligand hierarchies at one
center. This is a relational statement over all outcomes, not a sampled regression. A lone-pair
slot has no physical `Fin atomCount` witness and is therefore outside this molecular-digraph
relation. -/
structure ExactConstitutionalCenterHierarchy {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) : Prop where
  comparison : ∀ (left right : Fin 4)
      (leftLigand rightLigand : Fin mol.atomCount),
    leftLigand.val = ligandAtom root left →
    rightLigand.val = ligandAtom root right →
    ∀ outcome : Ordering,
    RawMolecule.compareCanonicalBranchKeys
        (discovery.branch left).key (discovery.branch right).key = outcome ↔
      RawMolecule.ExactConstitutionalHierarchyFirstStrictOutcome mol.toMoleculeGraph
        ((discovery.branch left).key.toDeclarativeDigraph mol)
        ((discovery.branch left).key.declarativeAddressing mol)
        ((discovery.branch right).key.toDeclarativeDigraph mol)
        ((discovery.branch right).key.declarativeAddressing mol)
        outcome

/-- Structural admission plus checked Rule-2 data lift the pairwise constitutional theorem to all
ordered physical-ligand pairs of a successfully discovered center. -/
theorem exactConstitutionalCenterHierarchy {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root)
    (admitted : mol.Admissible) (known : mol.Rule2MassesKnown) :
    ExactConstitutionalCenterHierarchy discovery where
  comparison := by
    intro left right leftLigand rightLigand leftEq rightEq outcome
    exact RawMolecule.branchCanonicalKeysAuthoritative_exactConstitutionalHierarchyFirstStrict_iff
      mol (centerAtom root) leftLigand rightLigand
      (discovery.branch left).key (discovery.branch right).key admitted known
      (by simpa [leftEq] using (discovery.branch left).accepted)
      (by simpa [rightEq] using (discovery.branch right).accepted)
      (discovery.branch left).complete (discovery.branch right).complete outcome

/-- A total family over every molecule-derived eligible center. -/
structure Discovery (mol : RawMolecule) where
  center : (root : Root mol) → CenterDiscovery mol root

theorem Discovery.unique {mol : RawMolecule} (first second : Discovery mol) : first = second := by
  cases first with
  | mk firstCenter =>
      cases second with
      | mk secondCenter =>
          congr
          funext root
          exact CenterDiscovery.unique (firstCenter root) (secondCenter root)

def allCentersSucceeded? (mol : RawMolecule) : Bool :=
  (allRoots mol).all fun root => (discoverCenter? mol root).isSome

theorem center_isSome_of_all_succeeded (mol : RawMolecule)
    (accepted : allCentersSucceeded? mol = true) (root : Root mol) :
    (discoverCenter? mol root).isSome := by
  exact List.all_eq_true.mp accepted root (root_mem_allRoots mol root)

def discoverAll? (mol : RawMolecule) : Option (Discovery mol) :=
  if accepted : allCentersSucceeded? mol = true then
    some { center := fun root =>
      (discoverCenter? mol root).get (center_isSome_of_all_succeeded mol accepted root) }
  else none

theorem Discovery.allCentersSucceeded {mol : RawMolecule} (discovery : Discovery mol) :
    allCentersSucceeded? mol = true := by
  unfold allCentersSucceeded?
  rw [List.all_eq_true]
  intro root _
  rw [(discovery.center root).discovered]
  rfl

@[simp] theorem Discovery.discovered {mol : RawMolecule} (discovery : Discovery mol) :
    discoverAll? mol = some discovery := by
  unfold discoverAll?
  split
  · exact congrArg some (Discovery.unique _ _)
  · rename_i rejected
    exact (rejected discovery.allCentersSucceeded).elim

@[simp] theorem discoverAll?_isSome (mol : RawMolecule) :
    (discoverAll? mol).isSome = allCentersSucceeded? mol := by
  unfold discoverAll?
  split <;> simp_all

end AuthoritativeCIPDiscovery

namespace BlueBookP92.Digraph

/-- Molecule-wide independent digraph conformance for the width-unbounded authoritative compiler. -/
structure AuthoritativeMoleculeConformance (mol : RawMolecule)
    (discovery : AuthoritativeCIPDiscovery.Discovery mol) : Prop where
  rootCoverage : ∀ center : Fin mol.atomCount,
    FinalUnitEligible mol center → ∃! root : Root mol, centerAtom root = center
  centerHierarchies : ∀ root : Root mol,
    AuthoritativeCIPDiscovery.CompleteCenterHierarchy (discovery.center root)
  physicalBranches : ∀ (root : Root mol) (slot : Fin 4)
      (ligand : Fin mol.atomCount),
    ligand.val = ligandAtom root slot →
      RootedDigraph.FaithfulExactExpansion
        (mol.canonicalHierarchyMoleculeGraph (centerAtom root) ligand)
        (centerAtom root) ligand
        (((discovery.center root).branch slot).key.toDeclarativeDigraph mol)

/-- Molecule-wide exact constitutional refinement for successful authoritative discovery.  It
combines faithful construction of every physical-ligand digraph with exact Rules-1a--2 comparison
of every ordered pair of physical-ligand hierarchies at every perceived tetrahedral center. -/
structure AuthoritativeExactConstitutionalMoleculeConformance (mol : RawMolecule)
    (discovery : AuthoritativeCIPDiscovery.Discovery mol) : Prop where
  moleculeDigraph : AuthoritativeMoleculeConformance mol discovery
  constitutionalHierarchies : ∀ root : Root mol,
    AuthoritativeCIPDiscovery.ExactConstitutionalCenterHierarchy (discovery.center root)

end BlueBookP92.Digraph

namespace AuthoritativeCIPDiscovery.Discovery

/-- Checked stereochemical admission discharges every molecular-integrity premise for a successful
width-unbounded molecule discovery. -/
theorem moleculeConformance_of_stereochemicalAdmissible
    {mol : RawMolecule} (discovery : AuthoritativeCIPDiscovery.Discovery mol)
    (admitted : mol.StereochemicalAdmissible) :
    BlueBookP92.Digraph.AuthoritativeMoleculeConformance mol discovery where
  rootCoverage := fun center eligible => root_coverage_unique mol center eligible
  centerHierarchies := fun root =>
    AuthoritativeCIPDiscovery.completeCenterHierarchy (discovery.center root)
  physicalBranches := by
    intro root slot ligand ligandEq
    have rootBonds := physicalLigandRootsBonded_of_writtenNeighborSound mol
      (BlueBookP92.Digraph.writtenNeighborSound_of_exact mol admitted.2)
    exact ((discovery.center root).branch slot).faithfulExactExpansion
      ligand ligandEq admitted.1 (rootBonds root slot ligand ligandEq)

/-- Checked stereochemical admission and Rule-2 source coverage discharge the complete
molecule-wide structural and constitutional comparison boundary. -/
theorem exactConstitutionalMoleculeConformance_of_stereochemicalAdmissible
    {mol : RawMolecule} (discovery : AuthoritativeCIPDiscovery.Discovery mol)
    (admitted : mol.StereochemicalAdmissible) (known : mol.Rule2MassesKnown) :
    BlueBookP92.Digraph.AuthoritativeExactConstitutionalMoleculeConformance mol discovery where
  moleculeDigraph := discovery.moleculeConformance_of_stereochemicalAdmissible admitted
  constitutionalHierarchies := fun root =>
    AuthoritativeCIPDiscovery.exactConstitutionalCenterHierarchy
      (discovery.center root) admitted.1 known

end AuthoritativeCIPDiscovery.Discovery

end


end TetraStereo.OneCenter
