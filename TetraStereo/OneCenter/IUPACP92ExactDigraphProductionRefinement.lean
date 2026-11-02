import TetraStereo.OneCenter.DeclarativeCIPFaithfulExpansionBisimulation
import TetraStereo.OneCenter.IUPACNext54P92DigraphRule1aReviewedSemantics
import TetraStereo.OneCenter.ProductionCIPFaithfulAssembly

set_option autoImplicit false

/-!
# Production refinement for the exact P-92 digraph family

This module is the first consumer of faithful-expansion representation independence.  A successful
complete production hierarchy is already proved faithful by `ProductionCIPFaithfulAssembly`; an
independently reviewed authority graph is required to be faithful by the P-92 reference.  The
single agreement theorem below therefore yields a rooted, fully labelled, depth-preserving
isomorphism and transports the three exact-digraph discriminants used by the acyclic,
multiple-bond, and cyclic authority rows.

The result is a production/reference refinement boundary.  It does not claim totality of the
low-level production builder: successful completion, raw-molecule well-formedness, unique bond
records, and root adjacency remain explicit hypotheses.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open DeclarativeCIP
open RawMolecule

noncomputable section

universe u

/-! ## Isomorphism-invariant exact-digraph observations -/

def P92GraphHasMultipleBondDuplicate {Atom : Type u} (graph : RootedDigraph Atom) : Prop :=
  ∃ node distance,
    (graph.label node).provenance = NodeProvenance.multipleBondDuplicate distance

def P92GraphHasRingDuplicate {Atom : Type u} (graph : RootedDigraph Atom) : Prop :=
  ∃ node distance,
    (graph.label node).provenance = NodeProvenance.ringDuplicate distance

def P92GraphHasNoRingDuplicate {Atom : Type u} (graph : RootedDigraph Atom) : Prop :=
  ∀ node distance,
    (graph.label node).provenance ≠ NodeProvenance.ringDuplicate distance

theorem p92GraphHasMultipleBondDuplicate_iff_of_iso
    {Atom : Type u} {left right : RootedDigraph Atom}
    (iso : RootedDigraph.Iso left right) :
    P92GraphHasMultipleBondDuplicate left ↔ P92GraphHasMultipleBondDuplicate right := by
  constructor
  · rintro ⟨node, distance, duplicate⟩
    refine ⟨iso.toEquiv node, distance, ?_⟩
    have labelEq := congrArg (fun label : NodeLabel Atom => label.provenance)
      (iso.map_label node)
    exact labelEq.symm.trans duplicate
  · rintro ⟨node, distance, duplicate⟩
    let leftNode := iso.toEquiv.symm node
    refine ⟨leftNode, distance, ?_⟩
    have labelEq := congrArg (fun label : NodeLabel Atom => label.provenance)
      (iso.map_label leftNode)
    have mappedNode : iso.toEquiv leftNode = node := by
      simp [leftNode]
    rw [mappedNode] at labelEq
    exact labelEq.trans duplicate

theorem p92GraphHasRingDuplicate_iff_of_iso
    {Atom : Type u} {left right : RootedDigraph Atom}
    (iso : RootedDigraph.Iso left right) :
    P92GraphHasRingDuplicate left ↔ P92GraphHasRingDuplicate right := by
  constructor
  · rintro ⟨node, distance, duplicate⟩
    refine ⟨iso.toEquiv node, distance, ?_⟩
    have labelEq := congrArg (fun label : NodeLabel Atom => label.provenance)
      (iso.map_label node)
    exact labelEq.symm.trans duplicate
  · rintro ⟨node, distance, duplicate⟩
    let leftNode := iso.toEquiv.symm node
    refine ⟨leftNode, distance, ?_⟩
    have labelEq := congrArg (fun label : NodeLabel Atom => label.provenance)
      (iso.map_label leftNode)
    have mappedNode : iso.toEquiv leftNode = node := by
      simp [leftNode]
    rw [mappedNode] at labelEq
    exact labelEq.trans duplicate

theorem p92GraphHasNoRingDuplicate_iff_of_iso
    {Atom : Type u} {left right : RootedDigraph Atom}
    (iso : RootedDigraph.Iso left right) :
    P92GraphHasNoRingDuplicate left ↔ P92GraphHasNoRingDuplicate right := by
  constructor
  · intro leftHasNone node distance rightDuplicate
    have rightHasDuplicate : P92GraphHasRingDuplicate right :=
      ⟨node, distance, rightDuplicate⟩
    rcases (p92GraphHasRingDuplicate_iff_of_iso iso).mpr rightHasDuplicate with
      ⟨leftNode, leftDistance, leftDuplicate⟩
    exact leftHasNone leftNode leftDistance leftDuplicate
  · intro rightHasNone node distance leftDuplicate
    have leftHasDuplicate : P92GraphHasRingDuplicate left :=
      ⟨node, distance, leftDuplicate⟩
    rcases (p92GraphHasRingDuplicate_iff_of_iso iso).mp leftHasDuplicate with
      ⟨rightNode, rightDistance, rightDuplicate⟩
    exact rightHasNone rightNode rightDistance rightDuplicate

@[simp] theorem p92Observation_hasMultipleBondDuplicate_iff
    (observation : P92ExactDigraphAuthorityObservation) :
    observation.HasMultipleBondDuplicate ↔
      P92GraphHasMultipleBondDuplicate observation.graph.toRootedDigraph :=
  Iff.rfl

@[simp] theorem p92Observation_hasRingDuplicate_iff
    (observation : P92ExactDigraphAuthorityObservation) :
    observation.HasRingDuplicate ↔
      P92GraphHasRingDuplicate observation.graph.toRootedDigraph :=
  Iff.rfl

@[simp] theorem p92Observation_hasNoRingDuplicate_iff
    (observation : P92ExactDigraphAuthorityObservation) :
    observation.HasNoRingDuplicate ↔
      P92GraphHasNoRingDuplicate observation.graph.toRootedDigraph :=
  Iff.rfl

/-! ## One agreement certificate for all three exact-digraph rows -/

inductive P92ExactDigraphProductionReferenceAgreement
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (production reference : RootedDigraph Atom) : Prop where
  | intro
      (productionFaithful :
        RootedDigraph.FaithfulExactExpansion molecule externalParent ligand production)
      (referenceFaithful :
        RootedDigraph.FaithfulExactExpansion molecule externalParent ligand reference)
      (iso : RootedDigraph.Iso production reference)
      (multipleBondDuplicate_iff :
        P92GraphHasMultipleBondDuplicate production ↔
          P92GraphHasMultipleBondDuplicate reference)
      (ringDuplicate_iff :
        P92GraphHasRingDuplicate production ↔ P92GraphHasRingDuplicate reference)
      (noRingDuplicate_iff :
        P92GraphHasNoRingDuplicate production ↔ P92GraphHasNoRingDuplicate reference)

theorem P92ExactDigraphProductionReferenceAgreement.ofFaithful
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (production reference : RootedDigraph Atom)
    (productionFaithful :
      RootedDigraph.FaithfulExactExpansion molecule externalParent ligand production)
    (referenceFaithful :
      RootedDigraph.FaithfulExactExpansion molecule externalParent ligand reference) :
    P92ExactDigraphProductionReferenceAgreement molecule externalParent ligand production
      reference := by
  rcases RootedDigraph.faithfulExactExpansion_unique_up_to_iso molecule externalParent ligand
    production reference productionFaithful referenceFaithful with ⟨iso⟩
  exact .intro productionFaithful referenceFaithful iso
    (p92GraphHasMultipleBondDuplicate_iff_of_iso iso)
    (p92GraphHasRingDuplicate_iff_of_iso iso)
    (p92GraphHasNoRingDuplicate_iff_of_iso iso)

/-! ## The concrete production hierarchy at the reviewed observation boundary -/

noncomputable def p92ProductionExactDigraphObservation
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey) : P92ExactDigraphAuthorityObservation where
  atomCount := mol.atomCount
  molecule := mol.canonicalHierarchyMoleculeGraph center ligand
  externalParent := center
  ligand := ligand
  graph := P92FiniteRootedDigraph.ofRootedDigraph (key.toDeclarativeDigraph mol)

noncomputable def p92ProductionExactDigraphObservation_graphIso
    (mol : RawMolecule) (key : CanonicalBranchKey) :
    RootedDigraph.Iso (key.toDeclarativeDigraph mol)
      (P92FiniteRootedDigraph.ofRootedDigraph
        (key.toDeclarativeDigraph mol)).toRootedDigraph :=
  P92FiniteRootedDigraph.ofRootedDigraphIso (key.toDeclarativeDigraph mol)

theorem p92ProductionExactDigraphObservation_faithful
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (wellFormed : mol.WellFormed)
    (bondRecordsUnique : mol.BondRecordsUnique)
    (built : branchCanonicalKey? mol center ligand = some key)
    (complete : key.complete = true)
    (rootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand) :
    (p92ProductionExactDigraphObservation mol center ligand key).Faithful := by
  apply (RootedDigraph.faithfulExactExpansion_iso_iff
    (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
    (p92ProductionExactDigraphObservation_graphIso mol key)).1
  exact mol.branchCanonicalKey?_faithfulExactExpansion center ligand key wellFormed
    bondRecordsUnique built complete rootBond

/-- A successful complete production hierarchy refines every faithful independent expansion of
the same normalized molecular branch, simultaneously for the three exact P-92 digraph rows. -/
theorem branchCanonicalKey?_p92ExactDigraph_refines
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (wellFormed : mol.WellFormed)
    (bondRecordsUnique : mol.BondRecordsUnique)
    (built : branchCanonicalKey? mol center ligand = some key)
    (complete : key.complete = true)
    (rootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
    (reference : RootedDigraph (Fin mol.atomCount))
    (referenceFaithful : RootedDigraph.FaithfulExactExpansion
      (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand reference) :
    P92ExactDigraphProductionReferenceAgreement
      (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
      (key.toDeclarativeDigraph mol) reference :=
  P92ExactDigraphProductionReferenceAgreement.ofFaithful
    (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
    (key.toDeclarativeDigraph mol) reference
    (mol.branchCanonicalKey?_faithfulExactExpansion center ligand key wellFormed
      bondRecordsUnique built complete rootBond)
    referenceFaithful

/-! ## Direct projections into the three independent authority references -/

theorem p92ProductionAcyclicDigraph_judged
    (source : AuthoritativeChemicalInput)
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (represents : P92CanonicalConstitutionRepresents source center ligand
      (mol.canonicalHierarchyMoleculeGraph center ligand))
    (wellFormed : mol.WellFormed)
    (bondRecordsUnique : mol.BondRecordsUnique)
    (built : branchCanonicalKey? mol center ligand = some key)
    (complete : key.complete = true)
    (rootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
    (hasNoRingDuplicate : P92GraphHasNoRingDuplicate (key.toDeclarativeDigraph mol)) :
    p92AcyclicDigraphReference.Judges source
      (p92ProductionExactDigraphObservation mol center ligand key) := by
  exact ⟨represents,
    p92ProductionExactDigraphObservation_faithful mol center ligand key wellFormed
      bondRecordsUnique built complete rootBond,
    (p92GraphHasNoRingDuplicate_iff_of_iso
      (p92ProductionExactDigraphObservation_graphIso mol key)).1 hasNoRingDuplicate⟩

theorem p92ProductionMultipleBondDigraph_judged
    (source : AuthoritativeChemicalInput)
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (represents : P92CanonicalConstitutionRepresents source center ligand
      (mol.canonicalHierarchyMoleculeGraph center ligand))
    (wellFormed : mol.WellFormed)
    (bondRecordsUnique : mol.BondRecordsUnique)
    (built : branchCanonicalKey? mol center ligand = some key)
    (complete : key.complete = true)
    (rootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
    (hasMultipleBondDuplicate :
      P92GraphHasMultipleBondDuplicate (key.toDeclarativeDigraph mol)) :
    p92MultipleBondDigraphReference.Judges source
      (p92ProductionExactDigraphObservation mol center ligand key) := by
  exact ⟨represents,
    p92ProductionExactDigraphObservation_faithful mol center ligand key wellFormed
      bondRecordsUnique built complete rootBond,
    (p92GraphHasMultipleBondDuplicate_iff_of_iso
      (p92ProductionExactDigraphObservation_graphIso mol key)).1 hasMultipleBondDuplicate⟩

theorem p92ProductionCyclicDigraph_judged
    (source : AuthoritativeChemicalInput)
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (represents : P92CanonicalConstitutionRepresents source center ligand
      (mol.canonicalHierarchyMoleculeGraph center ligand))
    (wellFormed : mol.WellFormed)
    (bondRecordsUnique : mol.BondRecordsUnique)
    (built : branchCanonicalKey? mol center ligand = some key)
    (complete : key.complete = true)
    (rootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
    (hasRingDuplicate : P92GraphHasRingDuplicate (key.toDeclarativeDigraph mol)) :
    p92CyclicDigraphReference.Judges source
      (p92ProductionExactDigraphObservation mol center ligand key) := by
  exact ⟨represents,
    p92ProductionExactDigraphObservation_faithful mol center ligand key wellFormed
      bondRecordsUnique built complete rootBond,
    (p92GraphHasRingDuplicate_iff_of_iso
      (p92ProductionExactDigraphObservation_graphIso mol key)).1 hasRingDuplicate⟩

end

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92GraphHasMultipleBondDuplicate_iff_of_iso
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92GraphHasRingDuplicate_iff_of_iso
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92GraphHasNoRingDuplicate_iff_of_iso
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.P92ExactDigraphProductionReferenceAgreement.ofFaithful
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92ProductionExactDigraphObservation_faithful
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.branchCanonicalKey?_p92ExactDigraph_refines
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92ProductionAcyclicDigraph_judged
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92ProductionMultipleBondDigraph_judged
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92ProductionCyclicDigraph_judged
