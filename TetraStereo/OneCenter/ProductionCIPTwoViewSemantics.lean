import TetraStereo.OneCenter.DeclarativeCIPConstitutionalViews
import TetraStereo.OneCenter.ProductionCIPRule1aCertifiedGlobal

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

namespace RawMolecule

/-- The production molecule's two constitutional views, related by the precise root-only
normalization contract. -/
def constitutionalViews (mol : RawMolecule)
    (center ligand : Fin mol.atomCount) :
    ConstitutionalViews (Fin mol.atomCount) where
  resonance := mol.toMoleculeGraph
  expansion := mol.canonicalHierarchyMoleculeGraph center ligand
  center := center
  ligand := ligand
  treatment := if mol.isTrigonalPyramidalOxidoRootEdge center ligand then
      .coordinationSingle else .preserve
  atomZ_eq := fun _ => rfl
  atomMass_eq := fun _ => rfl
  formalCharge_eq := fun _ => rfl
  bond_eq_of_not_root := by
    intro left right hnotRoot
    apply mol.canonicalHierarchyBond_eq_bondOrder_of_not_rootPair
    intro hroot
    apply hnotRoot
    rcases hroot with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · exact Or.inl ⟨Fin.ext hleft, Fin.ext hright⟩
    · exact Or.inr ⟨Fin.ext hleft, Fin.ext hright⟩
  root_bond_eq := by
    change mol.canonicalHierarchyBond center ligand center ligand =
      match (if mol.isTrigonalPyramidalOxidoRootEdge center ligand then
        RootBondTreatment.coordinationSingle else RootBondTreatment.preserve) with
      | .preserve => mol.bondOrder center ligand
      | .coordinationSingle => 1
    by_cases heq : center = ligand
    · subst ligand
      have hnotOxido : mol.isTrigonalPyramidalOxidoRootEdge center center = false := by
        unfold isTrigonalPyramidalOxidoRootEdge
        cases hspec : mol.atomAt? center.val with
        | none => simp
        | some spec =>
            simp only
            by_cases hp : spec.element = Element.P
            · simp [hp]
            · by_cases hs : spec.element = Element.S
              · simp [hs]
              · simp [hp, hs]
      simp [hnotOxido, canonicalHierarchyBond, mol.bondOrder_self]
    · by_cases hoxido : mol.isTrigonalPyramidalOxidoRootEdge center ligand = true
      · have hvalNe : center.val ≠ ligand.val := fun h => heq (Fin.ext h)
        simp [hoxido, canonicalHierarchyBond, hvalNe, IsRootPair]
      · have hoxidoFalse : mol.isTrigonalPyramidalOxidoRootEdge center ligand = false :=
          Bool.eq_false_of_not_eq_true hoxido
        have hvalNe : center.val ≠ ligand.val := fun h => heq (Fin.ext h)
        simp [hoxidoFalse, canonicalHierarchyBond, hvalNe, IsRootPair]
  coordination_original_double := by
    intro htreatment
    change (if mol.isTrigonalPyramidalOxidoRootEdge center ligand then
      RootBondTreatment.coordinationSingle else RootBondTreatment.preserve) =
        RootBondTreatment.coordinationSingle at htreatment
    have hoxido : mol.isTrigonalPyramidalOxidoRootEdge center ligand = true := by
      by_contra hnot
      have hfalse : mol.isTrigonalPyramidalOxidoRootEdge center ligand = false :=
        Bool.eq_false_of_not_eq_true hnot
      simp [hfalse] at htreatment
    unfold isTrigonalPyramidalOxidoRootEdge at hoxido
    cases hcenter : mol.atomAt? center.val with
    | none => simp [hcenter] at hoxido
    | some centerSpec =>
        cases hligand : mol.atomAt? ligand.val with
        | none => simp [hcenter, hligand] at hoxido
        | some ligandSpec =>
            simp only [hcenter, hligand, Bool.and_eq_true, Bool.or_eq_true,
              beq_iff_eq] at hoxido
            change mol.bondOrder center ligand = 2
            exact hoxido.2

@[simp] theorem constitutionalViews_resonance (mol : RawMolecule)
    (center ligand : Fin mol.atomCount) :
    (mol.constitutionalViews center ligand).resonance = mol.toMoleculeGraph :=
  rfl

@[simp] theorem constitutionalViews_expansion (mol : RawMolecule)
    (center ligand : Fin mol.atomCount) :
    (mol.constitutionalViews center ligand).expansion =
      mol.canonicalHierarchyMoleculeGraph center ligand :=
  rfl

/-- Rule-1a correctness at a realized hierarchy node, parameterized explicitly by the resonance
view rather than recovering it implicitly from `RawMolecule`. -/
def CanonicalBranchKey.RealizedRule1aObservationCorrectAtView
    (mol : RawMolecule) (resonance : MoleculeGraph (Fin mol.atomCount))
    (key : CanonicalBranchKey) (node : key.HierarchyNode)
    (source : CanonicalBranchNode) : Prop :=
  key.sourceNodeAtAddress? node.val = some source ∧
    ∃ label, mol.canonicalRule1aLabel? source = some label ∧
      label.toExactAtomicNumber.value =
        (exactRule1aNodeObservation resonance (key.toDeclarativeDigraph mol)
          (key.declarativeAddressing mol) node).value

/-- A complete production hierarchy certified against one explicit paired constitutional model. -/
structure PairedViewFaithfulExactRule1a
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey) : Prop where
  faithfulExpansion : RootedDigraph.FaithfulExactExpansion
    (mol.constitutionalViews center ligand).expansion center ligand
    (key.toDeclarativeDigraph mol)
  rule1aObservations : ∀ (node : key.HierarchyNode) (source : CanonicalBranchNode),
    key.sourceNodeAtAddress? node.val = some source →
      key.RealizedRule1aObservationCorrectAtView mol
        (mol.constitutionalViews center ligand).resonance node source

/-- The final production theorem restated through the named paired-view semantics.  Its type now
records that hierarchy expansion uses the root-normalized view while Rule 1a uses the written
resonance view. -/
theorem branchCanonicalKey?_certifiedPairedViewFaithfulExactRule1a
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true)
    (hrootBond : (mol.constitutionalViews center ligand).expansion.Adj center ligand) :
    PairedViewFaithfulExactRule1a mol center ligand key := by
  have hcertified :=
    mol.branchCanonicalKey?_certifiedFaithfulExactExpansion_and_rule1aObservationCorrect
      center ligand key hwellFormed hunique hkey hcomplete hrootBond
  refine ⟨hcertified.1, ?_⟩
  intro node source hsource
  have hcorrect := hcertified.2 node source hsource
  exact hcorrect

end RawMolecule

end
end OneCenter
end TetraStereo
