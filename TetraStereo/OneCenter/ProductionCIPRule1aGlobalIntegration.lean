import TetraStereo.OneCenter.ProductionCIPRule1aGeneralSoundness

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

namespace RawMolecule

/-!
# Global Rule-1a soundness assembly

The maximum-matching and nonlocalized branches are proved independently.  This module exposes the
only remaining dispatcher obligation as a named proposition: correctness when
`simpleMancudeCycle?` returns a cycle.  It then composes that obligation with the proved branches
to obtain `MancudeRule1aSound` and the production faithful-expansion/Rule-1a theorem.

No theorem in this module asserts the simple-cycle obligation without a proof of it.
-/

/-- Exact pointwise soundness obligation for precisely the branch selected by a successful
`simpleMancudeCycle?` call.  Keeping the detected cycle and alternate atom explicit makes this
predicate directly dischargeable by a future structural theorem about the detector. -/
def MancudeRule1aSimpleCycleBranchSound (mol : RawMolecule) : Prop :=
  ∀ (attached duplicated : Fin mol.atomCount) (cycle : List ℕ) (alternate : ℕ)
      (label : CIPAtomicLabel),
    containsUndirectedEdge mol.localizedMancudeEdges attached.val duplicated.val = true →
    mol.simpleMancudeCycle? attached.val duplicated.val = some (cycle, alternate) →
    mol.mancudeRule1aLabel? attached.val duplicated.val = some label →
      label.toExactAtomicNumber.value =
        (mol.toMoleculeGraph.exactRule1aMultipleBond attached duplicated).value

/-- The nonlocalized theorem, the proved general-branch theorem, and the explicit simple-cycle
obligation exhaust all cases of the production dispatcher. -/
theorem mancudeRule1aSound_of_general_and_simpleCycle
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique)
    (hgeneral : mol.MancudeRule1aGeneralBranchSound)
    (hsimple : mol.MancudeRule1aSimpleCycleBranchSound) :
    mol.MancudeRule1aSound := by
  intro attached duplicated label hlabel
  by_cases hraw : containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true
  · cases hcycle : mol.simpleMancudeCycle? attached.val duplicated.val with
    | none => exact hgeneral attached duplicated label hraw hcycle hlabel
    | some cycleData =>
        rcases cycleData with ⟨cycle, alternate⟩
        exact hsimple attached duplicated cycle alternate label hraw hcycle hlabel
  · have hrawFalse : containsUndirectedEdge mol.localizedMancudeEdges
        attached.val duplicated.val = false :=
      Bool.eq_false_of_not_eq_true hraw
    have hsemantic :
        ¬ mol.toMoleculeGraph.LocalizedMancudeEdge attached duplicated := by
      intro hlocalized
      apply hraw
      exact (mol.containsUndirectedEdge_localizedMancudeEdges_iff
        hwellFormed hunique attached duplicated).2 hlocalized
    exact mol.mancudeRule1aLabel?_sound_of_not_localized attached duplicated
      hrawFalse hsemantic label hlabel

/-- After the simple-cycle obligation is discharged, well-formedness and unique bond records
supply all other branches and hence unconditional global production Rule-1a soundness. -/
theorem mancudeRule1aSound_of_simpleCycleBranchSound
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique)
    (hsimple : mol.MancudeRule1aSimpleCycleBranchSound) :
    mol.MancudeRule1aSound := by
  exact mol.mancudeRule1aSound_of_general_and_simpleCycle hwellFormed hunique
    (mol.mancudeRule1aGeneralBranchSound hwellFormed hunique) hsimple

/-- Final production integration: once the isolated simple-cycle predicate is proved, every
successful complete hierarchy is simultaneously a faithful exact declarative expansion and
Rule-1a-correct at every realized node.  No separate global or hierarchy-local Mancude soundness
hypothesis remains. -/
theorem branchCanonicalKey?_faithfulExactExpansion_and_rule1aObservationCorrect_of_simpleCycle
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true)
    (hrootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
    (hsimple : mol.MancudeRule1aSimpleCycleBranchSound) :
    RootedDigraph.FaithfulExactExpansion
        (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
        (key.toDeclarativeDigraph mol) ∧
      ∀ (node : key.HierarchyNode) (source : CanonicalBranchNode),
        key.sourceNodeAtAddress? node.val = some source →
          key.RealizedRule1aObservationCorrectAt mol node source := by
  exact mol.branchCanonicalKey?_faithfulExactExpansion_and_rule1aObservationCorrect_of_global
    center ligand key hwellFormed hunique hkey hcomplete hrootBond
    (mol.mancudeRule1aSound_of_simpleCycleBranchSound hwellFormed hunique hsimple)

end RawMolecule

end
end OneCenter
end TetraStereo
