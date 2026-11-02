import TetraStereo.OneCenter.DeclarativeCIPConstitutional

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace DeclarativeCIPConstitutional

open OneCenter
open OneCenter.DeclarativeCIP

noncomputable section

/-- A one-node hierarchy used to exercise the declarative rule relations without any executable
hierarchy builder. -/
def singletonGraph {Atom : Type} (label : NodeLabel Atom) : RootedDigraph Atom where
  Node := Unit
  nodeFintype := inferInstance
  root := ()
  child := fun _ _ => False
  label := fun _ => label
  depth := fun _ => 0
  root_depth := rfl
  child_depth := by simp
  reachable := by
    intro node
    have h : node = () := Subsingleton.elim _ _
    subst node
    exact Relation.ReflTransGen.refl

/-- The unique parent-preserving address of a singleton hierarchy. -/
def singletonAddressing {Atom : Type} (label : NodeLabel Atom) :
    (singletonGraph label).Addressing where
  address := fun _ => []
  address_injective := by
    intro first second _
    cases first
    cases second
    rfl
  root_address := rfl
  child_iff := by
    intro parent node
    constructor
    · intro h
      exact h.elim
    · rintro ⟨slot, hslot⟩
      have hlength := congrArg List.length hslot
      simp at hlength

abbrev DemoAtom := Fin 2

def hydrogen : DemoAtom := 0
def carbon : DemoAtom := 1

/-- A minimal atom-label model with `C > H` by Rule 1a. -/
def atomicNumberMolecule : MoleculeGraph DemoAtom where
  atomZ := fun atom => if atom = hydrogen then 1 else 6
  atomMass := fun _ => 0
  bond := fun _ _ => 0
  bond_symm := by simp
  bond_self := by simp

def hydrogenLabel : NodeLabel DemoAtom :=
  ⟨some hydrogen, NodeProvenance.realAtom⟩

def carbonLabel : NodeLabel DemoAtom :=
  ⟨some carbon, NodeProvenance.realAtom⟩

/-- The independent Rule-1a relation derives carbon above hydrogen at the first hierarchy
position. -/
theorem rule1a_carbon_over_hydrogen :
    ConstitutionalHierarchyOutcome atomicNumberMolecule
      ConstitutionalRule.rule1aAtomicNumber
      (singletonGraph carbonLabel) (singletonAddressing carbonLabel)
      (singletonGraph hydrogenLabel) (singletonAddressing hydrogenLabel)
      Ordering.gt := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨some carbonLabel, some hydrogenLabel, ?_, ?_, ?_⟩
    · exact Or.inl ⟨(), rfl, rfl⟩
    · exact Or.inl ⟨(), rfl, rfl⟩
    · exact DescendingNatOutcome.gt (by decide)
  · intro earlier hearlier
    cases earlier <;>
      simp [HierarchyAddressBefore, HierarchyAddressKey, List.cons_lt_cons_iff] at hearlier

/-- A minimal isotope model with equal atomic numbers and mass `2 > 1`. -/
def isotopeMolecule : MoleculeGraph DemoAtom where
  atomZ := fun _ => 1
  atomMass := fun atom => if atom = hydrogen then 1 else 2
  bond := fun _ _ => 0
  bond_symm := by simp
  bond_self := by simp

/-- The independent Rule-2 relation derives the heavier isotope above the lighter isotope. -/
theorem rule2_heavier_isotope :
    ConstitutionalHierarchyOutcome isotopeMolecule
      ConstitutionalRule.rule2AtomicMass
      (singletonGraph carbonLabel) (singletonAddressing carbonLabel)
      (singletonGraph hydrogenLabel) (singletonAddressing hydrogenLabel)
      Ordering.gt := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨some carbonLabel, some hydrogenLabel, ?_, ?_, ?_⟩
    · exact Or.inl ⟨(), rfl, rfl⟩
    · exact Or.inl ⟨(), rfl, rfl⟩
    · exact DescendingNatOutcome.gt (by decide)
  · intro earlier hearlier
    cases earlier <;>
      simp [HierarchyAddressBefore, HierarchyAddressKey, List.cons_lt_cons_iff] at hearlier

def nearDuplicateLabel : NodeLabel DemoAtom :=
  ⟨some carbon, NodeProvenance.ringDuplicate 1⟩

def farDuplicateLabel : NodeLabel DemoAtom :=
  ⟨some carbon, NodeProvenance.ringDuplicate 3⟩

def rootDuplicateLabel : NodeLabel DemoAtom :=
  ⟨some carbon, NodeProvenance.ringDuplicate 0⟩

/-- The independent Rule-1b relation gives priority to the closer duplicate root. -/
theorem rule1b_closer_duplicate_root :
    ConstitutionalHierarchyOutcome atomicNumberMolecule
      ConstitutionalRule.rule1bDuplicateNodeProximity
      (singletonGraph nearDuplicateLabel) (singletonAddressing nearDuplicateLabel)
      (singletonGraph farDuplicateLabel) (singletonAddressing farDuplicateLabel)
      Ordering.gt := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨some nearDuplicateLabel, some farDuplicateLabel, ?_, ?_, ?_⟩
    · exact Or.inl ⟨(), rfl, rfl⟩
    · exact Or.inl ⟨(), rfl, rfl⟩
    · exact Rule1bDistanceOutcome.gt (by decide)
  · intro earlier hearlier
    cases earlier <;>
      simp [HierarchyAddressBefore, HierarchyAddressKey, List.cons_lt_cons_iff] at hearlier

/-- Regression for the former nontransitive missing-distance semantics: a real root has total
Rule-1b distance one, so a distance-zero duplicate strictly outranks it rather than tying. -/
theorem rule1b_duplicate_zero_over_real_root :
    ConstitutionalNodeOutcome atomicNumberMolecule
      ConstitutionalRule.rule1bDuplicateNodeProximity []
      (some rootDuplicateLabel) (some carbonLabel) Ordering.gt := by
  exact Rule1bDistanceOutcome.gt (by decide)

/-- The repaired total observation makes the formerly broken three-label chain transitive. -/
theorem rule1b_root_chain_transitive :
    ConstitutionalNodeOutcome atomicNumberMolecule
      ConstitutionalRule.rule1bDuplicateNodeProximity []
      (some rootDuplicateLabel) (some farDuplicateLabel) Ordering.gt := by
  have hfirst : Rule1bDistanceOutcome
      (nodeRule1bRootDistance [] (some rootDuplicateLabel))
      (nodeRule1bRootDistance [] (some carbonLabel)) Ordering.gt :=
    Rule1bDistanceOutcome.gt (by decide)
  have hsecond : Rule1bDistanceOutcome
      (nodeRule1bRootDistance [] (some carbonLabel))
      (nodeRule1bRootDistance [] (some farDuplicateLabel)) Ordering.gt :=
    Rule1bDistanceOutcome.gt (by decide)
  exact Rule1bDistanceOutcome.gt_trans hfirst hsecond

end
end DeclarativeCIPConstitutional
end Examples
end TetraStereo
