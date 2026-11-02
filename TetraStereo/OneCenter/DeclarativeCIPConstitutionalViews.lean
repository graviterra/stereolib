import TetraStereo.OneCenter.DeclarativeCIPRule1aExact

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

universe u

/-- Treatment of the distinguished root bond in the expansion view. -/
inductive RootBondTreatment where
  | preserve
  | coordinationSingle
  deriving DecidableEq, Repr

/-- The unordered distinguished root pair of a ligand hierarchy. -/
def IsDistinguishedRootPair {Atom : Type u} (center ligand left right : Atom) : Prop :=
  (left = center ∧ right = ligand) ∨ (left = ligand ∧ right = center)

/-- Independent paired constitutional semantics for CIP.

`resonance` retains the written constitution used by Rule 1a's Kekule ensemble.  `expansion` is the
graph expanded into the rooted ligand digraph.  The exact relationship is data in the declarative
model rather than an implicit convention of any particular production representation. -/
structure ConstitutionalViews (Atom : Type u) [Fintype Atom] [DecidableEq Atom] where
  resonance : MoleculeGraph Atom
  expansion : MoleculeGraph Atom
  center : Atom
  ligand : Atom
  treatment : RootBondTreatment
  atomZ_eq : ∀ atom, expansion.atomZ atom = resonance.atomZ atom
  atomMass_eq : ∀ atom, expansion.atomMass atom = resonance.atomMass atom
  formalCharge_eq : ∀ atom, expansion.formalCharge atom = resonance.formalCharge atom
  bond_eq_of_not_root : ∀ left right,
    ¬ IsDistinguishedRootPair center ligand left right →
      expansion.bond left right = resonance.bond left right
  root_bond_eq : expansion.bond center ligand =
    match treatment with
    | .preserve => resonance.bond center ligand
    | .coordinationSingle => 1
  coordination_original_double : treatment = .coordinationSingle →
    resonance.bond center ligand = 2

end DeclarativeCIP
end OneCenter
end TetraStereo
