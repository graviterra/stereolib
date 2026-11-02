import TetraStereo.OneCenter.DeclarativeCIPConstitutional

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

/-!
# Rule-1a label and canonical-addressing boundaries

This module records two obstructions that constrain an independent Rule-1a and sibling-addressing
semantics.

First, exact atomic-number averages must exclude zero denominators (or totalize them before forming
the semantic value).  Raw cross multiplication with a zero denominator makes rational equality
non-transitive.

Second, a canonical addressing cannot in general be both a single chosen addressing and natural
under every rooted-digraph automorphism.  Transport-invariance of one addressing forces every
automorphism to fix every node.  Symmetric sibling families therefore require an invariant family
of admissible dense addressings, with permutations allowed inside genuine semantic tie classes,
rather than an implementation-independent choice of one representative.
-/

namespace Rule1aRawLabelBoundary

/-- Deliberately unconstrained numerator/denominator data used to expose the zero-denominator
failure.  This is not the proposed independent Rule-1a label type. -/
structure RawLabel where
  numerator : ℕ
  denominator : ℕ

/-- The tempting raw cross-product equality, before imposing denominator positivity. -/
def Ties (left right : RawLabel) : Prop :=
  left.numerator * right.denominator = right.numerator * left.denominator

private def one : RawLabel := ⟨1, 1⟩
private def zeroOverZero : RawLabel := ⟨0, 0⟩
private def two : RawLabel := ⟨2, 1⟩

/-- Zero-over-zero ties every ordinary value under raw cross multiplication, destroying
transitivity of the induced equality relation. -/
theorem rawCrossProductTies_not_transitive :
    ¬ ∀ first second third,
      Ties first second → Ties second third → Ties first third := by
  intro htransitive
  have himpossible := htransitive one zeroOverZero two rfl rfl
  simp [Ties, one, two] at himpossible

end Rule1aRawLabelBoundary

namespace RootedDigraph

universe u

variable {Atom : Type u} {graph : RootedDigraph Atom}

/-- An addressing fixed by transport along an automorphism forces that automorphism to fix every
node.  Consequently, any rooted digraph with a nontrivial automorphism has no single addressing
that is natural under all of its automorphisms. -/
theorem addressing_fixedByAutomorphism_implies_pointwiseFixed
    (addressing : graph.Addressing) (iso : RootedDigraph.Iso graph graph)
    (hfixed : addressing.transport iso = addressing) (node : graph.Node) :
    iso.toEquiv node = node := by
  have haddress :=
    congrArg (fun candidate : graph.Addressing => candidate.address (iso.toEquiv node)) hfixed
  apply addressing.address_injective
  simpa using haddress.symm

/-- A nontrivial rooted-digraph automorphism rules out any addressing fixed by its transport. -/
theorem no_fixed_addressing_of_moved_node
    (iso : RootedDigraph.Iso graph graph) (node : graph.Node)
    (hmoved : iso.toEquiv node ≠ node) :
    ¬ ∃ addressing : graph.Addressing, addressing.transport iso = addressing := by
  rintro ⟨addressing, hfixed⟩
  exact hmoved
    (addressing_fixedByAutomorphism_implies_pointwiseFixed addressing iso hfixed node)

end RootedDigraph

end
end DeclarativeCIP
end OneCenter
end TetraStereo
