import TetraStereo.OneCenter.AuthoritativeLocalizedRule1bConformance
import TetraStereo.OneCenter.IUPACP92SemanticGraphFaithfulExpansion

set_option autoImplicit false

namespace TetraStereo.OneCenter

open scoped List

/-!
# Faithfulness of the runtime official source tree

This module closes the enumeration gap between the kernel-executable official child enumerator
`executableOfficialCIPChildren` and the graph-native semantic enumerator
`semanticOfficialCIPChildren`.

The first result is a generic, format-neutral transfer principle: two child enumerators that are
pointwise permutation-equivalent generate exactly the same recursive `OfficialCIPSourceTree`.
Duplicate equal source nodes are retained with their multiplicities, so repeated atoms, multiple
bonds and ring closures are covered without any injectivity assumption.

The second result composes that transfer with the existing runtime/semantic permutation theorem and
packages the *very same* tree into `MoleculeGraph.SemanticOfficialHierarchy`.  Consequently an
actual runtime-generated source tree whose root is a canonical center/ligand edge is already a
`FaithfulExactExpansion`; no faithful-expansion premise, occurrence count, duplicate-distance input
or supplied hierarchy witness is assumed.

The exported key theorem attaches that tree to the exact rule-major key it was compiled from, so
the retained `SourceLayersAligned key.sourceNodes tree` link is the original one produced by
`buildExecutableExactOfficialRuleMajorKey_generatedSourceTree`, not an arbitrary witness.

Scope: this is structural expansion faithfulness of the actual executable tree only.  It makes no
absolute-priority, descriptor-construction or universal chemical-correctness claim, and it does not
identify graph automorphisms with occurrence isomorphisms.
-/

namespace OfficialCIPSourceTree

variable {V : Type*}

/- Pointwise permutation-equivalent child enumerators generate exactly the same recursive source
tree.  The proof is the structural mutual induction over the tree and its sibling forest; sibling
multiplicities are preserved because permutation only reorders the enumerated list. -/
mutual
  /-- Pointwise permutation-equivalent child enumerators generate the same recursive source tree. -/
  theorem GeneratedBy.congr_enumerator
      {enumerate₁ enumerate₂ : OfficialCIPNode V → List (OfficialCIPNode V)}
      (pointwise : ∀ node : OfficialCIPNode V,
        (enumerate₁ node).Perm (enumerate₂ node)) :
      ∀ tree : OfficialCIPSourceTree V,
        tree.GeneratedBy enumerate₁ → tree.GeneratedBy enumerate₂
    | .node sourceNode subtrees, generated =>
        ⟨generated.1.trans (pointwise sourceNode),
          ForestGeneratedBy.congr_enumerator pointwise subtrees generated.2⟩

  theorem ForestGeneratedBy.congr_enumerator
      {enumerate₁ enumerate₂ : OfficialCIPNode V → List (OfficialCIPNode V)}
      (pointwise : ∀ node : OfficialCIPNode V,
        (enumerate₁ node).Perm (enumerate₂ node)) :
      ∀ trees : List (OfficialCIPSourceTree V),
        ForestGeneratedBy enumerate₁ trees → ForestGeneratedBy enumerate₂ trees
    | [], _ => trivial
    | tree :: trees, generated =>
        ⟨GeneratedBy.congr_enumerator pointwise tree generated.1,
          ForestGeneratedBy.congr_enumerator pointwise trees generated.2⟩
end

end OfficialCIPSourceTree

namespace CertifiedLocalizedCIPInput

/-- The runtime child enumerator and the graph-native semantic child enumerator are pointwise
permutation-equivalent: both enumerate exactly the same official child multiset. -/
theorem executableOfficialCIPChildren_perm_semanticOfficialCIPChildren
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom) :
    (input.executableOfficialCIPChildren node).Perm
      (input.moleculeGraph.semanticOfficialCIPChildren node) :=
  (input.executableOfficialCIPChildren_perm_officialCIPChildren node).trans
    (input.moleculeGraph.semanticOfficialCIPChildren_perm_officialCIPChildren node).symm




theorem generatedExecutableSourceTree_semanticGenerated
    (input : CertifiedLocalizedCIPInput)
    (tree : OfficialCIPSourceTree input.Atom)
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren) :
    tree.GeneratedBy input.moleculeGraph.semanticOfficialCIPChildren :=
  OfficialCIPSourceTree.GeneratedBy.congr_enumerator
    (fun node => input.executableOfficialCIPChildren_perm_semanticOfficialCIPChildren node)
    tree generated

/-- A runtime-generated source tree rooted at a canonically chosen center/ligand edge is a faithful
exact declarative expansion of the actual molecular graph.  The same tree is packaged unchanged into
`SemanticOfficialHierarchy`; the only additional premise is the actual root adjacency. -/
theorem generatedExecutableSourceTree_faithfulExactExpansion
    (input : CertifiedLocalizedCIPInput)
    (tree : OfficialCIPSourceTree input.Atom)
    (center ligand : input.Atom)
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (rootBond : input.moleculeGraph.Adj center ligand) :
    DeclarativeCIP.RootedDigraph.FaithfulExactExpansion
      input.moleculeGraph center ligand tree.toDeclarativeDigraph := by
  let hierarchy : MoleculeGraph.SemanticOfficialHierarchy input.moleculeGraph center ligand :=
    { tree := tree
      generated := input.generatedExecutableSourceTree_semanticGenerated tree generated
      rootSource := root }
  exact hierarchy.faithfulExactExpansion rootBond

/-- The exact rule-major key build exposes a recursive source tree that is simultaneously aligned
with the key's original `sourceNodes`, rooted at the canonical center/ligand root, and a faithful
exact expansion of the molecular graph.  Both witnesses are the *same* tree produced by
`buildExecutableExactOfficialRuleMajorKey_generatedSourceTree`. -/
theorem buildExecutableExactOfficialRuleMajorKey_faithfulSourceTree
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (key : ExactOfficialRuleMajorKey input.Atom)
    (computed : input.buildExecutableExactOfficialRuleMajorKey
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index)) = some key) :
    ∃ tree : OfficialCIPSourceTree input.Atom,
      OfficialCIPSourceTree.SourceLayersAligned key.sourceNodes tree ∧
        tree.source = OfficialCIPNode.rootFromEdge center.1
          (input.canonicalLigandAtom center index) ∧
        DeclarativeCIP.RootedDigraph.FaithfulExactExpansion input.moleculeGraph center.1
          (input.canonicalLigandAtom center index) tree.toDeclarativeDigraph := by
  obtain ⟨tree, aligned, generated, root⟩ :=
    input.buildExecutableExactOfficialRuleMajorKey_generatedSourceTree center index key computed
  exact ⟨tree, aligned, root,
    input.generatedExecutableSourceTree_faithfulExactExpansion tree center.1
      (input.canonicalLigandAtom center index) generated root
      (input.canonicalLigandAtom_adj center index)⟩

/-- Default-domain existence form: at the proved finite-atom fuel bound the exact key build succeeds
without any supplied success premise, and the resulting key carries a source tree that is aligned
with its original occurrences and is a faithful exact expansion. -/
theorem buildExecutableExactOfficialRuleMajorKey_faithfulSourceTree_default
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    ∃ key : ExactOfficialRuleMajorKey input.Atom,
      input.buildExecutableExactOfficialRuleMajorKey
        (input.certified.input.molecule.atomCount + 1)
        (OfficialCIPNode.rootFromEdge center.1
          (input.canonicalLigandAtom center index)) = some key ∧
      ∃ tree : OfficialCIPSourceTree input.Atom,
        OfficialCIPSourceTree.SourceLayersAligned key.sourceNodes tree ∧
          tree.source = OfficialCIPNode.rootFromEdge center.1
            (input.canonicalLigandAtom center index) ∧
          DeclarativeCIP.RootedDigraph.FaithfulExactExpansion input.moleculeGraph center.1
            (input.canonicalLigandAtom center index) tree.toDeclarativeDigraph := by
  obtain ⟨key, computed, _complete⟩ :=
    input.buildExecutableExactOfficialRuleMajorKey_complete_default center index
  obtain ⟨tree, aligned, root, faithful⟩ :=
    input.buildExecutableExactOfficialRuleMajorKey_faithfulSourceTree center index key computed
  exact ⟨key, computed, tree, aligned, root, faithful⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.OfficialCIPSourceTree.GeneratedBy.congr_enumerator
assert_kernel_only TetraStereo.OneCenter.OfficialCIPSourceTree.ForestGeneratedBy.congr_enumerator
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableOfficialCIPChildren_perm_semanticOfficialCIPChildren
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.generatedExecutableSourceTree_semanticGenerated
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.generatedExecutableSourceTree_faithfulExactExpansion
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildExecutableExactOfficialRuleMajorKey_faithfulSourceTree
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildExecutableExactOfficialRuleMajorKey_faithfulSourceTree_default
