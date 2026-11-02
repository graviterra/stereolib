import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalTreeAcyclic

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeChronologicalTreeSimplePathUniqueness
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeGeneratedRealPaths
open TetraStereo.UniversalProof.NativeChronologicalTreeAcyclic

/-- Every actual bounded, bonded vertex list with endpoints realizes a graph walk
    with exactly that support. No graph reachability or desired walk is supplied. -/
theorem raw_list_realizes_walk {mol : RawMolecule} (vertices : List Nat)
    (start finish : Nat) (bonded : RawBondedPath mol vertices)
    (head : vertices.head? = some start) (last : vertices.getLast? = some finish)
    (bounds : ∀ atom ∈ vertices, atom < mol.atomCount) :
    ∃ walk : (physicalGraph mol).Walk start finish, walk.support = vertices := by
  induction vertices generalizing start with
  | nil => simp at head
  | cons a tail ih =>
      have same : a = start := by simpa only [List.head?_cons, Option.some.injEq] using head
      subst start
      cases tail with
      | nil =>
          have same : a = finish := by simpa using last
          subst finish
          exact ⟨.nil, rfl⟩
      | cons b rest =>
          have edges : 0 < mol.bondOrder a b ∧ RawBondedPath mol (b :: rest) := by
            simpa only [RawBondedPath, List.isChain_cons_cons] using bonded
          have tailLast : (b :: rest).getLast? = some finish := by
            simpa only [List.getLast?_cons_cons] using last
          have tailBounds : ∀ atom ∈ b :: rest, atom < mol.atomCount := by
            intro atom member
            exact bounds atom (List.mem_cons_of_mem a member)
          obtain ⟨tailWalk, support⟩ := ih b edges.2 rfl tailLast tailBounds
          have adjacent : (physicalGraph mol).Adj a b :=
            ⟨bounds a (List.mem_cons_self), tailBounds b (List.mem_cons_self), edges.1⟩
          refine ⟨.cons adjacent tailWalk, ?_⟩
          change a :: tailWalk.support = a :: b :: rest
          rw [support]

/-- Nodup raw supported paths become actual graph paths, with identical vertex lists. -/
theorem raw_supported_realizes_path {mol : RawMolecule} {start finish : Nat}
    {vertices : List Nat} (supported : RawSupportedPath mol start finish vertices) :
    ∃ path : (physicalGraph mol).Path start finish, path.val.support = vertices := by
  obtain ⟨walk, support⟩ := raw_list_realizes_walk vertices start finish supported.2.1
    supported.2.2.1 supported.2.2.2.1 supported.2.2.2.2
  have simple : walk.IsPath := (walk.isPath_def).mpr (support.symm ▸ supported.1)
  exact ⟨⟨walk, simple⟩, support⟩

/-- The raw chronological inventory internally entails the existing full raw-path uniqueness ABI.
    Global acyclicity is derived by the dependency theorem, never supplied as a caller field. -/
theorem chronological_uniqueRawSimplePaths {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) : UniqueRawSimplePaths mol := by
  intro start finish p q pSupported qSupported
  obtain ⟨pPath, pSupport⟩ := raw_supported_realizes_path pSupported
  obtain ⟨qPath, qSupport⟩ := raw_supported_realizes_path qSupported
  have same := (chronological_physicalGraph_acyclic tree).path_unique pPath qPath
  have supportSame := congrArg (fun path : (physicalGraph mol).Path start finish => path.val.support) same
  exact pSupport.symm.trans (supportSame.trans qSupport)

end TetraStereo.UniversalProof.NativeChronologicalTreeSimplePathUniqueness
