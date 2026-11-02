import TetraStereo.UniversalProof.NextFrontier.FramedOccurrenceDerivations

set_option autoImplicit false




namespace TetraStereo.OneCenter.FramedOrdinaryConformance

open RawMolecule

variable {mol : RawMolecule}

/-- Full output fields follow the maintained ordinary fact formula; actual profile creation and
primitive ranking/adjacency derivations reconstruct the whole executable result. -/
structure OrdinaryFactCertificateComplete (authoritative : Bool) (aux : OccurrenceAuxState)
    (fuel : Nat) (node : CanonicalBranchNode) (fact : OccurrenceAuxFact) where
  profile : FrameRuntime.Profile
  profile_eq : FrameRuntime.profile? mol node = some profile
  spec : AtomSpec
  parity : TetrahedralInputParity
  roots : List CanonicalRerootCursor
  sorted : List CanonicalRerootCursor × Nat
  positions : List Nat
  compared : List (OccurrenceComparedPair mol aux fuel)
  atom_spec : mol.atomAt? node.atom = some spec
  tetrahedral : spec.tetrahedral? = some parity
  frame : occurrenceLigandFrame? mol node = some roots
  ranking : FrameSortOccurrencesDerivation (mol := mol) profile authoritative aux fuel roots sorted
  positions_eq :
    (sorted.1.mapM fun cursor =>
      ((mol.ligandsWithLonePair node.atom).zipIdx.find?
        fun entry => entry.1 == cursor.node.atom).map Prod.snd) = some positions
  comparisons : FrameAdjacentComparisonsDerivation (mol := mol) profile authoritative aux fuel
    sorted.1 compared
  strict : (compared.map fun comparison => comparison.decision).all
    (fun decision => decision.ordering != Ordering.eq) = true
  fact_eq : fact =
    { key := canonicalOccurrenceKey node
      atom := node.atom
      descriptor := RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven positions)
      uppercase :=
        ((compared.map fun comparison => comparison.decision).filter
          fun decision => decision.pseudo).length % 2 == 0
      priorityPositions := positions }

/-- The full fact equation is a consequence of actual primitives and literal fact assembly. -/
theorem OrdinaryFactCertificateComplete.production_eq {authoritative : Bool}
    {aux : OccurrenceAuxState} {fuel : Nat} {node : CanonicalBranchNode} {fact : OccurrenceAuxFact}
    (certificate : OrdinaryFactCertificateComplete (mol := mol) authoritative aux fuel node fact) :
    FramedCompleteRuntime.occurrenceFactComplete? mol authoritative fuel aux node = some fact := by
  unfold FramedCompleteRuntime.occurrenceFactComplete?
  dsimp only [Bind.bind, Option.bind]
  simp only [certificate.profile_eq,
    certificate.atom_spec, certificate.tetrahedral, certificate.frame,
    certificate.ranking.production_eq, certificate.positions_eq,
    certificate.comparisons.production_eq, certificate.strict]
  exact congrArg some certificate.fact_eq.symm

/-- Proof-irrelevant form for completeness without choosing a certificate from arbitrary Prop. -/
def OrdinaryFactClausesComplete (authoritative : Bool) (aux : OccurrenceAuxState)
    (fuel : Nat) (node : CanonicalBranchNode) (fact : OccurrenceAuxFact) : Prop :=
  Nonempty (OrdinaryFactCertificateComplete (mol := mol) authoritative aux fuel node fact)

theorem OrdinaryFactClausesComplete.production_eq {authoritative : Bool}
    {aux : OccurrenceAuxState} {fuel : Nat} {node : CanonicalBranchNode} {fact : OccurrenceAuxFact}
    (clauses : OrdinaryFactClausesComplete (mol := mol) authoritative aux fuel node fact) :
    FramedCompleteRuntime.occurrenceFactComplete? mol authoritative fuel aux node = some fact := by
  rcases clauses with ⟨certificate⟩
  exact certificate.production_eq

/-- Successful actual evaluation yields a certificate of each observed primitive. The success
premise is used only for this converse; it is not part of the primary certificate definition. -/
theorem ordinaryFactClausesComplete_of_production {authoritative : Bool}
    {aux : OccurrenceAuxState} {fuel : Nat} {node : CanonicalBranchNode} {fact : OccurrenceAuxFact}
    (computed : FramedCompleteRuntime.occurrenceFactComplete? mol authoritative fuel aux node =
      some fact) :
    OrdinaryFactClausesComplete (mol := mol) authoritative aux fuel node fact := by
  unfold FramedCompleteRuntime.occurrenceFactComplete? at computed
  dsimp only [Bind.bind, Option.bind] at computed
  cases profileEq : FrameRuntime.profile? mol node with
  | none => simp [profileEq] at computed
  | some profile =>
      simp only [profileEq] at computed
      cases atomEq : mol.atomAt? node.atom with
      | none => simp [atomEq] at computed
      | some spec =>
          simp only [atomEq] at computed
          cases parityEq : spec.tetrahedral? with
          | none => simp [parityEq] at computed
          | some parity =>
              simp only [parityEq] at computed
              cases frameEq : occurrenceLigandFrame? mol node with
              | none => simp [frameEq] at computed
              | some roots =>
                  simp only [frameEq] at computed
                  cases rankingEq : FramedCompleteRuntime.trackedSortComplete? mol profile
                      authoritative aux fuel roots with
                  | none => simp [rankingEq] at computed
                  | some sorted =>
                      simp only [rankingEq] at computed
                      cases positionsEq : (sorted.1.mapM fun cursor =>
                          ((mol.ligandsWithLonePair node.atom).zipIdx.find?
                            fun entry => entry.1 == cursor.node.atom).map Prod.snd) with
                      | none => simp [positionsEq] at computed
                      | some positions =>
                          simp only [positionsEq] at computed
                          cases comparisonsEq : FramedCompleteRuntime.adjacentComplete? mol profile
                              authoritative aux fuel sorted.1 with
                          | none => simp [comparisonsEq] at computed
                          | some compared =>
                              simp only [comparisonsEq] at computed
                              cases strictEq : (compared.map fun comparison => comparison.decision).all
                                  (fun decision => decision.ordering != Ordering.eq) with
                              | false =>
                                  simp only [strictEq] at computed
                                  simp at computed
                              | true =>
                                  simp only [strictEq] at computed
                                  have factEq : fact =
                                      { key := canonicalOccurrenceKey node
                                        atom := node.atom
                                        descriptor := RawMolecule.descriptorOfParity parity
                                          (RawMolecule.permutationIsEven positions)
                                        uppercase :=
                                          ((compared.map fun comparison => comparison.decision).filter
                                            fun decision => decision.pseudo).length % 2 == 0
                                        priorityPositions := positions } :=
                                    (Option.some.inj computed).symm
                                  exact ⟨
                                    { profile := profile
                                      profile_eq := profileEq
                                      spec := spec
                                      parity := parity
                                      roots := roots
                                      sorted := sorted
                                      positions := positions
                                      compared := compared
                                      atom_spec := atomEq
                                      tetrahedral := parityEq
                                      frame := frameEq
                                      ranking := frameSortOccurrencesDerivation_of_production profile
                                        authoritative aux fuel roots sorted rankingEq
                                      positions_eq := positionsEq
                                      comparisons := frameAdjacentComparisonsDerivation_of_production
                                        profile authoritative aux fuel sorted.1 compared comparisonsEq
                                      strict := strictEq
                                      fact_eq := factEq }⟩

theorem ordinaryFactClausesComplete_iff_production (authoritative : Bool)
    (aux : OccurrenceAuxState) (fuel : Nat) (node : CanonicalBranchNode) (fact : OccurrenceAuxFact) :
    OrdinaryFactClausesComplete (mol := mol) authoritative aux fuel node fact ↔
      FramedCompleteRuntime.occurrenceFactComplete? mol authoritative fuel aux node = some fact :=
  ⟨OrdinaryFactClausesComplete.production_eq, ordinaryFactClausesComplete_of_production⟩

end TetraStereo.OneCenter.FramedOrdinaryConformance
