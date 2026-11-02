import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-! Pure production carrier-frame disjointness, extracted unchanged from the semantic
applicability module. No runtime/declarative occurrence-alignment theorem is imported.
SOURCE-only successor: no kernel acceptance or scientific approval is claimed here. -/

/-- Every object emitted by the parser's extended-tetrahedral carrier recognizer has exactly its
two cumulene-axis neighbors in the written-neighbor frame.  This follows from the successful
constructor branch itself and requires no external chemical assumption. -/
theorem RawMolecule.writtenNeighbors_length_eq_two_of_mem_extendedTetrahedralParityCarriers
    (molecule : RawMolecule) (carrier : ExtendedTetrahedralParityCarrier)
    (present : carrier ∈ molecule.extendedTetrahedralParityCarriers) :
    (molecule.writtenNeighbors carrier.parityCarrier).length = 2 := by
  rw [RawMolecule.extendedTetrahedralParityCarriers, List.mem_filterMap] at present
  rcases present with ⟨chain, _chainPresent, computed⟩
  cases oddObserved : chain.length % 2 != 1 with
  | true => simp [oddObserved] at computed
  | false =>
      cases atomObserved : molecule.atomAt? (chain[chain.length / 2]?.getD 0) with
      | none =>
          simp [oddObserved, atomObserved] at computed
      | some spec =>
          cases parityObserved : spec.tetrahedral? with
          | none =>
              simp [oddObserved, atomObserved, parityObserved] at computed
          | some parity =>
              cases neighborsObserved :
                  molecule.writtenNeighbors (chain[chain.length / 2]?.getD 0) with
              | nil =>
                  simp [oddObserved, atomObserved,
                    neighborsObserved] at computed
              | cons writtenFirst rest =>
                  cases rest with
                  | nil =>
                      simp [oddObserved, atomObserved,
                        neighborsObserved] at computed
                  | cons writtenSecond tail =>
                      cases tail with
                      | nil =>
                          have neighborsObservedGetD :
                              molecule.writtenNeighbors
                                  (chain.getD (chain.length / 2) 0) =
                                [writtenFirst, writtenSecond] := by
                            simpa [List.getD] using neighborsObserved
                          simp only [oddObserved, Bool.false_eq_true, if_false,
                            neighborsObservedGetD] at computed
                          split at computed
                          · simp at computed
                          · have parityCarrierEqual :
                                carrier.parityCarrier =
                                  chain[chain.length / 2]?.getD 0 := by
                              have projected := congrArg
                                (fun result : Option ExtendedTetrahedralParityCarrier =>
                                  result.map (fun item => item.parityCarrier)) computed
                              simpa [atomObserved, parityObserved] using projected.symm
                            rw [parityCarrierEqual]
                            simpa [List.getD] using
                              congrArg List.length neighborsObservedGetD
                      | cons third tail =>
                          simp [oddObserved, atomObserved,
                            neighborsObserved] at computed

/-- A four-neighbor parser atom cannot simultaneously be an extended-tetrahedral parity carrier.
The two recognizers are therefore disjoint by construction, rather than by an unproved chemistry
side condition. -/
theorem RawMolecule.isExtendedTetrahedralParityCarrier_eq_false_of_writtenNeighbors_length_eq_four
    (molecule : RawMolecule) (atom : ℕ)
    (four : (molecule.writtenNeighbors atom).length = 4) :
    molecule.isExtendedTetrahedralParityCarrier atom = false := by
  cases observed : molecule.isExtendedTetrahedralParityCarrier atom with
  | false => rfl
  | true =>
      have existsCarrier : ∃ carrier ∈ molecule.extendedTetrahedralParityCarriers,
          (carrier.parityCarrier == atom) = true := by
        have anyTrue : molecule.extendedTetrahedralParityCarriers.any
            (fun carrier => carrier.parityCarrier == atom) = true := by
          simpa [RawMolecule.isExtendedTetrahedralParityCarrier] using observed
        exact List.any_eq_true.mp anyTrue
      rcases existsCarrier with ⟨carrier, present, carrierAtom⟩
      have atomEqual : carrier.parityCarrier = atom := by
        simpa using carrierAtom
      have two :=
        molecule.writtenNeighbors_length_eq_two_of_mem_extendedTetrahedralParityCarriers
          carrier present
      rw [atomEqual] at two
      omega

end TetraStereo.OneCenter
