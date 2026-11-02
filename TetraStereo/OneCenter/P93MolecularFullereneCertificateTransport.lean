import TetraStereo.OneCenter.P93MolecularFullereneFiniteFaceCertificate

set_option autoImplicit false

/-!
# Transporting a certified fullerene cage into a derivative molecule

Substitution changes only atoms and bonds outside a numbered fullerene carrier and the bonds from
that carrier to the addends.  The complete cage certificate therefore should not be rebuilt for
every derivative.  This file proves that principle extensionally: agreement on carrier atom
labels, carrier bounds, and every carrier-to-carrier bond order transports the exact table,
oriented face map, and numbered-cage certificate.
-/

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

open P94MolecularRingCycleScheduler

/-- Exact induced-cage agreement between a certified reference molecule and a derivative. -/
structure MolecularFullereneCageAgreement
    (reference derivative : RawMolecule) (carrier : Finset Nat) : Prop where
  derivativeBounds : ∀ atom ∈ carrier, atom < derivative.atomCount
  atomAt : ∀ atom ∈ carrier, derivative.atomAt? atom = reference.atomAt? atom
  bondOrder : ∀ left ∈ carrier, ∀ right ∈ carrier,
    derivative.bondOrder left right = reference.bondOrder left right

namespace MolecularFullereneCageAgreement

theorem cageNeighbors_eq
    {reference derivative : RawMolecule} {carrier : Finset Nat}
    (agreement : MolecularFullereneCageAgreement reference derivative carrier)
    (atom : Nat) (atomPresent : atom ∈ carrier) :
    molecularFullereneCageNeighbors derivative carrier atom =
      molecularFullereneCageNeighbors reference carrier atom := by
  ext neighbor
  simp only [molecularFullereneCageNeighbors, Finset.mem_filter]
  constructor
  · rintro ⟨neighborPresent, positive⟩
    refine ⟨neighborPresent, ?_⟩
    rw [← agreement.bondOrder atom atomPresent neighbor neighborPresent]
    exact positive
  · rintro ⟨neighborPresent, positive⟩
    refine ⟨neighborPresent, ?_⟩
    rw [agreement.bondOrder atom atomPresent neighbor neighborPresent]
    exact positive

theorem cageEdges_eq
    {reference derivative : RawMolecule} {carrier : Finset Nat}
    (agreement : MolecularFullereneCageAgreement reference derivative carrier) :
    molecularFullereneCageEdges derivative carrier =
      molecularFullereneCageEdges reference carrier := by
  ext edge
  simp only [molecularFullereneCageEdges, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨leftPresent, rightPresent⟩, ordered, positive⟩
    refine ⟨⟨leftPresent, rightPresent⟩, ordered, ?_⟩
    rw [← agreement.bondOrder edge.1 leftPresent edge.2 rightPresent]
    exact positive
  · rintro ⟨⟨leftPresent, rightPresent⟩, ordered, positive⟩
    refine ⟨⟨leftPresent, rightPresent⟩, ordered, ?_⟩
    rw [agreement.bondOrder edge.1 leftPresent edge.2 rightPresent]
    exact positive

theorem bonded_iff
    {reference derivative : RawMolecule} {carrier : Finset Nat}
    (agreement : MolecularFullereneCageAgreement reference derivative carrier)
    (left right : Nat) (leftPresent : left ∈ carrier) (rightPresent : right ∈ carrier)
    (distinct : left ≠ right) :
    P94ConformationUnit.Bonded derivative left right ↔
      P94ConformationUnit.Bonded reference left right := by
  unfold P94ConformationUnit.Bonded
  rw [← derivative.bondOrder_pos_iff_exists_bond distinct,
    agreement.bondOrder left leftPresent right rightPresent,
    reference.bondOrder_pos_iff_exists_bond distinct]

private theorem nodup_zipTail_distinct {Alpha : Type*} [DecidableEq Alpha]
    (atoms : List Alpha) (nodup : atoms.Nodup) :
    ∀ edge ∈ atoms.zip atoms.tail, edge.1 ≠ edge.2 := by
  induction atoms with
  | nil => simp
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil => simp
      | cons second tail =>
          have nodupParts := List.nodup_cons.mp nodup
          simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
          intro edge present
          rcases present with rfl | present
          · exact fun equal => nodupParts.1 (by
              rw [List.mem_cons]
              exact Or.inl equal)
          · exact inductionHypothesis nodupParts.2 edge present

private theorem zipTail_endpoints_mem {atoms : List Nat} {edge : Nat × Nat}
    (edgePresent : edge ∈ atoms.zip atoms.tail) : edge.1 ∈ atoms ∧ edge.2 ∈ atoms := by
  have endpoints := List.of_mem_zip edgePresent
  exact ⟨endpoints.1, List.mem_of_mem_tail endpoints.2⟩

private theorem cycleEdge_endpoints_mem {atoms : List Nat} {edge : Nat × Nat}
    (edgePresent : edge ∈ (molecularFullereneTraversalUnit atoms).cycleEdges) :
    edge.1 ∈ atoms ∧ edge.2 ∈ atoms := by
  have zippedPresent : edge ∈ atoms.zip (atoms.tail ++ atoms.take 1) := by
    simpa [molecularFullereneTraversalUnit, P94ConformationUnit.cycleEdges,
      P94ConformationUnit.cyclicAdjacentPairs, P94ConformationUnit.cyclicSuccessors] using
        edgePresent
  have endpoints := List.of_mem_zip zippedPresent
  refine ⟨endpoints.1, ?_⟩
  rcases List.mem_append.mp endpoints.2 with tailPresent | headPresent
  · exact List.mem_of_mem_tail tailPresent
  · exact List.mem_of_mem_take headPresent

theorem cagePath
    {reference derivative : RawMolecule} {carrier : Finset Nat}
    (agreement : MolecularFullereneCageAgreement reference derivative carrier)
    {first second : Nat} {path : List Nat}
    (judged : MolecularFullereneCagePath reference carrier first second path) :
    MolecularFullereneCagePath derivative carrier first second path := by
  rcases judged with ⟨nodup, within, headEq, lastEq, consecutive⟩
  refine ⟨nodup, within, headEq, lastEq, ?_⟩
  intro edge edgePresent
  have endpoints := zipTail_endpoints_mem edgePresent
  have distinct := nodup_zipTail_distinct path nodup edge edgePresent
  exact (agreement.bonded_iff edge.1 edge.2
    (within edge.1 endpoints.1) (within edge.2 endpoints.2) distinct).2
      (consecutive edge edgePresent)

theorem connected
    {reference derivative : RawMolecule} {carrier : Finset Nat}
    (agreement : MolecularFullereneCageAgreement reference derivative carrier)
    (judged : MolecularFullereneCageConnected reference carrier) :
    MolecularFullereneCageConnected derivative carrier := by
  refine ⟨judged.1, ?_⟩
  intro first firstPresent second secondPresent
  obtain ⟨path, pathJudged⟩ := judged.2 first firstPresent second secondPresent
  exact ⟨path, agreement.cagePath pathJudged⟩

theorem independentTraversal
    {reference derivative : RawMolecule} {carrier : Finset Nat}
    (agreement : MolecularFullereneCageAgreement reference derivative carrier)
    {face : List Nat} (faceSubset : face.toFinset ⊆ carrier)
    (judged : IndependentP94RingTraversal reference face) :
    IndependentP94RingTraversal derivative face := by
  rcases judged with ⟨minimum, nodup, _referenceBounds, cyclic, cycleCarrier, induced⟩
  have within : ∀ atom ∈ face, atom ∈ carrier := by
    intro atom atomPresent
    exact faceSubset (by simpa using atomPresent)
  have derivativeBounds : ∀ atom ∈ face, atom < derivative.atomCount := by
    intro atom atomPresent
    exact agreement.derivativeBounds atom (within atom atomPresent)
  have derivativeCycleCarrier :
      (molecularFullereneTraversalUnit face).CycleCarrier derivative := by
    refine ⟨minimum, nodup, derivativeBounds, ?_⟩
    intro edge edgePresent
    have endpoints := cycleEdge_endpoints_mem edgePresent
    rw [agreement.bondOrder edge.1 (within edge.1 endpoints.1)
      edge.2 (within edge.2 endpoints.2)]
    exact cycleCarrier.2.2.2 edge edgePresent
  have derivativeCyclic : P94ConformationUnit.CyclicallyBonded derivative face := by
    apply cyclicallyBonded_of_cycleEdges_bonded derivative face minimum
    intro edge edgePresent
    have endpoints := cycleEdge_endpoints_mem edgePresent
    have distinct := cycleEdges_distinct_of_minimum_nodup
      face minimum nodup edge edgePresent
    apply (derivative.bondOrder_pos_iff_exists_bond distinct).mp
    exact derivativeCycleCarrier.2.2.2 edge edgePresent
  refine ⟨minimum, nodup, derivativeBounds, derivativeCyclic, derivativeCycleCarrier, ?_⟩
  intro left leftPresent right rightPresent distinct
  exact (agreement.bonded_iff left right
    (within left leftPresent) (within right rightPresent) distinct).trans
      (induced left leftPresent right rightPresent distinct)

/-- The complete oriented face map depends only on the induced labeled cage graph. -/
theorem oriented
    {reference derivative : RawMolecule} {input : MolecularFullereneConfigurationInput}
    (agreement : MolecularFullereneCageAgreement
      reference derivative input.carrier)
    (judged : OrientedMolecularFullereneFaceMapJudgment reference input) :
    OrientedMolecularFullereneFaceMapJudgment derivative input := by
  rcases judged with ⟨carrierJudged, orientations⟩
  have derivativeCarrier : MolecularFullereneCarrierJudgment derivative input := by
    refine
      { minimumSize := carrierJudged.minimumSize
        carbonAtoms := ?_
        cubic := ?_
        connected := agreement.connected carrierJudged.connected
        facesNodup := carrierJudged.facesNodup
        facesValid := ?_
        facesCover := carrierJudged.facesCover
        twelvePentagons := carrierJudged.twelvePentagons
        hexagonCount := carrierJudged.hexagonCount
        twoFacesPerCageEdge := ?_
        eulerCharacteristicTwo := ?_ }
    · intro atom atomPresent
      obtain ⟨spec, atomEq, carbon⟩ := carrierJudged.carbonAtoms atom atomPresent
      exact ⟨spec, (agreement.atomAt atom atomPresent).trans atomEq, carbon⟩
    · intro atom atomPresent
      rw [agreement.cageNeighbors_eq atom atomPresent]
      exact carrierJudged.cubic atom atomPresent
    · intro face facePresent
      obtain ⟨traversal, subset, size⟩ := carrierJudged.facesValid face facePresent
      exact ⟨agreement.independentTraversal subset traversal, subset, size⟩
    · intro left leftPresent right rightPresent ordered
      rw [agreement.bondOrder left leftPresent right rightPresent]
      exact carrierJudged.twoFacesPerCageEdge left leftPresent right rightPresent ordered
    · rw [agreement.cageEdges_eq]
      exact carrierJudged.eulerCharacteristicTwo
  refine ⟨derivativeCarrier, ?_⟩
  intro left leftPresent right rightPresent ordered positive
  apply orientations left leftPresent right rightPresent ordered
  rw [← agreement.bondOrder left leftPresent right rightPresent]
  exact positive

end MolecularFullereneCageAgreement

namespace MolecularFullereneNumberedCagePackage.Certificate

/-- A shared numbered-cage certificate transports wholesale to a derivative whose induced labeled
cage graph is exactly unchanged. -/
def transport
    (reference derivative : RawMolecule)
    (package : MolecularFullereneNumberedCagePackage)
    (certificate : package.Certificate reference)
    (agreement : MolecularFullereneCageAgreement
      reference derivative package.carrier) :
    package.Certificate derivative := by
  apply Certificate.ofJudgments derivative package
  · have table := certificate.tableJudgment reference package
    exact ⟨table.1, table.2.1, table.2.2.1,
      table.2.2.2.trans agreement.cageEdges_eq.symm⟩
  · exact agreement.oriented certificate.oriented

end MolecularFullereneNumberedCagePackage.Certificate

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.MolecularFullereneNumberedCagePackage.Certificate.transport
