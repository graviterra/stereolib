import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionWitness
import TetraStereo.OneCenter.LocalizedChemicalRingCoveredRefusalOddWitness
import TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness
import TetraStereo.OneCenter.LocalizedChemicalRingFinalEntryCorrection
import TetraStereo.OneCenter.LocalizedChemicalRingRankedCorrectionLoop
import TetraStereo.OneCenter.LocalizedChemicalRingProperRotationConsensus
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
**Corrections derived from actual refusals, by induction on the residual size.**

For every reached occurrence in a tied root branch, every reference and either geometry side, an
actual marked-key tie between two slots gives one of:
* `SourceProper`: one automorphism fixing the history and the reference, sending the first slot
  atom to the second, proper at every center of the source component; or
* a `MovingRefusal` at some reached occurrence with strictly longer history. The escape
  need not belong to this source component or its matched paths, and may use another reference.

`MovingRefusal` is the two-port case and nothing else: the actual descriptor refuses under a
reference; an even map fixes the history and that reference and moves a neighbor; an odd map fixes
the history and moves that reference; both maps are proper at every center off the history.
This existential pair of maps does not exclude an additional odd reference-fixing map.
The accepted test at
`[0,30,34,26,1,2]` with reference 28 has this local shape. This module neither excludes that case
nor shows that it arises from an actual tie.

The correction oracle of `LocalizedChemicalRingRankedCorrectionLoop` is constructed from the
induction hypothesis when the global longer-history escape is excluded. That exclusion remains
a substantive hypothesis of the source-proper corollary. The quantifier is per tie: one tie gives one
automorphism for its whole source component. This is not universal ring correctness.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionInduction

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingReferenceConsensusCorrectionWitness
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingSelectedRefusalWitness
open LocalizedChemicalRingSelectedOutwardTie LocalizedChemicalRingOutwardKeyWitness
open LocalizedChemicalRingCoveredRefusalOddWitness (failed_eligible_reading_odd_witness eligible_reference_parent)
open LocalizedChemicalRingResidualThreeCycleRefusal (slotAction refusal_has_failed_eligible referenceAt_action)
open LocalizedChemicalRingInheritedReferenceTie (reached_descriptor_original_reference_tie)
open LocalizedChemicalRingMovedSlotEligibility (actual_slot_key_action)
open LocalizedChemicalRingSelectedParentEligibility (eligible_iff_other)
open LocalizedChemicalRingBoundaryWitnessFactMatch LocalizedChemicalRingWitnessFactMatch
open LocalizedChemicalRingBoundaryWitnessOrientation (witness_boundary)
open LocalizedChemicalRingWitnessRawDescent (boundary_query_length_le)
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRankedCorrectionTransport
open LocalizedChemicalRingRankedReconstruction LocalizedChemicalRingComponentExchangeProperness
open LocalizedChemicalRingComponentOrientationSupport (relativeSign_outside)
open LocalizedChemicalRingFinalEntryCorrection (slot_fixed)
open LocalizedChemicalRingTwoFixedNeighbors (local_odd_of_two_fixed_neighbors)
open LocalizedChemicalRingRankedCorrectionLoop
open LocalizedChemicalRingProperRotationConsensus (slot_current)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedPromotedRanking (frames refinedKey)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachableConfigurations (Reached reached_child)
open LocalizedMarkedTerminalReferenceScope (Descends descendant_reached)
open LocalizedMarkedOperationEvaluator (mem_tiedChildren_actual)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_one_or_neg_one)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

/-- One automorphism for the whole source component of a tie. -/
def SourceProper (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (reference a b : input.Atom) : Prop :=
  ∃ e : input.detectedMultiCenterMolecule.Aut,
    (∀ atom ∈ target.1.node.history, (e : Equiv.Perm input.Atom) atom = atom) ∧
    (e : Equiv.Perm input.Atom) a = b ∧
    (e : Equiv.Perm input.Atom) reference = reference ∧
    ∀ d : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph target.1.node.history.reverse a d.1 →
      relativeSign input.detectedMultiCenterMolecule cfg e d = 1

/-- An actual refusal with an even history/reference-fixing map moving a neighbor, and an
odd history-fixing map moving the reference. Both are proper off the history. This does not
assert that every odd map moves the reference or that a reference-fixing correction is impossible. -/
def MovingRefusal (reference : input.Atom) (query : RawMolecule.CanonicalBranchNode) : Prop :=
  ∃ (d : input.detectedMultiCenterMolecule.Center)
    (evenMap oddMap : input.detectedMultiCenterMolecule.Aut),
    query.atom = d.1.val ∧ Reached mol query ∧
    LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
      (structuralDepth mol query) (inputGeometry input) [] (some reference.val) query = none ∧
    (∀ value ∈ query.history, relabelOf input (evenMap : Equiv.Perm input.Atom) value = value) ∧
    (evenMap : Equiv.Perm input.Atom) reference = reference ∧
    relativeSign input.detectedMultiCenterMolecule cfg evenMap d = 1 ∧
    (∃ x, input.moleculeGraph.Adj d.1 x ∧ (evenMap : Equiv.Perm input.Atom) x ≠ x) ∧
    (∀ x : input.detectedMultiCenterMolecule.Center, x.1.val ∉ query.history →
      relativeSign input.detectedMultiCenterMolecule cfg evenMap x = 1) ∧
    (∀ value ∈ query.history, relabelOf input (oddMap : Equiv.Perm input.Atom) value = value) ∧
    relativeSign input.detectedMultiCenterMolecule cfg oddMap d = -1 ∧
    (oddMap : Equiv.Perm input.Atom) reference ≠ reference ∧
    ∀ x : input.detectedMultiCenterMolecule.Center, x.1.val ∉ query.history →
      relativeSign input.detectedMultiCenterMolecule cfg oddMap x = 1

/-- The induction statement at residual size `n`. -/
def Claim (n : Nat) : Prop :=
  ∀ (node : RawMolecule.CanonicalBranchNode), structuralDepth mol node = n → Reached mol node →
  ∀ (c : input.detectedMultiCenterMolecule.Center), node.atom = c.1.val →
  ∀ (data : OccurrenceData input mol c node), TiedRootBranch input data.target →
  ∀ (reference : input.Atom) (reflected : Bool) (left right : Fin 4) (a b : input.Atom), a ≠ b →
  MatchedSymmetry input single (sideState input mol node reference reflected) data.target data.real
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl reference left right a b →
  SourceProper input cfg data.target reference a b ∨
    ∃ (other : input.Atom) (query : RawMolecule.CanonicalBranchNode),
      node.history.length < query.history.length ∧ MovingRefusal input mol cfg other query

/-! ## From an actual tie to a matched symmetry, for any state -/

include charge in
theorem matched_of_tie (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode) (data : OccurrenceData input mol c node)
    (branch : TiedRootBranch input data.target) (state : OccurrenceAuxState) (reference : input.Atom)
    (left right : Fin 4) (distinct : left ≠ right)
    (tie : markedKeys input mol single c node data state reference left =
      markedKeys input mol single c node data state reference right) :
    ∃ a b : input.Atom, a ≠ b ∧
      Nonempty (MatchedSymmetry input single state data.target data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl reference left right a b) := by
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  change refinedKey input single state data.target data.real unit rfl reference
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) left =
    refinedKey input single state data.target data.real unit rfl reference
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) right at tie
  obtain ⟨center, current⟩ := input.localizedRerootCursor_current_exists
    (⟨data.target, none⟩ : input.LocalizedRerootCursor (retainedCarrierFuel input))
  obtain ⟨_, pair, a, b, _, _, _, targetEq, leftEq, rightEq, different,
      currentL, currentR, realL, realR⟩ := selected_refined_tie_real_outward input single
    branch.rootCursor branch.rootAddress branch.arm branch.arm' branch.member branch.member'
    branch.different branch.real branch.real' branch.read branch.read' branch.key branch.key'
    branch.built branch.built' branch.tie state data.target data.real branch.inside branch.nonroot
    center current unit rfl reference (retainedCarrierFuel input)
    (2 * (retainedCarrierFuel input + 1)) left right distinct tie
  have rootL := pair.leftRoot
  have rootR := pair.rightRoot
  have addressL := pair.leftAddress
  have addressR := pair.rightAddress
  rw [targetEq, leftEq] at rootL addressL
  rw [targetEq, rightEq] at rootR addressR
  rw [leftEq] at currentL realL
  rw [rightEq] at currentR realR
  obtain ⟨e, rank, fixed, entry, ref, support, matched⟩ := actual_outward_default_tie_witness
    input single state data.target data.real unit rfl reference left right a b currentL currentR
    realL realR rootL rootR pair.leftSlot pair.rightSlot addressL addressR tie charge
  exact ⟨a, b, different,
    ⟨⟨currentL, currentR, realL, realR, e, rank, fixed, entry, ref, support, matched⟩⟩⟩

/-! ## The boundary and branch of a deeper occurrence -/

private theorem foldSlots_prefix (start : OfficialCIPNode input.Atom) (xs ys : List input.Atom) :
    input.foldSlots start xs <+: input.foldSlots start (xs ++ ys) := by
  induction xs generalizing start with
  | nil => exact List.nil_prefix
  | cons x xs ih =>
      simp only [List.cons_append, CertifiedLocalizedCIPInput.foldSlots_cons]
      exact (List.prefix_cons_inj _).mpr (ih _)

section Query

variable {c d : input.detectedMultiCenterMolecule.Center} {node query : RawMolecule.CanonicalBranchNode}
  (data : OccurrenceData input mol c node) (actual : OccurrenceData input mol d query)
  (p : List input.Atom)
  (payload : query = rawPathNode data.target.1.root (boundaryPath data.target p))

include single payload in
/-- The actual occurrence of a boundary query has exactly the extended boundary as its history. -/
theorem actual_boundary :
    actual.target.1.node.history.reverse = data.target.1.node.history.reverse ++ p := by
  subst payload
  have histories : actual.target.1.node.history =
      (data.target.1.root :: boundaryPath data.target p).reverse := by
    apply List.map_injective_iff.mpr Fin.val_injective
    exact (LocalizedMarkedCarrierLookup.lookup?_sound input _ actual.target actual.found).history
  rw [histories, List.reverse_reverse, root_cons_boundaryPath single data.target p]

include single payload in
/-- A boundary query stays in any tied branch containing its source, and it is not a root. -/
def query_branch (branch : TiedRootBranch input data.target) :
    TiedRootBranch input actual.target := by
  have boundary := actual_boundary input mol single data actual p payload
  have packedS := input.legitimateOccurrence_transport single 1
    (input.carrierOccurrence_legitimate single data.target)
  have packedQ := input.legitimateOccurrence_transport single 1
    (input.carrierOccurrence_legitimate single actual.target)
  have rootS := packedS.sourceHead
  have rootQ := packedQ.sourceHead
  rw [boundary] at rootQ
  have sourceNonempty : data.target.1.node.history.reverse ≠ [] := by
    intro empty
    rw [empty] at rootS
    simp at rootS
  have sameRoot : data.target.1.root = actual.target.1.root := by
    rw [List.head?_append_of_ne_nil _ sourceNonempty] at rootQ
    exact Option.some.inj (rootS.symm.trans rootQ)
  have addressPrefix : data.target.1.address <+: actual.target.1.address := by
    rw [packedS.sourceAddress, packedQ.sourceAddress]
    unfold CertifiedLocalizedCIPInput.canonicalAddress
    rw [boundary, ← sameRoot]
    obtain ⟨first, rest, split⟩ := List.exists_cons_of_ne_nil sourceNonempty
    rw [split]
    exact foldSlots_prefix input _ rest p
  refine
    { rootCursor := branch.rootCursor
      rootAddress := branch.rootAddress
      arm := branch.arm
      arm' := branch.arm'
      member := branch.member
      member' := branch.member'
      different := branch.different
      real := branch.real
      real' := branch.real'
      read := branch.read
      read' := branch.read'
      fuel := branch.fuel
      fuel' := branch.fuel'
      key := branch.key
      key' := branch.key'
      built := branch.built
      built' := branch.built'
      tie := branch.tie
      inside := ⟨branch.inside.1.trans sameRoot, branch.inside.2.trans addressPrefix⟩
      nonroot := ?_ }
  intro empty
  rw [empty] at addressPrefix
  exact branch.nonroot (List.prefix_nil.mp addressPrefix)

end Query

/-! ## Local parity -/

private theorem even_fixed_cube : ∀ (p : Equiv.Perm (Fin 4)) (i : Fin 4), p i = i →
    Equiv.Perm.sign p = 1 → p ^ 3 = 1 := by decide +kernel

private theorem conjugate_cube : ∀ (frame p : Equiv.Perm (Fin 4)), p ^ 3 = 1 →
    ((frame.trans p).trans frame.symm) ^ 3 = 1 := by decide +kernel

private theorem sign_of_handedness (p : Equiv.Perm (Fin 4)) (proper : permHandedness p = 1) :
    Equiv.Perm.sign p = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with one | negative
  · exact one
  · exfalso
    have value : permHandedness p = -1 := by simp [permHandedness, negative]
    rw [value] at proper
    norm_num at proper

/-! ## Re-extension as one bundle -/

/-- A source-proper symmetry of a boundary, re-extended: the same entry action and fixed atoms,
identity off the two entry components, and proper at every center off the boundary. -/
theorem reextend_proper (boundary : List input.Atom) (a b : input.Atom)
    (e : input.detectedMultiCenterMolecule.Aut)
    (fixed : ∀ x ∈ boundary, (e : Equiv.Perm input.Atom) x = x)
    (entry : (e : Equiv.Perm input.Atom) a = b) (distinct : a ≠ b)
    (sourceProper : ∀ x : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph boundary a x.1 →
      relativeSign input.detectedMultiCenterMolecule cfg e x = 1) :
    ∃ g : input.detectedMultiCenterMolecule.Aut,
      (∀ x ∈ boundary, (g : Equiv.Perm input.Atom) x = x) ∧
      (∀ x, ¬ InComponent input.moleculeGraph boundary a x →
        ¬ InComponent input.moleculeGraph boundary b x → (g : Equiv.Perm input.Atom) x = x) ∧
      (g : Equiv.Perm input.Atom) a = b ∧
      (∀ r, (e : Equiv.Perm input.Atom) r = r → (g : Equiv.Perm input.Atom) r = r) ∧
      ∀ x : input.detectedMultiCenterMolecule.Center, x.1 ∉ boundary →
        relativeSign input.detectedMultiCenterMolecule cfg g x = 1 := by
  have ha : a ∉ boundary := fun member => distinct ((fixed a member).symm.trans entry)
  have hb : b ∉ boundary := by
    intro member
    apply distinct
    apply (e : Equiv.Perm input.Atom).injective
    rw [entry, fixed b member]
  have support := reextended_support input.detectedMultiCenterMolecule boundary a b e fixed entry
    ha hb
  refine ⟨reextendedAut input.detectedMultiCenterMolecule boundary a b e fixed entry ha hb,
    support.1, support.2, ?_, ?_, ?_⟩
  · exact (reextended_eq_source input.detectedMultiCenterMolecule boundary a b e fixed entry ha hb a
      (inComponent_self input.moleculeGraph ha)).trans entry
  · intro r fixedR
    exact reextended_preserves_fixed input.detectedMultiCenterMolecule boundary a b e fixed entry
      ha hb r fixedR
  · intro x outside
    by_cases left : InComponent input.moleculeGraph boundary a x.1
    · exact reextended_proper_union input.detectedMultiCenterMolecule cfg boundary a b e fixed entry
        ha hb sourceProper x (Or.inl left)
    · by_cases right : InComponent input.moleculeGraph boundary b x.1
      · exact reextended_proper_union input.detectedMultiCenterMolecule cfg boundary a b e fixed
          entry ha hb sourceProper x (Or.inr right)
      · exact relativeSign_outside input.detectedMultiCenterMolecule cfg _ boundary a b support.1
          support.2 x outside left right

/-! ## Correcting one center -/

/-- A correction at one center, in the shape `localCorrection_of_support` consumes. -/
def CenterCorrection (d : input.detectedMultiCenterMolecule.Center) (B : List input.Atom)
    (reference : input.Atom) (g : input.detectedMultiCenterMolecule.Aut) : Prop :=
  ∃ a' b' : input.Atom,
    input.moleculeGraph.Adj d.1 a' ∧ input.moleculeGraph.Adj d.1 b' ∧
    (∀ x ∈ B ++ [d.1], (g : Equiv.Perm input.Atom) x = x) ∧
    (∀ x, ¬ InComponent input.moleculeGraph (B ++ [d.1]) a' x →
      ¬ InComponent input.moleculeGraph (B ++ [d.1]) b' x → (g : Equiv.Perm input.Atom) x = x) ∧
    (g : Equiv.Perm input.Atom) reference = reference ∧
    relativeSign input.detectedMultiCenterMolecule cfg g d = -1 ∧
    ∀ e : input.detectedMultiCenterMolecule.Center, e.1 ∉ B ++ [d.1] →
      relativeSign input.detectedMultiCenterMolecule cfg g e = 1

include agreement admissible supported charge calibrated in
/-- **Correcting one refused center.** With the residual induction available, an actual refusal
under a reference gives an odd correction fixing that reference, or the two-port case. The
occurrence is any reached real detected occurrence whose history is `B` followed by its center. -/
theorem occurrence_correction (n : Nat) (IH : ∀ m < n, Claim input mol single cfg m)
    (d : input.detectedMultiCenterMolecule.Center) (query : RawMolecule.CanonicalBranchNode)
    (queryReached : Reached mol query) (queryReal : query.provenance = .realAtom)
    (atomEq : query.atom = d.1.val) (smaller : structuralDepth mol query < n)
    (B : List input.Atom) (outsideB : d.1 ∉ B)
    (boundary : ∀ actual : OccurrenceData input mol d query,
      actual.target.1.node.history.reverse = B ++ [d.1])
    (branch : ∀ actual : OccurrenceData input mol d query, TiedRootBranch input actual.target)
    (reference : input.Atom)
    (refused : LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
      (structuralDepth mol query) (inputGeometry input) [] (some reference.val) query = none) :
    (∃ g, CenterCorrection input cfg d B reference g) ∨
    ∃ (other : input.Atom) (deeper : RawMolecule.CanonicalBranchNode),
      query.history.length ≤ deeper.history.length ∧ MovingRefusal input mol cfg other deeper := by
  obtain ⟨actual, side, i, j, stepNone, different, tie⟩ := reached_descriptor_original_reference_tie
    input mol agreement admissible supported single cfg d (calibrated d) query queryReached queryReal
    atomEq (structuralDepth mol query) reference refused
  have actualBoundary := boundary actual
  have branchQ := branch actual
  have sound := (LocalizedMarkedCarrierLookup.lookup?_sound input query actual.target actual.found).history
  have inHistory : ∀ x ∈ B ++ [d.1], x.val ∈ query.history := by
    intro x member
    rw [← sound]
    rw [← actualBoundary] at member
    exact List.mem_map.mpr ⟨x, List.mem_reverse.mp member, rfl⟩
  have carriedB : ∀ atom ∈ B, atom.val ∈ query.history :=
    fun atom member => inHistory atom (List.mem_append_left _ member)
  have centerMember : d.1 ∈ B ++ [d.1] := List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have historyFixedOf (g : input.detectedMultiCenterMolecule.Aut)
      (fixed : ∀ x ∈ B ++ [d.1], (g : Equiv.Perm input.Atom) x = x) :
      ∀ value ∈ query.history, relabelOf input (g : Equiv.Perm input.Atom) value = value := by
    intro value member
    rw [← sound] at member
    obtain ⟨atom, present, same⟩ := List.mem_map.mp member
    rw [← same, relabelOf_val]
    apply congrArg Fin.val
    apply fixed
    rw [← actualBoundary]
    exact List.mem_reverse.mpr present
  have adjacentOf (slot : Fin 4) :
      input.moleculeGraph.Adj d.1 (referenceAt input mol d query actual slot) :=
    input.detectedMultiCenterMolecule.ligandAtomAt_adj d (actual.ligandOf slot)
  -- The tie under the inherited reference.
  obtain ⟨a', b', distinctQ, ⟨w⟩⟩ := matched_of_tie input mol single charge d query actual branchQ
    _ reference i j different tie
  have atLeft : a' = referenceAt input mol d query actual i :=
    Option.some.inj (w.leftCurrent.symm.trans (slot_current input mol single d query actual _ i))
  have atRight : b' = referenceAt input mol d query actual j :=
    Option.some.inj (w.rightCurrent.symm.trans (slot_current input mol single d query actual _ j))
  have adjacentA : input.moleculeGraph.Adj d.1 a' := by
    rw [atLeft]
    exact adjacentOf i
  have adjacentB : input.moleculeGraph.Adj d.1 b' := by
    rw [atRight]
    exact adjacentOf j
  rcases IH _ smaller query rfl queryReached d atomEq actual branchQ reference side i j a' b'
    distinctQ w with good | moving
  swap
  · obtain ⟨other, deeper, longer, bad⟩ := moving
    exact Or.inr ⟨other, deeper, Nat.le_of_lt longer, bad⟩
  obtain ⟨e, fixedE, entryE, referenceE, properE⟩ := good
  have fixedB : ∀ x ∈ B ++ [d.1], (e : Equiv.Perm input.Atom) x = x := by
    intro x member
    rw [← actualBoundary] at member
    exact fixedE x (List.mem_reverse.mp member)
  have sourceE : ∀ x : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph (B ++ [d.1]) a' x.1 →
      relativeSign input.detectedMultiCenterMolecule cfg e x = 1 := by
    intro x member
    rw [← actualBoundary] at member
    exact properE x member
  obtain ⟨g1, fixed1, support1, moved1, keeps1, off1⟩ :=
    reextend_proper input cfg (B ++ [d.1]) a' b' e fixedB entryE distinctQ sourceE
  have reference1 := keeps1 reference referenceE
  rcases relativeSign_eq_one_or_neg_one input.detectedMultiCenterMolecule cfg g1 d with
    evenSign | negative
  swap
  · exact Or.inl ⟨g1, a', b', adjacentA, adjacentB, fixed1, support1, reference1, negative, off1⟩
  -- The map fixing the reference is even at the center: the fallback population decides.
  have fixedCenter : input.detectedMultiCenterMolecule.centerPerm g1 d = d :=
    Subtype.ext (fixed1 d.1 centerMember)
  have handedness : permHandedness (input.detectedMultiCenterMolecule.ligandPermAt g1 d) = 1 := by
    rw [← LocalizedChemicalRingCompletenessOrbit.relativeSign_fixed input cfg g1 d fixedCenter]
    exact evenSign
  have historyFixed1 := historyFixedOf g1 fixed1
  obtain ⟨permutation, atoms, keys⟩ := actual_slot_key_action input mol agreement admissible supported
    single g1 d query actual queryReached historyFixed1
  have changed : permutation i ≠ i := by
    intro same
    have image := atoms i
    rw [same, ← atLeft, moved1] at image
    exact distinctQ image
  have memberA : i ∈ eligibleSlots input mol single d query actual :=
    (eligible_iff_other input mol single d query actual i).mpr ⟨permutation i, changed, keys i⟩
  obtain ⟨parent, parentHistory, parentAdjacent, _⟩ :=
    eligible_reference_parent input mol single d query actual branchQ i memberA
  have parentFixed : (g1 : Equiv.Perm input.Atom) parent = parent := by
    apply fixed1
    rw [← actualBoundary]
    exact List.mem_reverse.mpr parentHistory
  obtain ⟨parentLigand, atParent⟩ := input.detectedMultiCenterMolecule.ligandAtomAt_surjective d parent
    parentAdjacent
  have ligandFixed : input.detectedMultiCenterMolecule.ligandPermAt g1 d parentLigand = parentLigand :=
    slot_fixed input.detectedMultiCenterMolecule g1 d parentLigand fixedCenter
      (by rw [atParent]; exact parentFixed)
  have ligandCube := even_fixed_cube _ parentLigand ligandFixed (sign_of_handedness _ handedness)
  have cube : (slotAction input mol g1 d query actual) ^ 3 = 1 :=
    conjugate_cube actual.ligandOf _ ligandCube
  have nontrivial : slotAction input mol g1 d query actual ≠ 1 := by
    intro same
    have image := referenceAt_action input mol g1 d query actual fixedCenter i
    rw [same, Equiv.Perm.coe_one, id_eq, ← atLeft, moved1] at image
    exact distinctQ image
  have properResidual : ∀ x : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph B d.1 x.1 → x.1 ≠ d.1 →
      relativeSign input.detectedMultiCenterMolecule cfg g1 x = 1 := by
    intro x member other
    apply off1
    intro present
    rcases List.mem_append.mp present with inB | isCenter
    · exact inComponent_not_mem input.moleculeGraph member inB
    · exact other (List.mem_singleton.mp isCenter)
  obtain ⟨slot, member, failed, _⟩ := refusal_has_failed_eligible input mol single g1 d query actual
    agreement admissible supported queryReached atomEq historyFixed1 cfg calibrated queryReal B
    outsideB carriedB properResidual branchQ cube nontrivial (structuralDepth mol query)
    (some reference.val) side stepNone
  -- The tie under a local reference: an odd map, by the same induction.
  obtain ⟨left, right, a'', b'', _, distinctO, wOdd, _⟩ := failed_eligible_reading_odd_witness
    input mol single d query actual agreement admissible supported cfg (calibrated d) atomEq
    branchQ charge (structuralDepth mol query) side slot member failed
  have atOddLeft : a'' = referenceAt input mol d query actual left :=
    Option.some.inj (wOdd.leftCurrent.symm.trans
      (slot_current input mol single d query actual _ left))
  have atOddRight : b'' = referenceAt input mol d query actual right :=
    Option.some.inj (wOdd.rightCurrent.symm.trans
      (slot_current input mol single d query actual _ right))
  have adjacentOddA : input.moleculeGraph.Adj d.1 a'' := by
    rw [atOddLeft]
    exact adjacentOf left
  have adjacentOddB : input.moleculeGraph.Adj d.1 b'' := by
    rw [atOddRight]
    exact adjacentOf right
  rcases IH _ smaller query rfl queryReached d atomEq actual branchQ
    (referenceAt input mol d query actual slot) side left right a'' b'' distinctO wOdd with
    goodO | moving
  swap
  · obtain ⟨other, deeper, longer, bad⟩ := moving
    exact Or.inr ⟨other, deeper, Nat.le_of_lt longer, bad⟩
  obtain ⟨o, fixedO, entryO, referenceO, properO⟩ := goodO
  have fixedOB : ∀ x ∈ B ++ [d.1], (o : Equiv.Perm input.Atom) x = x := by
    intro x present
    rw [← actualBoundary] at present
    exact fixedO x (List.mem_reverse.mp present)
  have sourceO : ∀ x : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph (B ++ [d.1]) a'' x.1 →
      relativeSign input.detectedMultiCenterMolecule cfg o x = 1 := by
    intro x present
    rw [← actualBoundary] at present
    exact properO x present
  obtain ⟨g2, fixed2, support2, moved2, keeps2, off2⟩ :=
    reextend_proper input cfg (B ++ [d.1]) a'' b'' o fixedOB entryO distinctO sourceO
  obtain ⟨parentO, parentOHistory, parentOAdjacent, parentODifferent⟩ :=
    eligible_reference_parent input mol single d query actual branchQ slot member
  have parentOFixed : (g2 : Equiv.Perm input.Atom) parentO = parentO := by
    apply fixed2
    rw [← actualBoundary]
    exact List.mem_reverse.mpr parentOHistory
  obtain ⟨fixedCenter2, oddLocal⟩ := local_odd_of_two_fixed_neighbors
    input.detectedMultiCenterMolecule g2 d (fixed2 d.1 centerMember) parentO
    (referenceAt input mol d query actual slot) parentODifferent parentOAdjacent (adjacentOf slot)
    parentOFixed (keeps2 _ referenceO)
    ⟨a'', adjacentOddA, by rw [moved2]; exact Ne.symm distinctO⟩
  have negativeO : relativeSign input.detectedMultiCenterMolecule cfg g2 d = -1 := by
    rw [LocalizedChemicalRingCompletenessOrbit.relativeSign_fixed input cfg g2 d fixedCenter2]
    exact oddLocal
  by_cases referenceKept : (g2 : Equiv.Perm input.Atom) reference = reference
  · exact Or.inl ⟨g2, a'', b'', adjacentOddA, adjacentOddB, fixed2, support2, referenceKept,
      negativeO, off2⟩
  · exact Or.inr ⟨reference, query, Nat.le_refl _, d, g1, g2, atomEq, queryReached, refused,
      historyFixed1, reference1, evenSign,
      ⟨a', adjacentA, by rw [moved1]; exact Ne.symm distinctQ⟩,
      fun x absent => off1 x (fun present => absent (inHistory x.1 present)),
      historyFixedOf g2 fixed2, negativeO, referenceKept,
      fun x absent => off2 x (fun present => absent (inHistory x.1 present))⟩

/-! ## The residual induction -/

include agreement admissible supported charge calibrated in
theorem claim_step (n : Nat) (IH : ∀ m < n, Claim input mol single cfg m) :
    Claim input mol single cfg n := by
  intro node nodeDepth reached c _current data branch reference reflected left right a b distinct w
  by_cases escape : ∃ (other : input.Atom) (query : RawMolecule.CanonicalBranchNode),
      node.history.length < query.history.length ∧ MovingRefusal input mol cfg other query
  · exact Or.inr escape
  left
  obtain ⟨W, _⟩ := exists_correctionWitness input mol agreement admissible supported c node data
    reached reference single reflected left right a b distinct w
  unfold SourceProper
  apply sourceProper_of_oracle input mol agreement admissible supported single c node data reached W
    cfg calibrated
  intro d p _member terminal prefixLower higher refused
  have boundaryFacts := witness_boundary input single data.target a p.1 p.2
  have atomEq : (rawPathNode data.target.1.root (boundaryPath data.target p.1)).atom = d.1.val := by
    rw [← terminal]
    exact boundaryFacts.1.symm
  have outsideB : d.1 ∉ data.target.1.node.history.reverse ++ p.1.dropLast := by
    rw [← terminal]
    exact boundaryFacts.2.1
  obtain ⟨child, selected, descent, _⟩ := W.execution p.1 p.2
  have queryReached : Reached mol (rawPathNode data.target.1.root (boundaryPath data.target p.1)) :=
    descendant_reached (reached_child mol node child reached
      (mem_tiedChildren_actual mol (sparseOperations input mol) [] node child selected)) descent
  have queryReal : (rawPathNode data.target.1.root (boundaryPath data.target p.1)).provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom := rfl
  have nodeLength : node.history.length = data.target.1.node.history.length := by
    have sound := (LocalizedMarkedCarrierLookup.lookup?_sound input node data.target data.found).history
    rw [← sound, List.length_map]
  have queryLength : (rawPathNode data.target.1.root (boundaryPath data.target p.1)).history.length =
      data.target.1.node.history.length + p.1.length := by
    rw [boundaryPath_raw_history single data.target p.1, List.length_map, List.length_append,
      List.length_reverse, Nat.add_comm]
  have pathPositive : 0 < p.1.length := List.length_pos_of_ne_nil p.2.nonempty
  have queryBound := boundary_query_length_le input mol agreement single data.target data.real a
    p.1 p.2
  have split : p.1.dropLast ++ [d.1] = p.1 := by
    have whole := List.dropLast_append_getLast p.2.nonempty
    have last : p.1.getLast p.2.nonempty = d.1 := terminal
    rw [last] at whole
    exact whole
  generalize queryEq : rawPathNode data.target.1.root (boundaryPath data.target p.1) = query
    at atomEq queryReached queryReal queryLength queryBound refused
  have remaining : structuralDepth mol node + node.history.length - query.history.length =
      structuralDepth mol query := by
    unfold structuralDepth
    omega
  have smaller : structuralDepth mol query < n := by
    rw [← nodeDepth]
    unfold structuralDepth
    omega
  rw [remaining] at refused
  rcases occurrence_correction input mol agreement admissible supported single charge cfg calibrated
      n IH d query queryReached queryReal atomEq smaller
      (data.target.1.node.history.reverse ++ p.1.dropLast) outsideB
      (fun actual => by
        have extended := actual_boundary input mol single data actual p.1 queryEq.symm
        rw [extended, List.append_assoc, split])
      (fun actual => query_branch input mol single data actual p.1 queryEq.symm branch)
      reference refused with correction | ⟨other, deeper, longer, bad⟩
  · obtain ⟨g, a', b', adjacentA, adjacentB, fixedG, supportG, referenceG, negativeG, properG⟩ :=
      correction
    exact ⟨g, localCorrection_of_support input mol c node data W cfg d p.1 prefixLower higher
      outsideB g a' b' adjacentA adjacentB fixedG supportG referenceG negativeG properG⟩
  · exact absurd ⟨other, deeper, by omega, bad⟩ escape

include agreement admissible supported charge calibrated in
theorem claim_all (n : Nat) : Claim input mol single cfg n := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  exact claim_step input mol agreement admissible supported single charge cfg calibrated n ih

include agreement admissible supported charge calibrated in
/-- **Every actual tie in a tied root branch is source-proper, or a deeper two-port refusal
exists.** The entry atoms are the two tied slots' own ligand atoms. Any reached occurrence, any
reference, either geometry side, the actual generated state at the structural depth. -/
theorem tie_sourceProper_or_movingRefusal (node : RawMolecule.CanonicalBranchNode)
    (reached : Reached mol node) (c : input.detectedMultiCenterMolecule.Center)
    (current : node.atom = c.1.val) (data : OccurrenceData input mol c node)
    (branch : TiedRootBranch input data.target) (reference : input.Atom) (reflected : Bool)
    (left right : Fin 4) (distinct : left ≠ right)
    (tie : markedKeys input mol single c node data (sideState input mol node reference reflected)
        reference left =
      markedKeys input mol single c node data (sideState input mol node reference reflected)
        reference right) :
    SourceProper input cfg data.target reference (referenceAt input mol c node data left)
        (referenceAt input mol c node data right) ∨
      ∃ (other : input.Atom) (query : RawMolecule.CanonicalBranchNode),
        node.history.length < query.history.length ∧ MovingRefusal input mol cfg other query := by
  obtain ⟨a, b, different, ⟨w⟩⟩ := matched_of_tie input mol single charge c node data branch _
    reference left right distinct tie
  have atLeft : a = referenceAt input mol c node data left :=
    Option.some.inj (w.leftCurrent.symm.trans (slot_current input mol single c node data _ left))
  have atRight : b = referenceAt input mol c node data right :=
    Option.some.inj (w.rightCurrent.symm.trans (slot_current input mol single c node data _ right))
  subst atLeft
  subst atRight
  exact claim_all input mol agreement admissible supported single charge cfg calibrated
    (structuralDepth mol node) node rfl reached c current data branch reference reflected left right
    _ _ different w

include agreement admissible supported charge calibrated in
/-- If the entire input has no `MovingRefusal` witness, every actual tie is source-proper.
The global exclusion is explicit and is not proved here. -/
theorem tie_sourceProper_of_no_movingRefusal
    (noTwoPort : ∀ (other : input.Atom) (query : RawMolecule.CanonicalBranchNode),
      ¬ MovingRefusal input mol cfg other query)
    (node : RawMolecule.CanonicalBranchNode)
    (reached : Reached mol node) (c : input.detectedMultiCenterMolecule.Center)
    (current : node.atom = c.1.val) (data : OccurrenceData input mol c node)
    (branch : TiedRootBranch input data.target) (reference : input.Atom) (reflected : Bool)
    (left right : Fin 4) (distinct : left ≠ right)
    (tie : markedKeys input mol single c node data (sideState input mol node reference reflected)
        reference left =
      markedKeys input mol single c node data (sideState input mol node reference reflected)
        reference right) :
    SourceProper input cfg data.target reference (referenceAt input mol c node data left)
      (referenceAt input mol c node data right) := by
  rcases tie_sourceProper_or_movingRefusal input mol agreement admissible supported single charge cfg
    calibrated node reached c current data branch reference reflected left right distinct tie with
    proper | ⟨other, query, _, bad⟩
  · exact proper
  · exact absurd bad (noTwoPort other query)

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionInduction

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionInduction.matched_of_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionInduction.actual_boundary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionInduction.query_branch
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionInduction.reextend_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionInduction.occurrence_correction
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionInduction.claim_step
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionInduction.claim_all
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionInduction.tie_sourceProper_or_movingRefusal
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionInduction.tie_sourceProper_of_no_movingRefusal
