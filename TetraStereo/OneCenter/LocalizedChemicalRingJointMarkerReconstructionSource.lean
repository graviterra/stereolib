import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReadback
import TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceFixing
import TetraStereo.OneCenter.LocalizedChemicalRingReferencePathReconstruction
import TetraStereo.OneCenter.LocalizedChemicalRingColoredReconstruction
import TetraStereo.OneCenter.LocalizedActualBoundaryPathRealization
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-!
# One common source hierarchy and one automorphism fixing every joint reference

The accepted actual joint-key readback derives one joint-canonical pair of addressings, one
address-aligned hierarchy equivalence, all constitutional observations, occupancy, the full
optional reader label and every retained marker coordinate from an actual frame-level tie. The
existing reference-fixing construction then consumes a *single* reference: it uses the scalar
`referenceColor` at one chosen atom.

This module removes that single-reference restriction at the source level. An ordered vector of
source reference bits,

`referenceVectorAt tree references address = references.map (referenceAt tree · address)`,

is preserved at every common readdressed address because each of its coordinates is one column of
the jointly matched mark vector. The same `residualPathTreeEquivOfSameObservations` therefore
preserves the ordered vector color, and `exists_color_preserving_automorphism` yields ONE
molecular automorphism whose action fixes every atom of `references` simultaneously. No reference
is selected inside the construction and no per-reference family of automorphisms is produced.

Main outputs:

* `actual_joint_tie_source_pair`: from an actual list-reference joint-key tie, the common
  hierarchy mapping together with a source-level `ObservedTreePair`, the full readback facts, and
  coordinatewise source reference agreement at every common address.
* `actual_joint_tie_all_references_fixed_aut`: additionally ONE automorphism fixing the boundary,
  sending the left entry to the right entry, fixing every listed reference, acting as the identity
  outside the two residual components, and retaining the witness paths of the very same residual
  path equivalence.
* `actual_root_joint_tie_all_references_fixed_aut`: the actual-root specialization, where
  boundary-rootedness and parent adjacency are derived from the frame rather than supplied.

The boundary of the result: this is a molecular graph statement. Tetrahedral parity preservation
and the physical interpretation of the generated labels remain separate obligations. The exported results carry
kernel-only guards. Physical properness is not a conclusion of this module.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionSource

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalMarker
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedSubtreeContext
open LocalizedChemicalRingJointMarkerKey LocalizedChemicalRingJointMarkerRanking
open LocalizedChemicalRingJointMarkerReadback LocalizedChemicalRingJointMarkerReconstruction
open LocalizedChemicalRingActualReferenceFixing LocalizedChemicalRingReaddressedSource
open LocalizedChemicalRingReferencePathReconstruction LocalizedChemicalRingColoredReconstruction
open LocalizedChemicalRingPromotedConstitutionReadback
open LocalizedActualBoundaryPathRealization
open RetainedCoherentSymmetry RetainedRingSymmetryReconstruction BoundaryComponentReconstruction

noncomputable section
open scoped Classical

/-! ## The ordered source reference vector and its coordinates -/

/-- The ordered vector of source reference-membership bits at one ranked address of an official
source tree. Coordinate `index` is the bit for `references[index]`. -/
def referenceVectorAt (input : CertifiedLocalizedCIPInput)
    (tree : OfficialCIPSourceTree input.Atom) (references : List input.Atom)
    (address : List Nat) : List Nat :=
  references.map fun reference => referenceAt tree reference address

/-- The ordered vector of membership bits of one atom in a list of references. -/
def referenceVectorColor (input : CertifiedLocalizedCIPInput)
    (references : List input.Atom) (atom : input.Atom) : List Nat :=
  references.map fun reference => referenceColor reference atom

/-- Coordinate `index` of the retained mark vector is the single-reference mark of
`references[index]`. -/
theorem referenceMarks_getD (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (references : List input.Atom)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (node : (ruleMajorTreeGraph tree).Node) (index : Nat)
    (indexBound : index < references.length) :
    (referenceMarks input references tree node).getD index 0 =
      referenceMark input references[index] tree node := by
  unfold referenceMarks
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem indexBound,
    Option.map_some, Option.getD_some]

/-- Coordinate `index` of the vector color is the membership bit of `references[index]`. -/
theorem referenceVectorColor_getD (input : CertifiedLocalizedCIPInput)
    (references : List input.Atom) (atom : input.Atom) (index : Nat)
    (indexBound : index < references.length) :
    (referenceVectorColor input references atom).getD index 0 =
      referenceColor references[index] atom := by
  unfold referenceVectorColor
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem indexBound,
    Option.map_some, Option.getD_some]

/-- Coordinate `index` of the source reference vector is the single-reference bit of
`references[index]`. -/
theorem referenceVectorAt_getD (input : CertifiedLocalizedCIPInput)
    (tree : OfficialCIPSourceTree input.Atom) (references : List input.Atom)
    (address : List Nat) (index : Nat) (indexBound : index < references.length) :
    (referenceVectorAt input tree references address).getD index 0 =
      referenceAt tree references[index] address := by
  unfold referenceVectorAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem indexBound,
    Option.map_some, Option.getD_some]

/-! ## Each coordinate of the joint marker is one source reference bit -/

/-- Jointly matched addressings give agreement of the readdressed source reference bit for the
reference at any in-range mark coordinate. This is the scalar ingredient that replaces the
single-reference premise of the accepted construction. -/
theorem readdressed_referenceAt_eq_of_matched
    (input : CertifiedLocalizedCIPInput) (references : List input.Atom)
    {carrierFuel : Nat} (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    {P : Type*} [LinearOrder P]
    {priorL : (ruleMajorTreeGraph left).Node → P}
    {priorR : (ruleMajorTreeGraph right).Node → P}
    {W D : Nat}
    (matched : MatchedJointMarkerAddressings (ruleMajorTreeGraph left)
      (ruleMajorTreeGraph right) priorL priorR
      (referenceMarks input references left) (referenceMarks input references right)
      references.length W D)
    (index : Nat) (indexBound : index < references.length) (position : List Nat) :
    referenceAt (readdressed (toOfficialSourceTree left) matched.leftAddressing
        matched.leftCanonical.1) references[index] position =
      referenceAt (readdressed (toOfficialSourceTree right) matched.rightAddressing
        matched.rightCanonical.1) references[index] position := by
  rw [readdressed_referenceAt_eq (tree := left) (addressing := matched.leftAddressing)
      (dense := matched.leftCanonical.1) (reference := references[index]) (position := position),
    readdressed_referenceAt_eq (tree := right) (addressing := matched.rightAddressing)
      (dense := matched.rightCanonical.1) (reference := references[index]) (position := position)]
  have same := matched.same position index indexBound
  have funcL : (fun x => (referenceMarks input references left x).getD index 0) =
      referenceMark input references[index] left := by
    funext x
    exact referenceMarks_getD input references left x index indexBound
  have funcR : (fun x => (referenceMarks input references right x).getD index 0) =
      referenceMark input references[index] right := by
    funext x
    exact referenceMarks_getD input references right x index indexBound
  rw [funcL, funcR] at same
  exact same

/-- The whole ordered source reference vector agrees at every address of the constructed common
object readdressing. -/
theorem referenceVectorAt_readdressed_eq
    (input : CertifiedLocalizedCIPInput) (references : List input.Atom)
    {carrierFuel : Nat} (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    {P : Type*} [LinearOrder P]
    {priorL : (ruleMajorTreeGraph left).Node → P}
    {priorR : (ruleMajorTreeGraph right).Node → P}
    {W D : Nat}
    (matched : MatchedJointMarkerAddressings (ruleMajorTreeGraph left)
      (ruleMajorTreeGraph right) priorL priorR
      (referenceMarks input references left) (referenceMarks input references right)
      references.length W D)
    (position : List Nat) :
    referenceVectorAt input
        (readdressed (toOfficialSourceTree left) matched.leftAddressing matched.leftCanonical.1)
        references position =
      referenceVectorAt input
        (readdressed (toOfficialSourceTree right) matched.rightAddressing matched.rightCanonical.1)
        references position := by
  unfold referenceVectorAt
  apply List.map_congr_left
  intro reference member
  obtain ⟨index, indexBound, rfl⟩ := List.mem_iff_getElem.mp member
  exact readdressed_referenceAt_eq_of_matched input references left right matched index
    indexBound position

/-! ## Vector-color preservation and one all-reference-fixing automorphism -/

/-- The residual path equivalence of two boundary-rooted source trees preserves the ordered
reference vector color whenever every source reference vector agrees at every common address. -/
theorem residual_reference_vector_preserved
    (input : CertifiedLocalizedCIPInput) {B : List input.Atom} {a b : input.Atom}
    {left right : OfficialCIPSourceTree input.Atom}
    (pair : ObservedTreePair input B B a b left right)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (parentL : ∀ z, B.getLast? = some z → input.moleculeGraph.Adj a z)
    (parentR : ∀ z, B.getLast? = some z → input.moleculeGraph.Adj b z)
    (references : List input.Atom)
    (same : ∀ address, referenceVectorAt input left references address =
      referenceVectorAt input right references address) :
    TerminalColorPreserved
      (residualPathTreeEquivOfSameObservations pair charge rfl parentL parentR)
      (referenceVectorColor input references) := by
  intro path
  obtain ⟨address, lookupL, lookupR⟩ :=
    residualPathTreeEquivOfSameObservations_correspond pair charge rfl parentL parentR path
  have equalBits := same address
  unfold referenceVectorColor
  apply List.map_congr_left
  intro reference member
  obtain ⟨index, indexBound, rfl⟩ := List.mem_iff_getElem.mp member
  have coordinate := congrArg (fun values : List Nat => values.getD index 0) equalBits
  dsimp only at coordinate
  rw [referenceVectorAt_getD input left references address index indexBound,
    referenceVectorAt_getD input right references address index indexBound] at coordinate
  simp only [referenceAt, lookupL, lookupR, Option.map_some, Option.getD_some,
    boundaryNode_current?] at coordinate
  simpa only [referenceColor, pathTerminal,
    List.getLast?_eq_some_getLast path.2.nonempty,
    List.getLast?_eq_some_getLast
      ((residualPathTreeEquivOfSameObservations pair charge rfl parentL parentR).toEquiv path).2.nonempty,
    Option.some.injEq] using coordinate.symm

/-- Preserving the whole ordered vector color fixes every listed reference under the one
constructed permutation. -/
theorem reference_fixed_of_vectorColor (input : CertifiedLocalizedCIPInput)
    (references : List input.Atom) (π : Equiv.Perm input.Atom)
    (colors : ∀ z, referenceVectorColor input references (π z) =
      referenceVectorColor input references z) :
    ∀ reference ∈ references, π reference = reference := by
  intro reference member
  obtain ⟨index, indexBound, rfl⟩ := List.mem_iff_getElem.mp member
  have coordinate := congrArg (fun values : List Nat => values.getD index 0)
    (colors references[index])
  dsimp only at coordinate
  rw [referenceVectorColor_getD input references (π references[index]) index indexBound,
    referenceVectorColor_getD input references references[index] index indexBound] at coordinate
  by_contra different
  simp [referenceColor, different] at coordinate

/-- One color-preserving automorphism of the vector color fixes all listed references at once and
keeps the boundary, the entry image, the outside identity and the witness paths. -/
theorem exists_references_fixed_automorphism
    (input : CertifiedLocalizedCIPInput) {B : List input.Atom} {a b : input.Atom}
    (e : ResidualPathTreeEquiv input.moleculeGraph B B a b)
    (ha : a ∉ B) (references : List input.Atom)
    (preserved : TerminalColorPreserved e (referenceVectorColor input references)) :
    ∃ π : Equiv.Perm input.Atom, input.moleculeGraph.IsAutomorphism π ∧
      (∀ z ∈ B, π z = z) ∧ π a = b ∧
      (∀ reference ∈ references, π reference = reference) ∧
      (∀ x, ¬ InComponent input.moleculeGraph B a x →
        ¬ InComponent input.moleculeGraph B b x → π x = x) ∧
      ∀ x, InComponent input.moleculeGraph B a x →
        ∃ p : {p : List input.Atom // ResidualObsPath input.moleculeGraph B a p},
          pathTerminal p.1 p.2.nonempty = x ∧ (e.toEquiv p).1 = p.1.map π := by
  obtain ⟨π, aut, boundary, entry, colors, outside, witnesses⟩ :=
    exists_color_preserving_automorphism e ha (referenceVectorColor input references) preserved
  exact ⟨π, aut, boundary, entry,
    reference_fixed_of_vectorColor input references π colors, outside, witnesses⟩

/-- From the pair of actual source trees, all listed references are fixed by one automorphism. -/
theorem exists_references_fixed_aut
    (input : CertifiedLocalizedCIPInput) {B : List input.Atom} {a b : input.Atom}
    {left right : OfficialCIPSourceTree input.Atom}
    (pair : ObservedTreePair input B B a b left right)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (parentL : ∀ z, B.getLast? = some z → input.moleculeGraph.Adj a z)
    (parentR : ∀ z, B.getLast? = some z → input.moleculeGraph.Adj b z)
    (references : List input.Atom)
    (same : ∀ address, referenceVectorAt input left references address =
      referenceVectorAt input right references address) :
    ∃ π : Equiv.Perm input.Atom, input.moleculeGraph.IsAutomorphism π ∧
      (∀ z ∈ B, π z = z) ∧ π a = b ∧
      (∀ reference ∈ references, π reference = reference) ∧
      (∀ x, ¬ InComponent input.moleculeGraph B a x →
        ¬ InComponent input.moleculeGraph B b x → π x = x) ∧
      ∀ x, InComponent input.moleculeGraph B a x →
        ∃ p : {p : List input.Atom // ResidualObsPath input.moleculeGraph B a p},
          pathTerminal p.1 p.2.nonempty = x ∧
            ((residualPathTreeEquivOfSameObservations pair charge rfl parentL parentR).toEquiv p).1 =
              p.1.map π := by
  have outside : a ∉ B := not_mem_of_nodup_append_singleton pair.rooted₁.nodup
  exact exists_references_fixed_automorphism input
    (residualPathTreeEquivOfSameObservations pair charge rfl parentL parentR) outside references
    (residual_reference_vector_preserved input pair charge parentL parentR references same)

/-! ## Actual frame ties: the source pair and the all-reference automorphism -/

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph) (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (references : List input.Atom) (W D : Nat) (fallback : CompleteLigandRule5Key)

include fallback

/-- **The actual joint tie constructs the source pair.** One joint-canonical addressing pair and
one hierarchy equivalence are derived from the actual tie; readdressing both arm trees at the
jointly occupied addresses gives an actual `ObservedTreePair`, and the whole source reference
vector agrees at every common address. No source/molecular map, common boundary map or reference
selection is assumed. -/
theorem actual_joint_tie_source_pair (left right : Fin 4)
    (widthL : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).childList node).length ≤ W)
    (heightL : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).height ≤ D)
    (widthR : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).childList node).length ≤ W)
    (heightR : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).height ≤ D)
    (tie : refinedKey input single state target real unit targetUnit references W D left =
      refinedKey input single state target real unit targetUnit references W D right)
    (B : List input.Atom) (a b : input.Atom)
    (rootedL : BoundaryRootedTree input B a
      (toOfficialSourceTree (slotTree input single state target real unit targetUnit left)))
    (rootedR : BoundaryRootedTree input B b
      (toOfficialSourceTree (slotTree input single state target real unit targetUnit right))) :
    let treeL := slotTree input single state target real unit targetUnit left
    let treeR := slotTree input single state target real unit targetUnit right
    ∃ (matched : MatchedJointMarkerAddressings (ruleMajorTreeGraph treeL) (ruleMajorTreeGraph treeR)
        (deepPrior (rawStateDescriptorMap input state) target fallback treeL)
        (deepPrior (rawStateDescriptorMap input state) target fallback treeR)
        (referenceMarks input references treeL) (referenceMarks input references treeR)
        references.length W D)
      (equiv : AlignedHierarchyEquiv matched.leftAddressing matched.rightAddressing)
      (_pair : ObservedTreePair input B B a b
        (readdressed (toOfficialSourceTree treeL) matched.leftAddressing matched.leftCanonical.1)
        (readdressed (toOfficialSourceTree treeR) matched.rightAddressing matched.rightCanonical.1)),
      (∀ rule position,
        LocalizedChemicalRingPromotedConstitutionReadback.observationAt
            (ruleMajorTreeGraph treeL) (observe treeL) matched.leftAddressing rule position =
          LocalizedChemicalRingPromotedConstitutionReadback.observationAt
            (ruleMajorTreeGraph treeR) (observe treeR) matched.rightAddressing rule position) ∧
      (∀ position, (∃ node, matched.leftAddressing.address node = position) ↔
        (∃ node, matched.rightAddressing.address node = position)) ∧
      (∀ x, rawStateReader input state target (nodeSource input treeL x) =
        rawStateReader input state target (nodeSource input treeR (equiv.toEquiv x))) ∧
      (∀ x index, index < references.length →
        (referenceMarks input references treeL x).getD index 0 =
          (referenceMarks input references treeR (equiv.toEquiv x)).getD index 0) ∧
      (∀ position,
        referenceVectorAt input
            (readdressed (toOfficialSourceTree treeL) matched.leftAddressing
              matched.leftCanonical.1) references position =
          referenceVectorAt input
            (readdressed (toOfficialSourceTree treeR) matched.rightAddressing
              matched.rightCanonical.1) references position) := by
  dsimp only
  let treeL := slotTree input single state target real unit targetUnit left
  let treeR := slotTree input single state target real unit targetUnit right
  obtain ⟨matched, equiv, constitution, occupied, reader, marks⟩ :=
    actual_joint_tie_full_readback input single state target real unit targetUnit references W D
      fallback left right widthL heightL widthR heightR tie
  have realizesL := LocalizedRuleMajorSortTrace.realizes_of_trace
    ((frames input single state target real unit targetUnit).stages left).a.trace
  have realizesR := LocalizedRuleMajorSortTrace.realizes_of_trace
    ((frames input single state target real unit targetUnit).stages right).a.trace
  have constitution' := readdressed_constitution_eq treeL treeR realizesL realizesR
    matched.leftAddressing matched.rightAddressing matched.leftCanonical.1 matched.rightCanonical.1
    constitution occupied
  have pair := observedTreePair_of_constitutional single
    (readdressed_boundaryRooted _ matched.leftAddressing matched.leftCanonical.1 rootedL)
    (readdressed_boundaryRooted _ matched.rightAddressing matched.rightCanonical.1 rootedR)
    rfl constitution'
  refine ⟨matched, equiv, pair, constitution, occupied, reader, marks, ?_⟩
  intro position
  exact referenceVectorAt_readdressed_eq input references treeL treeR matched position

/-- **The actual joint tie constructs one automorphism fixing all references.** The common source
pair and source vector agreement are derived from the actual tie; the same residual path
equivalence then yields one automorphism fixing the boundary, sending the left entry to the right
entry, fixing every listed reference at once, acting as the identity off the two residual
components, and realizing its images along the retained witness paths. -/
theorem actual_joint_tie_all_references_fixed_aut (left right : Fin 4)
    (widthL : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).childList node).length ≤ W)
    (heightL : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).height ≤ D)
    (widthR : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).childList node).length ≤ W)
    (heightR : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).height ≤ D)
    (tie : refinedKey input single state target real unit targetUnit references W D left =
      refinedKey input single state target real unit targetUnit references W D right)
    (B : List input.Atom) (a b : input.Atom)
    (rootedL : BoundaryRootedTree input B a
      (toOfficialSourceTree (slotTree input single state target real unit targetUnit left)))
    (rootedR : BoundaryRootedTree input B b
      (toOfficialSourceTree (slotTree input single state target real unit targetUnit right)))
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (parentL : ∀ z, B.getLast? = some z → input.moleculeGraph.Adj a z)
    (parentR : ∀ z, B.getLast? = some z → input.moleculeGraph.Adj b z) :
    let treeL := slotTree input single state target real unit targetUnit left
    let treeR := slotTree input single state target real unit targetUnit right
    ∃ (matched : MatchedJointMarkerAddressings (ruleMajorTreeGraph treeL) (ruleMajorTreeGraph treeR)
        (deepPrior (rawStateDescriptorMap input state) target fallback treeL)
        (deepPrior (rawStateDescriptorMap input state) target fallback treeR)
        (referenceMarks input references treeL) (referenceMarks input references treeR)
        references.length W D)
      (equiv : AlignedHierarchyEquiv matched.leftAddressing matched.rightAddressing)
      (pair : ObservedTreePair input B B a b
        (readdressed (toOfficialSourceTree treeL) matched.leftAddressing matched.leftCanonical.1)
        (readdressed (toOfficialSourceTree treeR) matched.rightAddressing matched.rightCanonical.1))
      (π : Equiv.Perm input.Atom),
      (∀ rule position,
        LocalizedChemicalRingPromotedConstitutionReadback.observationAt
            (ruleMajorTreeGraph treeL) (observe treeL) matched.leftAddressing rule position =
          LocalizedChemicalRingPromotedConstitutionReadback.observationAt
            (ruleMajorTreeGraph treeR) (observe treeR) matched.rightAddressing rule position) ∧
      (∀ position, (∃ node, matched.leftAddressing.address node = position) ↔
        (∃ node, matched.rightAddressing.address node = position)) ∧
      (∀ x, rawStateReader input state target (nodeSource input treeL x) =
        rawStateReader input state target (nodeSource input treeR (equiv.toEquiv x))) ∧
      (∀ x index, index < references.length →
        (referenceMarks input references treeL x).getD index 0 =
          (referenceMarks input references treeR (equiv.toEquiv x)).getD index 0) ∧
      (∀ position,
        referenceVectorAt input
            (readdressed (toOfficialSourceTree treeL) matched.leftAddressing
              matched.leftCanonical.1) references position =
          referenceVectorAt input
            (readdressed (toOfficialSourceTree treeR) matched.rightAddressing
              matched.rightCanonical.1) references position) ∧
      input.moleculeGraph.IsAutomorphism π ∧
      (∀ z ∈ B, π z = z) ∧ π a = b ∧
      (∀ reference ∈ references, π reference = reference) ∧
      (∀ x, ¬ InComponent input.moleculeGraph B a x →
        ¬ InComponent input.moleculeGraph B b x → π x = x) ∧
      (∀ x, InComponent input.moleculeGraph B a x →
        ∃ p : {p : List input.Atom // ResidualObsPath input.moleculeGraph B a p},
          pathTerminal p.1 p.2.nonempty = x ∧
            ((residualPathTreeEquivOfSameObservations pair charge rfl parentL parentR).toEquiv p).1 =
              p.1.map π) := by
  dsimp only
  obtain ⟨matched, equiv, pair, constitution, occupied, reader, marks, vectorSame⟩ :=
    actual_joint_tie_source_pair input single state target real unit targetUnit references W D
      fallback left right widthL heightL widthR heightR tie B a b rootedL rootedR
  obtain ⟨π, aut, boundary, entry, fixedRefs, outside, witnesses⟩ :=
    exists_references_fixed_aut input pair charge parentL parentR references vectorSame
  exact ⟨matched, equiv, pair, π, constitution, occupied, reader, marks, vectorSame,
    aut, boundary, entry, fixedRefs, outside, witnesses⟩

/-- **The actual-root special case.** Boundary-rootedness and parent adjacency are derived from
the actual frame by `root_slot_boundary`; the conclusion fixes the center, sends the left slot atom
to the right one, fixes every listed reference under the same single automorphism, and keeps the
identity off the two residual components at the singleton boundary. -/
theorem actual_root_joint_tie_all_references_fixed_aut (rootAddress : target.1.address = [])
    (left right : Fin 4)
    (widthL : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).childList node).length ≤ W)
    (heightL : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).height ≤ D)
    (widthR : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).childList node).length ≤ W)
    (heightR : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).height ≤ D)
    (tie : refinedKey input single state target real unit targetUnit references W D left =
      refinedKey input single state target real unit targetUnit references W D right)
    (a b : input.Atom)
    (currentL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.current? = some a)
    (currentR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.current? = some b)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph) :
    ∃ π : Equiv.Perm input.Atom, input.moleculeGraph.IsAutomorphism π ∧
      π target.1.root = target.1.root ∧ π a = b ∧
      (∀ reference ∈ references, π reference = reference) ∧
      (∀ x, ¬ InComponent input.moleculeGraph [target.1.root] a x →
        ¬ InComponent input.moleculeGraph [target.1.root] b x → π x = x) := by
  obtain ⟨rootedL, adjacentL⟩ := root_slot_boundary single (rawStateDescriptorMap input state)
    target (frames input single state target real unit targetUnit) rootAddress left a currentL
  obtain ⟨rootedR, adjacentR⟩ := root_slot_boundary single (rawStateDescriptorMap input state)
    target (frames input single state target real unit targetUnit) rootAddress right b currentR
  obtain ⟨matched, equiv, pair, π, constitution, occupied, reader, marks, vectorSame,
    aut, boundary, entry, fixedRefs, outside, witnesses⟩ :=
    actual_joint_tie_all_references_fixed_aut input single state target real unit targetUnit
      references W D fallback left right widthL heightL widthR heightR tie
      [target.1.root] a b rootedL rootedR charge
      (by
        intro z hz
        have equality : target.1.root = z := by simpa using hz
        rw [← equality]
        exact adjacentL)
      (by
        intro z hz
        have equality : target.1.root = z := by simpa using hz
        rw [← equality]
        exact adjacentR)
  exact ⟨π, aut, boundary target.1.root (by simp), entry, fixedRefs, outside⟩

end

end TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionSource

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionSource.referenceVectorAt
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionSource.referenceVectorColor
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionSource.referenceMarks_getD
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionSource.referenceVectorColor_getD
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionSource.readdressed_referenceAt_eq_of_matched
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionSource.referenceVectorAt_readdressed_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionSource.residual_reference_vector_preserved
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionSource.reference_fixed_of_vectorColor
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionSource.exists_references_fixed_automorphism
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionSource.exists_references_fixed_aut
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionSource.actual_joint_tie_source_pair
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionSource.actual_joint_tie_all_references_fixed_aut
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionSource.actual_root_joint_tie_all_references_fixed_aut

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionSource.referenceVectorAt_getD
