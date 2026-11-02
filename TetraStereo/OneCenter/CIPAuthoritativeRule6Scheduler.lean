import TetraStereo.OneCenter.DeclarativeCIPOccurrenceRules456
import TetraStereo.OneCenter.CIPAuthoritativeRule6P92Enumeration
import TetraStereo.OneCenter.CIPAuthoritativeOccurrenceDescriptorComparatorLaws
import TetraStereo.OneCenter.CIPAuthoritativeLonePairDigraphConformance

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.AuthoritativeCIPRule6Scheduler

open RawMolecule
open DeclarativeCIP
open DeclarativeCIP.ProductionOccurrenceRules456
open AuthoritativeCIPOccurrenceCompleteness
open AuthoritativeCIPOccurrenceCompleteness.DescriptorRule6HierarchySupport
open AuthoritativeCIPRule6Completeness
open AuthoritativeCIPRule6P92Enumeration
open AuthoritativeCIPRule6ReferenceFamily
open Rule6ReferenceFamilySemantics
open Rule6FourWayFamilySemantics

/-!
# Uncapped authoritative Rule-6 scheduling

The exact P-92 two-, three-, and dependent four-reference evaluators were previously proved as
standalone functions.  This module connects them to one executable Rule-6 result path.  Both the
initial Rules-1a--5 partition and every promoted Rule-6 ranking use the width-unbounded
authoritative occurrence comparators.
-/

/-- Uncapped Rules-1a--5 comparison between two positions of a four-ligand frame. -/
def compareAuthoritativeRule6InitialPositions? (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat) (roots : List CanonicalRerootCursor)
    (left right : Nat) : Option OccurrenceComparison := do
  let leftRoot ← roots[left]?
  let rightRoot ← roots[right]?
  compareOccurrenceBranchesUnrestrictedAuthoritative? mol state fuel leftRoot rightRoot

/-- Stable fail-closed insertion by the uncapped ordinary comparator. -/
def insertAuthoritativeRule6InitialPosition? (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat) (roots : List CanonicalRerootCursor)
    (candidate : Nat) : List Nat → Option (List Nat)
  | [] => some [candidate]
  | head :: tail => do
      let decision ← compareAuthoritativeRule6InitialPositions?
        mol state fuel roots candidate head
      if decision.ordering = Ordering.lt then
        let deeper ← insertAuthoritativeRule6InitialPosition?
          mol state fuel roots candidate tail
        some (head :: deeper)
      else
        some (candidate :: head :: tail)

/-- Initial Rule-6 position order using no production frontier cap or automorphism-conflict gate. -/
def sortAuthoritativeRule6InitialPositions? (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat) (roots : List CanonicalRerootCursor) :
    List Nat → Option (List Nat)
  | [] => some []
  | position :: positions => do
      let sorted ← sortAuthoritativeRule6InitialPositions? mol state fuel roots positions
      insertAuthoritativeRule6InitialPosition? mol state fuel roots position sorted

/-- All adjacent outcomes of the uncapped initial order, in the shape expected by P-92's
reference-family selectors. -/
def compareAuthoritativeRule6InitialAdjacent? (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat) (roots : List CanonicalRerootCursor) :
    List Nat → Option (List (Option Ordering))
  | [] | [_] => some []
  | left :: right :: remaining => do
      let decision ← compareAuthoritativeRule6InitialPositions?
        mol state fuel roots left right
      let deeper ← compareAuthoritativeRule6InitialAdjacent?
        mol state fuel roots (right :: remaining)
      some (some decision.ordering :: deeper)

/-- Adjacent traversal returns exactly one fewer outcome than positions. -/
theorem compareAuthoritativeRule6InitialAdjacent?_length
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) :
    ∀ positions adjacent,
      compareAuthoritativeRule6InitialAdjacent? mol state fuel roots positions = some adjacent →
        adjacent.length = positions.length - 1
  | [], adjacent, computed => by
      simp [compareAuthoritativeRule6InitialAdjacent?] at computed
      subst adjacent
      rfl
  | [_], adjacent, computed => by
      simp [compareAuthoritativeRule6InitialAdjacent?] at computed
      subst adjacent
      rfl
  | left :: right :: remaining, adjacent, computed => by
      unfold compareAuthoritativeRule6InitialAdjacent? at computed
      cases decisionEq : compareAuthoritativeRule6InitialPositions?
          mol state fuel roots left right with
      | none => simp [decisionEq] at computed
      | some decision =>
          cases deeperEq : compareAuthoritativeRule6InitialAdjacent?
              mol state fuel roots (right :: remaining) with
          | none => simp [decisionEq, deeperEq] at computed
          | some deeper =>
              simp [decisionEq, deeperEq] at computed
              subst adjacent
              have tailLength := compareAuthoritativeRule6InitialAdjacent?_length
                mol state fuel roots (right :: remaining) deeper deeperEq
              simp at tailLength ⊢
              exact tailLength

/-- The initial authoritative sort preserves every input position exactly. -/
theorem insertAuthoritativeRule6InitialPosition?_perm
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (candidate : Nat) :
    ∀ input output,
      insertAuthoritativeRule6InitialPosition? mol state fuel roots candidate input =
          some output →
        output.Perm (candidate :: input)
  | [], output, computed => by
      simp [insertAuthoritativeRule6InitialPosition?] at computed
      subst output
      rfl
  | head :: tail, output, computed => by
      unfold insertAuthoritativeRule6InitialPosition? at computed
      cases decisionEq : compareAuthoritativeRule6InitialPositions?
          mol state fuel roots candidate head with
      | none => simp [decisionEq] at computed
      | some decision =>
          by_cases isLt : decision.ordering = Ordering.lt
          · cases deeperEq : insertAuthoritativeRule6InitialPosition?
                mol state fuel roots candidate tail with
            | none => simp [decisionEq, isLt, deeperEq] at computed
            | some deeper =>
                simp [decisionEq, isLt, deeperEq] at computed
                subst output
                exact (List.Perm.cons head
                  (insertAuthoritativeRule6InitialPosition?_perm mol state fuel roots candidate
                    tail deeper deeperEq)).trans
                  (List.Perm.swap candidate head tail)
          · simp [decisionEq, isLt] at computed
            subst output
            rfl

theorem sortAuthoritativeRule6InitialPositions?_perm
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) :
    ∀ input output,
      sortAuthoritativeRule6InitialPositions? mol state fuel roots input = some output →
        output.Perm input
  | [], output, computed => by
      simp [sortAuthoritativeRule6InitialPositions?] at computed
      subst output
      rfl
  | candidate :: remaining, output, computed => by
      unfold sortAuthoritativeRule6InitialPositions? at computed
      cases tailEq : sortAuthoritativeRule6InitialPositions?
          mol state fuel roots remaining with
      | none => simp [tailEq] at computed
      | some tail =>
          cases insertedEq : insertAuthoritativeRule6InitialPosition?
              mol state fuel roots candidate tail with
          | none => simp [tailEq, insertedEq] at computed
          | some inserted =>
              simp [tailEq, insertedEq] at computed
              subst output
              exact (insertAuthoritativeRule6InitialPosition?_perm
                mol state fuel roots candidate tail inserted insertedEq).trans
                (List.Perm.cons candidate
                  (sortAuthoritativeRule6InitialPositions?_perm
                    mol state fuel roots remaining tail tailEq))

/-- Every listed position names an actual cursor in the selected ligand frame. -/
def Rule6PositionsInRange (roots : List CanonicalRerootCursor)
    (positions : List Nat) : Prop :=
  ∀ position, position ∈ positions → position < roots.length

theorem compareAuthoritativeRule6InitialPositions?_exists_of_support
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    (hierarchy : DescriptorRule6HierarchySupport mol state fuel)
    (roots : List CanonicalRerootCursor)
    (supported : ∀ root, root ∈ roots → CursorSupport mol fuel root)
    (left right : Nat) (leftBound : left < roots.length)
    (rightBound : right < roots.length) :
    ∃ decision,
      compareAuthoritativeRule6InitialPositions? mol state fuel roots left right =
        some decision := by
  let leftRoot := roots[left]
  let rightRoot := roots[right]
  have leftEq : roots[left]? = some leftRoot := List.getElem?_eq_getElem leftBound
  have rightEq : roots[right]? = some rightRoot := List.getElem?_eq_getElem rightBound
  rcases hierarchy.ordinary_comparison_exists leftRoot rightRoot
      (supported leftRoot (List.getElem_mem leftBound))
      (supported rightRoot (List.getElem_mem rightBound)) with
    ⟨decision, decisionEq⟩
  exact ⟨decision, by
    simp [compareAuthoritativeRule6InitialPositions?, leftEq, rightEq, decisionEq]⟩

theorem insertAuthoritativeRule6InitialPosition?_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor}
    (comparisonTotal : ∀ left right,
      left < roots.length → right < roots.length →
      ∃ decision,
        compareAuthoritativeRule6InitialPositions? mol state fuel roots left right =
          some decision)
    (candidate : Nat) (candidateBound : candidate < roots.length) :
    ∀ input, Rule6PositionsInRange roots input →
      ∃ output,
        insertAuthoritativeRule6InitialPosition? mol state fuel roots candidate input =
          some output
  | [], _ => ⟨[candidate], rfl⟩
  | head :: tail, inRange => by
      have headBound : head < roots.length := inRange head (by simp)
      rcases comparisonTotal candidate head candidateBound headBound with
        ⟨decision, decisionEq⟩
      by_cases isLt : decision.ordering = Ordering.lt
      · have tailRange : Rule6PositionsInRange roots tail := by
          intro position member
          exact inRange position (by simp [member])
        rcases insertAuthoritativeRule6InitialPosition?_exists comparisonTotal
            candidate candidateBound tail tailRange with ⟨deeper, deeperEq⟩
        exact ⟨head :: deeper, by
          simp [insertAuthoritativeRule6InitialPosition?, decisionEq, isLt, deeperEq]⟩
      · exact ⟨candidate :: head :: tail, by
          simp [insertAuthoritativeRule6InitialPosition?, decisionEq, isLt]⟩

theorem sortAuthoritativeRule6InitialPositions?_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor}
    (comparisonTotal : ∀ left right,
      left < roots.length → right < roots.length →
      ∃ decision,
        compareAuthoritativeRule6InitialPositions? mol state fuel roots left right =
          some decision) :
    ∀ input, Rule6PositionsInRange roots input →
      ∃ output,
        sortAuthoritativeRule6InitialPositions? mol state fuel roots input = some output
  | [], _ => ⟨[], rfl⟩
  | candidate :: remaining, inRange => by
      have candidateBound : candidate < roots.length := inRange candidate (by simp)
      have remainingRange : Rule6PositionsInRange roots remaining := by
        intro position member
        exact inRange position (by simp [member])
      rcases sortAuthoritativeRule6InitialPositions?_exists comparisonTotal
          remaining remainingRange with ⟨sorted, sortedEq⟩
      have sortedPerm := sortAuthoritativeRule6InitialPositions?_perm
        mol state fuel roots remaining sorted sortedEq
      have sortedRange : Rule6PositionsInRange roots sorted := by
        intro position member
        exact remainingRange position ((sortedPerm.mem_iff).mp member)
      rcases insertAuthoritativeRule6InitialPosition?_exists comparisonTotal
          candidate candidateBound sorted sortedRange with ⟨output, outputEq⟩
      exact ⟨output, by
        simp [sortAuthoritativeRule6InitialPositions?, sortedEq, outputEq]⟩

theorem compareAuthoritativeRule6InitialAdjacent?_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor}
    (comparisonTotal : ∀ left right,
      left < roots.length → right < roots.length →
      ∃ decision,
        compareAuthoritativeRule6InitialPositions? mol state fuel roots left right =
          some decision) :
    ∀ positions, Rule6PositionsInRange roots positions →
      ∃ adjacent,
        compareAuthoritativeRule6InitialAdjacent? mol state fuel roots positions =
          some adjacent
  | [], _ => ⟨[], rfl⟩
  | [_], _ => ⟨[], rfl⟩
  | left :: right :: remaining, inRange => by
      have leftBound : left < roots.length := inRange left (by simp)
      have rightBound : right < roots.length := inRange right (by simp)
      rcases comparisonTotal left right leftBound rightBound with ⟨decision, decisionEq⟩
      have tailRange : Rule6PositionsInRange roots (right :: remaining) := by
        intro position member
        exact inRange position (by simp_all)
      rcases compareAuthoritativeRule6InitialAdjacent?_exists comparisonTotal
          (right :: remaining) tailRange with ⟨deeper, deeperEq⟩
      exact ⟨some decision.ordering :: deeper, by
        simp [compareAuthoritativeRule6InitialAdjacent?, decisionEq, deeperEq]⟩

/-- Consequently, chemical recursive support makes the uncapped initial four-position ranking
operationally total. -/
theorem sortAuthoritativeRule6InitialPositions?_exists_of_support
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    (hierarchy : DescriptorRule6HierarchySupport mol state fuel)
    (roots : List CanonicalRerootCursor) (rootsLength : roots.length = 4)
    (supported : ∀ root, root ∈ roots → CursorSupport mol fuel root) :
    ∃ sorted,
      sortAuthoritativeRule6InitialPositions? mol state fuel roots (List.range 4) =
        some sorted := by
  apply sortAuthoritativeRule6InitialPositions?_exists
    (fun left right leftBound rightBound =>
      compareAuthoritativeRule6InitialPositions?_exists_of_support hierarchy roots supported
        left right leftBound rightBound)
  intro position member
  rw [List.mem_range] at member
  simpa [rootsLength] using member

/-- On a supported four-cursor frame, both phases of the initial P-92 partition—sorting and
adjacent comparison—complete. -/
theorem authoritativeRule6InitialPartition_exists_of_support
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    (hierarchy : DescriptorRule6HierarchySupport mol state fuel)
    (roots : List CanonicalRerootCursor) (rootsLength : roots.length = 4)
    (supported : ∀ root, root ∈ roots → CursorSupport mol fuel root) :
    ∃ sorted adjacent,
      sortAuthoritativeRule6InitialPositions? mol state fuel roots (List.range 4) =
          some sorted ∧
        compareAuthoritativeRule6InitialAdjacent? mol state fuel roots sorted =
          some adjacent := by
  let comparisonTotal := fun left right leftBound rightBound =>
    compareAuthoritativeRule6InitialPositions?_exists_of_support hierarchy roots supported
      left right leftBound rightBound
  rcases sortAuthoritativeRule6InitialPositions?_exists_of_support
      hierarchy roots rootsLength supported with ⟨sorted, sortedEq⟩
  have sortedPerm := sortAuthoritativeRule6InitialPositions?_perm
    mol state fuel roots (List.range 4) sorted sortedEq
  have sortedRange : Rule6PositionsInRange roots sorted := by
    intro position member
    have inFour : position < 4 := by
      rw [← List.mem_range]
      exact (sortedPerm.mem_iff).mp member
    simpa [rootsLength] using inFour
  rcases compareAuthoritativeRule6InitialAdjacent?_exists comparisonTotal
      sorted sortedRange with ⟨adjacent, adjacentEq⟩
  exact ⟨sorted, adjacent, sortedEq, adjacentEq⟩

/-- The standard four-ligand occurrence frame has recursive support even when its fourth slot is
the canonical lone-pair phantom.  The physical cursors inherit molecule-derived support; the
phantom is a forced terminal leaf. -/
theorem occurrenceLigandFrame?_result_length
    (mol : RawMolecule) (occurrence : CanonicalBranchNode)
    (roots : List CanonicalRerootCursor)
    (frameEq : occurrenceLigandFrame? mol occurrence = some roots) :
    roots.length = 4 := by
  dsimp [occurrenceLigandFrame?] at frameEq
  split at frameEq
  · simp at frameEq
  · split at frameEq
    · rename_i physicalFour
      have rootsEq := Option.some.inj frameEq
      subst roots
      simpa using physicalFour
    · split at frameEq
      · rename_i physicalThreeAndPhantom
        have rootsEq := Option.some.inj frameEq
        subst roots
        have resolved : (occurrenceLigandCursors mol occurrence).length = 3 ∧
            mol.atomCount ∈ mol.ligandsWithLonePair occurrence.atom := by
          simpa using physicalThreeAndPhantom
        have physicalThree := resolved.1
        simp [physicalThree]
      · simp at frameEq

theorem mem_eraseCanonicalParentCopy_of_fst_ne
    (parent : Nat) (copy : Nat × Nat) (copies : List (Nat × Nat))
    (notParent : copy.1 ≠ parent) (member : copy ∈ copies) :
    copy ∈ RawMolecule.eraseCanonicalParentCopy parent copies := by
  induction copies with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at member
      by_cases erased : head.1 == parent && head.2 == 0
      · simp [RawMolecule.eraseCanonicalParentCopy, erased]
        rcases member with copyEq | member
        · subst head
          simp at erased
          exact (notParent erased.1).elim
        · exact member
      · simp [RawMolecule.eraseCanonicalParentCopy, erased]
        rcases member with rfl | member
        · exact Or.inl rfl
        · exact Or.inr (inductionHypothesis member)

/-- A positive physical edge supplies the real canonical root occurrence used by the explicit
production ligand frame. -/
theorem canonicalRoot_mem_canonicalChildren_of_bondOrder_pos
    (mol : RawMolecule) (center ligand : Nat) (distinct : ligand ≠ center)
    (positive : 0 < mol.bondOrder center ligand) :
    canonicalRoot center ligand ∈ mol.canonicalChildren (canonicalCenterRoot center) := by
  have canonicalPositive :
      0 < mol.canonicalBondOrder (canonicalCenterRoot center) ligand :=
    AuthoritativeCIPValenceBondingNumber.canonicalBondOrder_pos_of_bondOrder_pos
      mol (canonicalCenterRoot center) ligand positive
  have centerNeLigand : center ≠ ligand := Ne.symm distinct
  rcases (RawMolecule.bondOrder_pos_iff_exists_bond mol centerNeLigand).mp positive with
    ⟨bond, bondMember, connects⟩
  have rawSeed : (ligand, 0) ∈
      mol.bonds.flatMap fun selected =>
        let next? :=
          if selected.source == center then some selected.target
          else if selected.target == center then some selected.source
          else none
        match next? with
        | none => []
        | some next =>
            (List.range (mol.canonicalBondOrder (canonicalCenterRoot center) next)).map
              fun copyIndex => (next, copyIndex) := by
    rw [List.mem_flatMap]
    refine ⟨bond, bondMember, ?_⟩
    simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connects
    rcases connects with forward | reverse
    · rcases forward with ⟨sourceEq, targetEq⟩
      simp [sourceEq, targetEq, canonicalPositive]
    · rcases reverse with ⟨sourceEq, targetEq⟩
      simp [sourceEq, targetEq, distinct, canonicalPositive]
  have retained : (ligand, 0) ∈ mol.canonicalChildCopies (canonicalCenterRoot center) := by
    unfold RawMolecule.canonicalChildCopies
    apply mem_eraseCanonicalParentCopy_of_fst_ne
    · simpa [canonicalCenterRoot] using distinct
    · exact rawSeed
  unfold RawMolecule.canonicalChildren
  simp only [CanonicalBranchNode.forcedLeaf, canonicalCenterRoot,
    CanonicalNodeProvenance.realAtom, Bool.false_eq_true, ↓reduceIte, List.mem_map]
  refine ⟨(ligand, 0), retained, ?_⟩
  simp [canonicalRoot, distinct]

/-- Each slot of the production center frame has recursive uncapped-comparator support.  Physical
slots are generated real canonical edges; the atom-count lone-pair slot is terminal. -/
theorem productionLigandCursor_supported
    {mol : RawMolecule} (wellFormed : mol.WellFormed)
    (writtenExact : mol.WrittenNeighborExact)
    (root : ProductionCIPOccurrenceDiscovery.Root mol)
    (bonding : AuthoritativeCIPMoleculeCursorRanking.CanonicalCenterBondingNumberSix mol
      (ProductionCIPOccurrenceDiscovery.centerAtom root).val)
    (fuel : Nat) (depthCovered : 2 * mol.atomCount + 1 ≤ fuel) (slot : Fin 4) :
    CursorSupport mol fuel (ProductionCIPOccurrenceDiscovery.ligandCursor root slot) := by
  let center := (ProductionCIPOccurrenceDiscovery.centerAtom root).val
  let ligand := ProductionCIPOccurrenceDiscovery.ligandAtom root slot
  by_cases phantom : ligand = mol.atomCount
  · apply CursorSupport.terminal
    have childrenNil : mol.canonicalChildren
        (ProductionCIPOccurrenceDiscovery.ligandRootNode root slot) = [] := by
      apply canonicalChildren_eq_nil_of_atom_eq_atomCount
        mol (ProductionCIPOccurrenceDiscovery.ligandRootNode root slot) wellFormed
      simpa [ProductionCIPOccurrenceDiscovery.ligandRootNode,
        ProductionCIPOccurrenceDiscovery.ligandCursor, ligand] using phantom
    have cursorChildrenNil :
        (ProductionCIPOccurrenceDiscovery.ligandCursor root slot).children mol = [] := by
      simp [ProductionCIPOccurrenceDiscovery.ligandRootNode, canonicalRoot] at childrenNil
      simp [ProductionCIPOccurrenceDiscovery.ligandCursor,
        ProductionCIPOccurrenceDiscovery.ligandRootNode, canonicalRoot,
        CanonicalRerootCursor.children, CanonicalRerootCursor.neighbors,
        canonicalOriginalParent?, canonicalCenterRoot, childrenNil]
    simp [cursorTerminal, cursorChildrenNil]
  · have ligandMember : ligand ∈ mol.ligandsWithLonePair center := by
      exact ProductionCIPOccurrenceDiscovery.ligandAtom_mem root slot
    have writtenMember : ligand ∈ mol.writtenNeighbors center :=
      mem_writtenNeighbors_of_mem_ligandsWithLonePair_of_ne
        mol center ligand ligandMember phantom
    have centerBound : center < mol.atomCount :=
      (ProductionCIPOccurrenceDiscovery.centerAtom root).isLt
    have clauses := RawMolecule.WrittenNeighborExact.at mol writtenExact
      (ProductionCIPOccurrenceDiscovery.centerAtom root)
    have ligandBound : ligand < mol.atomCount := clauses.2.1 ligand writtenMember
    let ligandFin : Fin mol.atomCount := ⟨ligand, ligandBound⟩
    have positive : 0 < mol.bondOrder center ligand :=
      (clauses.2.2 ligandFin).mp writtenMember
    have distinct : ligand ≠ center := by
      intro equal
      have positiveSelf : 0 < mol.bondOrder center center := by
        simpa [equal] using positive
      rw [mol.bondOrder_self] at positiveSelf
      exact (Nat.not_lt_zero 0 positiveSelf).elim
    have childMember : canonicalRoot center ligand ∈
        mol.canonicalChildren (canonicalCenterRoot center) :=
      canonicalRoot_mem_canonicalChildren_of_bondOrder_pos
        mol center ligand distinct positive
    have eligible : AuthoritativeCIPMoleculeCursorRanking.CanonicalCenterRerootCursor
        mol center (ProductionCIPOccurrenceDiscovery.ligandCursor root slot) := by
      simpa [ProductionCIPOccurrenceDiscovery.ligandCursor,
        ProductionCIPOccurrenceDiscovery.ligandRootNode, center, ligand] using
          (AuthoritativeCIPMoleculeCursorRanking.canonicalRootCursor_eligible childMember)
    exact (AuthoritativeCIPMoleculeCursorRanking.canonicalCenterCursorSupport
      centerBound wellFormed bonding eligible).mono depthCovered

theorem productionLigandCursors_supported
    {mol : RawMolecule} (wellFormed : mol.WellFormed)
    (writtenExact : mol.WrittenNeighborExact)
    (root : ProductionCIPOccurrenceDiscovery.Root mol)
    (bonding : AuthoritativeCIPMoleculeCursorRanking.CanonicalCenterBondingNumberSix mol
      (ProductionCIPOccurrenceDiscovery.centerAtom root).val)
    (fuel : Nat) (depthCovered : 2 * mol.atomCount + 1 ≤ fuel) :
    ∀ cursor, cursor ∈ ProductionCIPOccurrenceDiscovery.ligandCursors root →
      CursorSupport mol fuel cursor := by
  intro cursor member
  rw [ProductionCIPOccurrenceDiscovery.ligandCursors, List.mem_ofFn] at member
  rcases member with ⟨slot, rfl⟩
  exact productionLigandCursor_supported wellFormed writtenExact root bonding fuel
    depthCovered slot

/-- On the exact slot-aligned production center frame, certified chemical intake makes the
initial partition and every promoted P-92 reference ranking operationally total. -/
theorem authoritativeProductionRule6Frame_operationally_total
    {mol : RawMolecule} {state : OccurrenceAuxState}
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (writtenExact : mol.WrittenNeighborExact) (valence : mol.ValenceOK)
    (kekule : AuthoritativeCIPMancudeTotality.LocalizedMancudeKekuleAdmissible mol)
    (root : ProductionCIPOccurrenceDiscovery.Root mol) :
    ∃ sorted adjacent,
      sortAuthoritativeRule6InitialPositions? mol state (2 * mol.atomCount + 1)
          (ProductionCIPOccurrenceDiscovery.ligandCursors root) (List.range 4) = some sorted ∧
        compareAuthoritativeRule6InitialAdjacent? mol state (2 * mol.atomCount + 1)
          (ProductionCIPOccurrenceDiscovery.ligandCursors root) sorted = some adjacent ∧
        ∀ referencePosition,
          ∃ ranking,
            authoritativeOccurrenceRule6PositionRankingBackend mol state
              (2 * mol.atomCount + 1)
              (ProductionCIPOccurrenceDiscovery.ligandCursors root)
              (mol.ligandsWithLonePair
                (ProductionCIPOccurrenceDiscovery.centerAtom root).val)
              referencePosition = some ranking := by
  let center := (ProductionCIPOccurrenceDiscovery.centerAtom root).val
  have centerBound : center < mol.atomCount :=
    (ProductionCIPOccurrenceDiscovery.centerAtom root).isLt
  let hierarchy : DescriptorRule6HierarchySupport mol state (2 * mol.atomCount + 1) :=
    .ofLocalizedMancudeKekuleAdmissible mol state (2 * mol.atomCount + 1)
      wellFormed unique kekule
  have bonding : AuthoritativeCIPMoleculeCursorRanking.CanonicalCenterBondingNumberSix
      mol center :=
    AuthoritativeCIPValenceBondingNumber.canonicalCenterBondingNumberSix_of_valence
      mol center centerBound wellFormed unique valence
  have supported : ∀ cursor,
      cursor ∈ ProductionCIPOccurrenceDiscovery.ligandCursors root →
        CursorSupport mol (2 * mol.atomCount + 1) cursor :=
    productionLigandCursors_supported wellFormed writtenExact root bonding
      (2 * mol.atomCount + 1) (by rfl)
  rcases authoritativeRule6InitialPartition_exists_of_support hierarchy
      (ProductionCIPOccurrenceDiscovery.ligandCursors root)
      (ProductionCIPOccurrenceDiscovery.ligandCursors_length root) supported with
    ⟨sorted, adjacent, sortedEq, adjacentEq⟩
  refine ⟨sorted, adjacent, sortedEq, adjacentEq, ?_⟩
  intro referencePosition
  apply rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?_exists
  intro left right leftMember rightMember
  exact hierarchy.promoted_comparison_exists
    ((mol.ligandsWithLonePair center).getD referencePosition 0)
    (2 * mol.atomCount + 1) (by rfl) left right
    (supported left leftMember) (supported right rightMember)

theorem occurrenceLigandFrame_supported
    {mol : RawMolecule} {center : Nat} (centerBound : center < mol.atomCount)
    (wellFormed : mol.WellFormed)
    (bonding : AuthoritativeCIPMoleculeCursorRanking.CanonicalCenterBondingNumberSix mol center)
    {occurrence : CanonicalBranchNode}
    (occurrenceGenerated :
      AuthoritativeCIPMoleculeCursorRanking.CanonicalCenterTreeNode mol center occurrence)
    {roots : List CanonicalRerootCursor}
    (frameEq : occurrenceLigandFrame? mol occurrence = some roots) (fuel : Nat)
    (depthCovered : 2 * mol.atomCount + 1 ≤ fuel) :
    ∀ root, root ∈ roots → CursorSupport mol fuel root := by
  let ligands := mol.ligandsWithLonePair occurrence.atom
  let physical := occurrenceLigandCursors mol occurrence
  by_cases ligandsLength : ligands.length = 4
  · by_cases physicalFour : physical.length = 4
    · have rootsEq : roots = physical := by
        simpa [occurrenceLigandFrame?, ligands, physical, ligandsLength, physicalFour] using
          frameEq.symm
      subst roots
      intro root member
      exact (AuthoritativeCIPMoleculeCursorRanking.occurrenceLigandCursors_supported
        centerBound wellFormed bonding occurrenceGenerated root member).mono depthCovered
    · by_cases physicalThree : physical.length = 3
      · by_cases hasPhantom : ligands.contains mol.atomCount = true
        · have rootsEq : roots = physical ++
              [{ node := mol.canonicalPhantom occurrence.atom (occurrence.depth + 1)
                 previous? := some occurrence }] := by
            have resolved : mol.atomCount ∈ ligands ∧
                roots = physical ++
                  [{ node := mol.canonicalPhantom occurrence.atom (occurrence.depth + 1)
                     previous? := some occurrence }] := by
              simpa [occurrenceLigandFrame?, ligands, physical, ligandsLength, physicalFour,
                physicalThree, hasPhantom] using frameEq.symm
            exact resolved.2
          subst roots
          intro root member
          rcases List.mem_append.mp member with physicalMember | phantomMember
          · exact (AuthoritativeCIPMoleculeCursorRanking.occurrenceLigandCursors_supported
              centerBound wellFormed bonding occurrenceGenerated root physicalMember).mono
                depthCovered
          · have rootEq : root =
                { node := mol.canonicalPhantom occurrence.atom (occurrence.depth + 1)
                  previous? := some occurrence } := by
              simpa using phantomMember
            subst root
            apply CursorSupport.terminal
            simp [cursorTerminal, CanonicalRerootCursor.children,
              RawMolecule.canonicalPhantom, CanonicalBranchNode.forcedLeaf]
        · have contained : ligands.contains mol.atomCount = true := by
            have resolved : mol.atomCount ∈ ligands ∧
                roots = physical ++
                  [{ node := mol.canonicalPhantom occurrence.atom (occurrence.depth + 1)
                     previous? := some occurrence }] := by
              simpa [occurrenceLigandFrame?, ligands, physical, ligandsLength, physicalFour,
                physicalThree] using frameEq.symm
            simpa using resolved.1
          exact (hasPhantom contained).elim
      · simp [occurrenceLigandFrame?, ligands, physical, ligandsLength, physicalFour,
          physicalThree] at frameEq
  · simp [occurrenceLigandFrame?, ligands, ligandsLength] at frameEq

/-- Any recursively supported ligand frame makes every position-adapted promoted Rule-6 ranking
executable.  This is the support-level theorem used for lone-pair as well as physical frames. -/
theorem authoritativeOccurrenceRule6PositionRankingBackend_total_of_support
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    (hierarchy : DescriptorRule6HierarchySupport mol state fuel)
    (roots : List CanonicalRerootCursor)
    (supported : ∀ root, root ∈ roots → CursorSupport mol fuel root)
    (ligands : List Nat) :
    ∀ referencePosition,
      ∃ ranking,
        authoritativeOccurrenceRule6PositionRankingBackend
          mol state fuel roots ligands referencePosition = some ranking := by
  intro referencePosition
  apply rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?_exists
  intro left right leftMember rightMember
  exact hierarchy.promoted_comparison_exists (ligands.getD referencePosition 0)
    fuel (by rfl) left right (supported left leftMember) (supported right rightMember)

/-- Chemical applicability therefore makes the exact P-92 backend total on the actual normalized
four-ligand frame, including a possible lone-pair phantom. -/
theorem authoritativeOccurrenceRule6PositionRankingBackend_total_of_chemical_frame
    {mol : RawMolecule} {state : OccurrenceAuxState} {center : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (valence : mol.ValenceOK)
    (kekule : AuthoritativeCIPMancudeTotality.LocalizedMancudeKekuleAdmissible mol)
    {occurrence : CanonicalBranchNode}
    (occurrenceGenerated :
      AuthoritativeCIPMoleculeCursorRanking.CanonicalCenterTreeNode mol center occurrence)
    {roots : List CanonicalRerootCursor}
    (frameEq : occurrenceLigandFrame? mol occurrence = some roots)
    (ligands : List Nat) :
    ∀ referencePosition,
      ∃ ranking,
        authoritativeOccurrenceRule6PositionRankingBackend mol state
          (2 * mol.atomCount + 1) roots ligands referencePosition = some ranking := by
  let hierarchy : DescriptorRule6HierarchySupport mol state (2 * mol.atomCount + 1) :=
    .ofLocalizedMancudeKekuleAdmissible mol state (2 * mol.atomCount + 1)
      wellFormed unique kekule
  have bonding :
      AuthoritativeCIPMoleculeCursorRanking.CanonicalCenterBondingNumberSix mol center :=
    AuthoritativeCIPValenceBondingNumber.canonicalCenterBondingNumberSix_of_valence
      mol center centerBound wellFormed unique valence
  apply authoritativeOccurrenceRule6PositionRankingBackend_total_of_support
    hierarchy roots
  exact occurrenceLigandFrame_supported centerBound wellFormed bonding occurrenceGenerated
    frameEq (2 * mol.atomCount + 1) (by rfl)

/-- Chemical applicability also discharges every operational lookup/comparison in the initial
Rules-1a--5 partition of the normalized four-ligand frame. -/
theorem authoritativeRule6InitialPartition_exists_of_chemical_frame
    {mol : RawMolecule} {state : OccurrenceAuxState} {center : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (valence : mol.ValenceOK)
    (kekule : AuthoritativeCIPMancudeTotality.LocalizedMancudeKekuleAdmissible mol)
    {occurrence : CanonicalBranchNode}
    (occurrenceGenerated :
      AuthoritativeCIPMoleculeCursorRanking.CanonicalCenterTreeNode mol center occurrence)
    {roots : List CanonicalRerootCursor}
    (frameEq : occurrenceLigandFrame? mol occurrence = some roots) :
    ∃ sorted adjacent,
      sortAuthoritativeRule6InitialPositions? mol state (2 * mol.atomCount + 1)
          roots (List.range 4) = some sorted ∧
        compareAuthoritativeRule6InitialAdjacent? mol state (2 * mol.atomCount + 1)
          roots sorted = some adjacent := by
  let hierarchy : DescriptorRule6HierarchySupport mol state (2 * mol.atomCount + 1) :=
    .ofLocalizedMancudeKekuleAdmissible mol state (2 * mol.atomCount + 1)
      wellFormed unique kekule
  have bonding :
      AuthoritativeCIPMoleculeCursorRanking.CanonicalCenterBondingNumberSix mol center :=
    AuthoritativeCIPValenceBondingNumber.canonicalCenterBondingNumberSix_of_valence
      mol center centerBound wellFormed unique valence
  apply authoritativeRule6InitialPartition_exists_of_support hierarchy roots
    (occurrenceLigandFrame?_result_length mol occurrence roots frameEq)
  exact occurrenceLigandFrame_supported centerBound wellFormed bonding occurrenceGenerated
    frameEq (2 * mol.atomCount + 1) (by rfl)

/-- Independent descriptor meaning of the three admitted P-92 Rule-6 partition shapes. -/
def AuthoritativeRule6BranchDescriptorJudgment
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (sorted : List Nat) (adjacent : List (Option Ordering))
    (groupCount : Nat) (descriptor : RS) : Prop :=
  sorted.Perm (List.range 4) ∧ adjacent.length = 3 ∧
    some Ordering.lt ∉ adjacent ∧
    ((groupCount = 1 ∧
        AuthoritativeFourWayDescriptorJudgment backend parity sorted descriptor) ∨
    (groupCount = 2 ∧
        CommonRule6Descriptor backend parity
          (rule6EquivalentReferencePositions sorted adjacent) descriptor) ∨
    (groupCount = 3 ∧
        CommonRule6Descriptor backend parity
          (rule6ThreeGroupReferencePositions sorted) (RS.swap descriptor)))

/-- A single exact result path for P-92 Rule 6.  There is no bounded production comparator and
no first-reference fallback: two-group candidates all agree, the three-group singleton is
reversed, and the four-way branch uses its dependent second reference. -/
def authoritativeOccurrenceRule6Result? (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor) :
    Option OccurrenceRule6Result := do
  let spec ← mol.atomAt? node.atom
  let parity ← spec.tetrahedral?
  let ligands := mol.ligandsWithLonePair node.atom
  if ligands.length != 4 || roots.length != 4 then none else
  let sorted ← sortAuthoritativeRule6InitialPositions? mol state fuel roots (List.range 4)
  let adjacent ← compareAuthoritativeRule6InitialAdjacent? mol state fuel roots sorted
  if adjacent.contains (some Ordering.lt) then none else
  let groupCount := rule6GroupCount adjacent
  let initialBefore := fun left right =>
    (compareAuthoritativeRule6InitialPositions? mol state fuel roots left right).any
      fun decision => decision.ordering = Ordering.eq
  let oddTopology? :=
    hasOddConstitutionAutomorphismAtCenter mol node.atom ligands initialBefore
  if oddTopology? != some false then none else
  let backend := authoritativeOccurrenceRule6PositionRankingBackend
    mol state fuel roots ligands
  if groupCount == 1 then
    let agreement ← authoritativeOccurrenceRule6FourWayAgreement? backend parity sorted
    some
      { fact :=
          { key := canonicalOccurrenceKey node
            atom := node.atom
            descriptor := agreement.descriptor
            uppercase := agreement.secondRanking.pseudoComparisons != 1
            priorityPositions := agreement.secondRanking.positions }
        parity := parity
        ligands := ligands
        roots := roots
        sorted := sorted
        adjacent := adjacent
        groupCount := groupCount
        oddTopology? := oddTopology?
        carrier := .fourWay agreement }
  else if groupCount == 2 then
    let references := rule6EquivalentReferencePositions sorted adjacent
    let ranking ← rankProductionRule6EquivalentReferencesWithBackend?
      backend parity references
    some
      { fact :=
          { key := canonicalOccurrenceKey node
            atom := node.atom
            descriptor := RawMolecule.descriptorOfParity parity
              (RawMolecule.permutationIsEven ranking.positions)
            uppercase := ranking.pseudoComparisons != 1
            priorityPositions := ranking.positions }
        parity := parity
        ligands := ligands
        roots := roots
        sorted := sorted
        adjacent := adjacent
        groupCount := groupCount
        oddTopology? := oddTopology?
        carrier := .twoGroup references ranking }
  else if groupCount == 3 then
    let reference := sorted[1]?.getD 0
    let referenceRoot ← roots[reference]?
    if adjacent[1]?.getD none != some Ordering.eq ||
        !occurrenceBranchHasLocalReference (mol := mol) state fuel [referenceRoot] then none else
    let ranking ← rankProductionRule6EquivalentReferencesWithBackend?
      backend parity [reference]
    some
      { fact :=
          { key := canonicalOccurrenceKey node
            atom := node.atom
            descriptor := RS.swap (RawMolecule.descriptorOfParity parity
              (RawMolecule.permutationIsEven ranking.positions))
            uppercase := true
            priorityPositions := ranking.positions }
        parity := parity
        ligands := ligands
        roots := roots
        sorted := sorted
        adjacent := adjacent
        groupCount := groupCount
        oddTopology? := oddTopology?
        carrier := .threeGroup reference ranking }
  else none

/-- Every descriptor emitted by the uncapped scheduler satisfies the corresponding independent
P-92 two-, three-, or dependent four-reference judgment. -/
theorem authoritativeOccurrenceRule6Result?_sound
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (result : OccurrenceRule6Result)
    (computed : authoritativeOccurrenceRule6Result? mol state fuel node roots = some result) :
    AuthoritativeRule6BranchDescriptorJudgment
      (authoritativeOccurrenceRule6PositionRankingBackend
        mol state fuel result.roots result.ligands)
      result.parity result.sorted result.adjacent result.groupCount result.fact.descriptor := by
  cases atomEq : mol.atomAt? node.atom with
  | none => simp [authoritativeOccurrenceRule6Result?, atomEq] at computed
  | some spec =>
      cases parityEq : spec.tetrahedral? with
      | none => simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq] at computed
      | some parity =>
          let ligands := mol.ligandsWithLonePair node.atom
          by_cases ligandsLength : ligands.length = 4
          · by_cases rootsLength : roots.length = 4
            · cases sortedEq : sortAuthoritativeRule6InitialPositions?
                  mol state fuel roots (List.range 4) with
              | none =>
                  simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
                    ligandsLength, rootsLength, sortedEq] at computed
              | some sorted =>
                cases adjacentEq : compareAuthoritativeRule6InitialAdjacent?
                    mol state fuel roots sorted with
                | none =>
                    simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
                      ligandsLength, rootsLength, sortedEq, adjacentEq] at computed
                | some adjacent =>
                  by_cases adjacentNotLt : some Ordering.lt ∉ adjacent
                  · have sortedPerm : sorted.Perm (List.range 4) :=
                      sortAuthoritativeRule6InitialPositions?_perm
                        mol state fuel roots (List.range 4) sorted sortedEq
                    have sortedLength : sorted.length = 4 := by
                      simpa using sortedPerm.length_eq
                    have adjacentLength : adjacent.length = 3 := by
                      have traversed := compareAuthoritativeRule6InitialAdjacent?_length
                        mol state fuel roots sorted adjacent adjacentEq
                      simpa [sortedLength] using traversed
                    let groupCount := rule6GroupCount adjacent
                    let initialBefore := fun left right =>
                      (compareAuthoritativeRule6InitialPositions?
                        mol state fuel roots left right).any
                        fun decision => decision.ordering = Ordering.eq
                    let oddTopology? :=
                      hasOddConstitutionAutomorphismAtCenter
                        mol node.atom ligands initialBefore
                    by_cases oddFalse : oddTopology? = some false
                    · let backend := authoritativeOccurrenceRule6PositionRankingBackend
                        mol state fuel roots ligands
                      by_cases groupOne : groupCount = 1
                      · cases agreementEq : authoritativeOccurrenceRule6FourWayAgreement?
                            backend parity sorted with
                        | none =>
                            simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
                              ligandsLength, rootsLength, sortedEq, adjacentEq, adjacentNotLt,
                              groupCount, initialBefore, oddTopology?, oddFalse, backend,
                              groupOne, agreementEq] at computed
                        | some agreement =>
                            have resultEq : result =
                                { fact :=
                                    { key := canonicalOccurrenceKey node
                                      atom := node.atom
                                      descriptor := agreement.descriptor
                                      uppercase := agreement.secondRanking.pseudoComparisons != 1
                                      priorityPositions := agreement.secondRanking.positions }
                                  parity := parity
                                  ligands := ligands
                                  roots := roots
                                  sorted := sorted
                                  adjacent := adjacent
                                  groupCount := groupCount
                                  oddTopology? := oddTopology?
                                  carrier := .fourWay agreement } := by
                              simpa [authoritativeOccurrenceRule6Result?, atomEq, parityEq,
                                ligands, ligandsLength, rootsLength, sortedEq, adjacentEq,
                                adjacentNotLt, groupCount, initialBefore, oddTopology?, oddFalse,
                                backend, groupOne, agreementEq] using computed.symm
                            subst result
                            refine ⟨sortedPerm, adjacentLength, adjacentNotLt,
                              Or.inl ⟨groupOne, ?_⟩⟩
                            apply
                              (authoritativeOccurrenceRule6FourWayDescriptor?_eq_some_iff_judgment
                                backend parity sorted agreement.descriptor).mp
                            simp [authoritativeOccurrenceRule6FourWayDescriptor?, agreementEq]
                      · by_cases groupTwo : groupCount = 2
                        · let references := rule6EquivalentReferencePositions sorted adjacent
                          cases rankingEq : rankProductionRule6EquivalentReferencesWithBackend?
                              backend parity references with
                          | none =>
                              simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq,
                                ligands, ligandsLength, rootsLength, sortedEq, adjacentEq,
                                adjacentNotLt, groupCount, initialBefore, oddTopology?, oddFalse,
                                backend, groupOne, groupTwo, references, rankingEq] at computed
                          | some ranking =>
                              have resultEq : result =
                                  { fact :=
                                      { key := canonicalOccurrenceKey node
                                        atom := node.atom
                                        descriptor := RawMolecule.descriptorOfParity parity
                                          (RawMolecule.permutationIsEven ranking.positions)
                                        uppercase := ranking.pseudoComparisons != 1
                                        priorityPositions := ranking.positions }
                                    parity := parity
                                    ligands := ligands
                                    roots := roots
                                    sorted := sorted
                                    adjacent := adjacent
                                    groupCount := groupCount
                                    oddTopology? := oddTopology?
                                    carrier := .twoGroup references ranking } := by
                                simpa [authoritativeOccurrenceRule6Result?, atomEq, parityEq,
                                  ligands, ligandsLength, rootsLength, sortedEq, adjacentEq,
                                  adjacentNotLt, groupCount, initialBefore, oddTopology?, oddFalse,
                                  backend, groupOne, groupTwo, references, rankingEq] using
                                    computed.symm
                              subst result
                              rcases
                                  rankProductionRule6EquivalentReferencesWithBackend?_sound
                                    backend parity references ranking rankingEq with
                                ⟨certificate⟩
                              have referencesNonempty : references ≠ [] := by
                                intro empty
                                simpa [empty] using certificate.reference_head
                              exact ⟨sortedPerm, adjacentLength, adjacentNotLt,
                                Or.inr (Or.inl
                                  ⟨groupTwo, referencesNonempty,
                                    certificate.all_references⟩)⟩
                        · by_cases groupThree : groupCount = 3
                          · let reference := sorted[1]?.getD 0
                            cases referenceRootEq : roots[reference]? with
                            | none =>
                                simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq,
                                  ligands, ligandsLength, rootsLength, sortedEq, adjacentEq,
                                  adjacentNotLt, groupCount, initialBefore, oddTopology?, oddFalse,
                                  backend, groupOne, groupTwo, groupThree, reference,
                                  referenceRootEq] at computed
                            | some referenceRoot =>
                              by_cases middleTie : adjacent[1]?.getD none = some Ordering.eq
                              · by_cases localReference : occurrenceBranchHasLocalReference
                                    (mol := mol) state fuel [referenceRoot] = true
                                · cases rankingEq :
                                      rankProductionRule6EquivalentReferencesWithBackend?
                                        backend parity [reference] with
                                  | none =>
                                      simp [authoritativeOccurrenceRule6Result?, atomEq,
                                        parityEq, ligands, ligandsLength, rootsLength, sortedEq,
                                        adjacentEq, adjacentNotLt, groupCount, initialBefore,
                                        oddTopology?, oddFalse, backend, groupOne, groupTwo,
                                        groupThree, reference, referenceRootEq, middleTie,
                                        localReference, rankingEq] at computed
                                  | some ranking =>
                                      have resultEq : result =
                                          { fact :=
                                              { key := canonicalOccurrenceKey node
                                                atom := node.atom
                                                descriptor := RS.swap
                                                  (RawMolecule.descriptorOfParity parity
                                                    (RawMolecule.permutationIsEven
                                                      ranking.positions))
                                                uppercase := true
                                                priorityPositions := ranking.positions }
                                            parity := parity
                                            ligands := ligands
                                            roots := roots
                                            sorted := sorted
                                            adjacent := adjacent
                                            groupCount := groupCount
                                            oddTopology? := oddTopology?
                                            carrier := .threeGroup reference ranking } := by
                                        simpa [authoritativeOccurrenceRule6Result?, atomEq,
                                          parityEq, ligands, ligandsLength, rootsLength, sortedEq,
                                          adjacentEq, adjacentNotLt, groupCount, initialBefore,
                                          oddTopology?, oddFalse, backend, groupOne, groupTwo,
                                          groupThree, reference, referenceRootEq, middleTie,
                                          localReference, rankingEq] using computed.symm
                                      subst result
                                      rcases
                                          rankProductionRule6EquivalentReferencesWithBackend?_sound
                                            backend parity [reference] ranking rankingEq with
                                        ⟨certificate⟩
                                      have commonBase : CommonRule6Descriptor backend parity
                                          [reference]
                                          (RawMolecule.descriptorOfParity parity
                                            (RawMolecule.permutationIsEven ranking.positions)) :=
                                        ⟨by simp, certificate.all_references⟩
                                      exact ⟨sortedPerm, adjacentLength, adjacentNotLt,
                                        Or.inr (Or.inr ⟨groupThree, by
                                          simpa [rule6ThreeGroupReferencePositions, reference,
                                            rs_swap_involutive] using commonBase⟩)⟩
                                · simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq,
                                    ligands, ligandsLength, rootsLength, sortedEq, adjacentEq,
                                    adjacentNotLt, groupCount, initialBefore, oddTopology?,
                                    oddFalse, backend, groupOne, groupTwo, groupThree, reference,
                                    referenceRootEq, middleTie, localReference] at computed
                              · simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq,
                                  ligands, ligandsLength, rootsLength, sortedEq, adjacentEq,
                                  adjacentNotLt, groupCount, initialBefore, oddTopology?, oddFalse,
                                  backend, groupOne, groupTwo, groupThree, reference,
                                  referenceRootEq, middleTie] at computed
                          · simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
                              ligandsLength, rootsLength, sortedEq, adjacentEq, adjacentNotLt,
                              groupCount, initialBefore, oddTopology?, oddFalse, backend, groupOne,
                              groupTwo, groupThree] at computed
                    · simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
                        ligandsLength, rootsLength, sortedEq, adjacentEq, adjacentNotLt,
                        groupCount, initialBefore, oddTopology?, oddFalse] at computed
                  · simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
                      ligandsLength, rootsLength, sortedEq, adjacentEq, adjacentNotLt] at computed
            · simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
                ligandsLength, rootsLength] at computed
          · simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
              ligandsLength] at computed

/-! ## Final production-scheduler bridge -/

/-- Rule-6 label construction with the legacy bounded result evaluator replaced by the exact
uncapped scheduler above. -/
def authoritativeRule6Label? {mol : RawMolecule}
    (discovery : ProductionCIPOccurrenceDiscovery.Discovery mol)
    (fuel : Nat) (state : State discovery) (target : Occurrence discovery) :
    Option (Label discovery) := do
  match frameEq : target.node with
  | .inr _ => none
  | .inl marker =>
      let aux ← executableStateFor? discovery state target
      let roots ← targetLigandFrame? discovery target
      let result ← authoritativeOccurrenceRule6Result? mol aux fuel
        (sourceNode discovery target) roots
      some (labelOfFinalFact discovery target result.fact marker frameEq)

theorem authoritativeRule6Label?_eq_some_iff {mol : RawMolecule}
    (discovery : ProductionCIPOccurrenceDiscovery.Discovery mol)
    (fuel : Nat) (state : State discovery)
    (target : Occurrence discovery) (label : Label discovery) :
    authoritativeRule6Label? discovery fuel state target = some label ↔
      ∃ marker,
        ∃ frameEq : target.node = Sum.inl marker,
          ∃ aux roots result,
            executableStateFor? discovery state target = some aux ∧
            targetLigandFrame? discovery target = some roots ∧
            authoritativeOccurrenceRule6Result? mol aux fuel
                (sourceNode discovery target) roots = some result ∧
            labelOfFinalFact discovery target result.fact marker frameEq = label := by
  rcases target with ⟨root, node⟩
  rcases node with marker | branch
  · cases auxEq : executableStateFor? discovery state
        { root := root, node := Sum.inl marker } with
    | none => simp [authoritativeRule6Label?, auxEq]
    | some aux =>
        cases rootsEq : targetLigandFrame? discovery
            { root := root, node := Sum.inl marker } with
        | none => simp [authoritativeRule6Label?, auxEq, rootsEq]
        | some roots =>
            cases resultEq : authoritativeOccurrenceRule6Result? mol aux fuel
                (sourceNode discovery { root := root, node := Sum.inl marker }) roots with
            | none => simp [authoritativeRule6Label?, auxEq, rootsEq, resultEq]
            | some result =>
                have finalEquation : authoritativeRule6Label? discovery fuel state
                    { root := root, node := Sum.inl marker } =
                      some (labelOfFinalFact discovery
                        { root := root, node := Sum.inl marker } result.fact marker rfl) := by
                  simp [authoritativeRule6Label?, auxEq, rootsEq, resultEq]
                constructor
                · intro accepted
                  have labelEq := Option.some.inj (finalEquation.symm.trans accepted)
                  exact ⟨marker, rfl, aux, roots, result, rfl, rfl, resultEq, labelEq⟩
                · rintro ⟨otherMarker, frameEq, otherAux, otherRoots, otherResult,
                    otherAuxEq, otherRootsEq, otherResultEq, labelEq⟩
                  have auxEqual := Option.some.inj otherAuxEq
                  subst otherAux
                  have rootsEqual := Option.some.inj otherRootsEq
                  subst otherRoots
                  have resultEqual := Option.some.inj (otherResultEq.symm.trans resultEq)
                  subst otherResult
                  have markerEq : otherMarker = marker := Subsingleton.elim _ _
                  subst otherMarker
                  exact finalEquation.trans (congrArg some labelEq)
  · simp [authoritativeRule6Label?]

/-- The public label layer preserves the exact branch judgment: no descriptor can be introduced
or changed while packaging the uncapped Rule-6 fact as a final production label. -/
theorem authoritativeRule6Label?_sound {mol : RawMolecule}
    (discovery : ProductionCIPOccurrenceDiscovery.Discovery mol)
    (fuel : Nat) (state : State discovery)
    (target : Occurrence discovery) (label : Label discovery)
    (computed : authoritativeRule6Label? discovery fuel state target = some label) :
    ∃ aux roots result,
      authoritativeOccurrenceRule6Result? mol aux fuel
          (sourceNode discovery target) roots = some result ∧
      label.fact = result.fact ∧
      AuthoritativeRule6BranchDescriptorJudgment
        (authoritativeOccurrenceRule6PositionRankingBackend
          mol aux fuel result.roots result.ligands)
        result.parity result.sorted result.adjacent result.groupCount label.fact.descriptor := by
  rcases (authoritativeRule6Label?_eq_some_iff
      discovery fuel state target label).mp computed with
    ⟨marker, frameEq, aux, roots, result, _auxEq, _rootsEq, resultEq, labelEq⟩
  have factEq : label.fact = result.fact :=
    (congrArg Label.fact labelEq).symm
  refine ⟨aux, roots, result, resultEq, factEq, ?_⟩
  rw [factEq]
  exact authoritativeOccurrenceRule6Result?_sound mol aux fuel
    (sourceNode discovery target) roots result resultEq

/-- Combined final evaluator retaining ordinary-rule precedence while replacing only the Rule-6
fallback with the uncapped exact path. -/
def authoritativeDerive? {mol : RawMolecule}
    (discovery : ProductionCIPOccurrenceDiscovery.Discovery mol)
    (fuel : Nat) (state : State discovery) (target : Occurrence discovery) :
    Option (Label discovery) :=
  match ordinaryLabel? discovery fuel state target with
  | some label => some label
  | none => authoritativeRule6Label? discovery fuel state target

/-- Whenever ordinary Rules 4b/5 are silent, every label emitted by the combined replacement
scheduler is certified by the exact P-92 Rule-6 branch judgment. -/
theorem authoritativeDerive?_rule6_sound {mol : RawMolecule}
    (discovery : ProductionCIPOccurrenceDiscovery.Discovery mol)
    (fuel : Nat) (state : State discovery)
    (target : Occurrence discovery) (label : Label discovery)
    (ordinaryNone : ordinaryLabel? discovery fuel state target = none)
    (computed : authoritativeDerive? discovery fuel state target = some label) :
    ∃ aux roots result,
      authoritativeOccurrenceRule6Result? mol aux fuel
          (sourceNode discovery target) roots = some result ∧
      label.fact = result.fact ∧
      AuthoritativeRule6BranchDescriptorJudgment
        (authoritativeOccurrenceRule6PositionRankingBackend
          mol aux fuel result.roots result.ligands)
        result.parity result.sorted result.adjacent result.groupCount label.fact.descriptor := by
  apply authoritativeRule6Label?_sound discovery fuel state target label
  simpa [authoritativeDerive?, ordinaryNone] using computed

theorem authoritativeRule6Label?_eq_of_depth_agree {mol : RawMolecule}
    (discovery : ProductionCIPOccurrenceDiscovery.Discovery mol)
    (fuel : Nat) {left right : State discovery} (target : Occurrence discovery)
    (agree : ∀ source, DepthDependency source target → left source = right source) :
    authoritativeRule6Label? discovery fuel left target =
      authoritativeRule6Label? discovery fuel right target := by
  unfold authoritativeRule6Label?
  rw [executableStateFor?_eq_of_depth_agree discovery target agree]

theorem authoritativeDerive?_eq_of_depth_agree {mol : RawMolecule}
    (discovery : ProductionCIPOccurrenceDiscovery.Discovery mol)
    (fuel : Nat) {left right : State discovery} (target : Occurrence discovery)
    (agree : ∀ source, DepthDependency source target → left source = right source) :
    authoritativeDerive? discovery fuel left target =
      authoritativeDerive? discovery fuel right target := by
  have ordinaryEq := ordinaryLabel?_eq_of_depth_agree discovery fuel target agree
  have rule6Eq := authoritativeRule6Label?_eq_of_depth_agree discovery fuel target agree
  unfold authoritativeDerive?
  rw [ordinaryEq]
  cases ordinaryLabel? discovery fuel right target <;> simp [rule6Eq]

/-- Proof-relevant declarative clauses for the scheduler with the authoritative Rule-6 branch. -/
inductive AuthoritativeDerivation {mol : RawMolecule}
    (discovery : ProductionCIPOccurrenceDiscovery.Discovery mol)
    (fuel : Nat) (state : State discovery) (target : Occurrence discovery) :
    Option (Label discovery) → Prop
  | ordinary {label : Label discovery} :
      OrdinaryDerivation (mol := mol) discovery fuel state target label →
      AuthoritativeDerivation discovery fuel state target (some label)
  | rule6 {label : Label discovery} :
      NoOrdinaryDerivation (mol := mol) discovery fuel state target →
      authoritativeRule6Label? discovery fuel state target = some label →
      AuthoritativeDerivation discovery fuel state target (some label)
  | noLabel :
      NoOrdinaryDerivation (mol := mol) discovery fuel state target →
      authoritativeRule6Label? discovery fuel state target = none →
      AuthoritativeDerivation discovery fuel state target none

theorem authoritativeDerivation_iff_derive? {mol : RawMolecule}
    (discovery : ProductionCIPOccurrenceDiscovery.Discovery mol)
    (fuel : Nat) (state : State discovery) (target : Occurrence discovery)
    (outcome : Option (Label discovery)) :
    AuthoritativeDerivation discovery fuel state target outcome ↔
      authoritativeDerive? discovery fuel state target = outcome := by
  constructor
  · intro derived
    cases derived with
    | ordinary ordinary =>
        have accepted := (ordinaryDerivation_iff discovery fuel state target _).1 ordinary
        simp [authoritativeDerive?, accepted]
    | rule6 ordinaryAbsent accepted =>
        have ordinaryNone :=
          (noOrdinaryDerivation_iff discovery fuel state target).1 ordinaryAbsent
        simp [authoritativeDerive?, ordinaryNone, accepted]
    | noLabel ordinaryAbsent rule6None =>
        have ordinaryNone :=
          (noOrdinaryDerivation_iff discovery fuel state target).1 ordinaryAbsent
        simp [authoritativeDerive?, ordinaryNone, rule6None]
  · intro equation
    cases ordinaryEq : ordinaryLabel? discovery fuel state target with
    | some label =>
        have ordinary :=
          (ordinaryDerivation_iff discovery fuel state target label).2 ordinaryEq
        have derived : AuthoritativeDerivation discovery fuel state target (some label) :=
          .ordinary ordinary
        rwa [← equation, authoritativeDerive?, ordinaryEq]
    | none =>
        have ordinaryAbsent : NoOrdinaryDerivation (mol := mol)
            discovery fuel state target :=
          (noOrdinaryDerivation_iff discovery fuel state target).2 ordinaryEq
        cases rule6Eq : authoritativeRule6Label? discovery fuel state target with
        | some label =>
            have derived : AuthoritativeDerivation discovery fuel state target (some label) :=
              .rule6 ordinaryAbsent rule6Eq
            rwa [← equation, authoritativeDerive?, ordinaryEq, rule6Eq]
        | none =>
            have derived : AuthoritativeDerivation discovery fuel state target none :=
              .noLabel ordinaryAbsent rule6Eq
            rwa [← equation, authoritativeDerive?, ordinaryEq, rule6Eq]

/-- The well-founded occurrence system whose final Rule-6 branch is the uncapped exact evaluator. -/
def authoritativeOccurrenceSystem {mol : RawMolecule}
    (discovery : ProductionCIPOccurrenceDiscovery.Discovery mol) (fuel : Nat) :
    OccurrenceSystem (ProductionCIPOccurrenceDiscovery.FinalUnit mol)
      (Occurrence discovery) (Label discovery) where
  finalOccurrence := ProductionCIPOccurrenceDiscovery.finalOccurrence discovery
  descriptorOf := Label.descriptor
  DeclarativeDerivation := fun state target outcome =>
    AuthoritativeDerivation discovery fuel state target outcome
  executableStep := fun state target => authoritativeDerive? discovery fuel state target

theorem authoritativeDerivationStepCorrespondence {mol : RawMolecule}
    (discovery : ProductionCIPOccurrenceDiscovery.Discovery mol) (fuel : Nat) :
    (authoritativeOccurrenceSystem discovery fuel).DerivationStepCorrespondence := by
  intro state target outcome
  exact authoritativeDerivation_iff_derive? discovery fuel state target outcome

theorem authoritativeEvaluatorLocalFor_depthDependency {mol : RawMolecule}
    (discovery : ProductionCIPOccurrenceDiscovery.Discovery mol) (fuel : Nat) :
    (authoritativeOccurrenceSystem discovery fuel).EvaluatorLocalFor
      (@DepthDependency mol discovery) := by
  intro left right target agree
  exact authoritativeDerive?_eq_of_depth_agree discovery fuel target agree

/-- The replacement scheduler has one and only one complete occurrence model. -/
theorem existsUnique_authoritativeCIPModel {mol : RawMolecule}
    (discovery : ProductionCIPOccurrenceDiscovery.Discovery mol) (fuel : Nat) :
    ∃! state, (authoritativeOccurrenceSystem discovery fuel).CIPModel state :=
  (authoritativeOccurrenceSystem discovery fuel).existsUnique_cipModel_of_wellFounded
    (authoritativeDerivationStepCorrespondence discovery fuel)
    (@DepthDependency mol discovery)
    (depthDependency_wellFounded discovery)
    (authoritativeEvaluatorLocalFor_depthDependency discovery fuel)

/-- The dependency-ready monotone closure decodes to that unique authoritative occurrence model. -/
theorem authoritativeSchedulerClosure_cipModel {mol : RawMolecule}
    (discovery : ProductionCIPOccurrenceDiscovery.Discovery mol) (fuel : Nat) :
    (authoritativeOccurrenceSystem discovery fuel).CIPModel
      (OccurrenceScheduler.decode (authoritativeOccurrenceSystem discovery fuel)
        (@DepthDependency mol discovery)
        (OccurrenceScheduler.closure (authoritativeOccurrenceSystem discovery fuel)
          (@DepthDependency mol discovery))) := by
  exact OccurrenceScheduler.decode_closure_cipModel
    (authoritativeOccurrenceSystem discovery fuel)
    (authoritativeDerivationStepCorrespondence discovery fuel)
    (@DepthDependency mol discovery)
    (depthDependency_wellFounded discovery)
    (authoritativeEvaluatorLocalFor_depthDependency discovery fuel)

/-- Every assignment in the complete replacement model is either an independently certified
ordinary derivation or an exact P-92 Rule-6 branch result. -/
theorem authoritativeModel_assignment_certified_at {mol : RawMolecule}
    (discovery : ProductionCIPOccurrenceDiscovery.Discovery mol) (fuel : Nat)
    {state : State discovery}
    (model : (authoritativeOccurrenceSystem discovery fuel).CIPModel state)
    (target : Occurrence discovery) (label : Label discovery)
    (assigned : state target = some label) :
    OrdinaryDerivation (mol := mol) discovery fuel state target label ∨
      ∃ aux roots result,
        authoritativeOccurrenceRule6Result? mol aux fuel
            (sourceNode discovery target) roots = some result ∧
        label.fact = result.fact ∧
        AuthoritativeRule6BranchDescriptorJudgment
          (authoritativeOccurrenceRule6PositionRankingBackend
            mol aux fuel result.roots result.ligands)
          result.parity result.sorted result.adjacent result.groupCount
            label.fact.descriptor := by
  have derived : AuthoritativeDerivation discovery fuel state target (some label) := by
    simpa [authoritativeOccurrenceSystem, assigned] using model target
  cases derived with
  | ordinary ordinary => exact Or.inl ordinary
  | rule6 _ordinaryAbsent accepted =>
      exact Or.inr (authoritativeRule6Label?_sound
        discovery fuel state target label accepted)

/-- At a target where the ordinary evaluator returns no label, a complete-model assignment is
necessarily an exact authoritative Rule-6 assignment. -/
theorem authoritativeModel_rule6_assignment_sound {mol : RawMolecule}
    (discovery : ProductionCIPOccurrenceDiscovery.Discovery mol) (fuel : Nat)
    {state : State discovery}
    (model : (authoritativeOccurrenceSystem discovery fuel).CIPModel state)
    (target : Occurrence discovery) (label : Label discovery)
    (assigned : state target = some label)
    (ordinaryNone : ordinaryLabel? discovery fuel state target = none) :
    ∃ aux roots result,
      authoritativeOccurrenceRule6Result? mol aux fuel
          (sourceNode discovery target) roots = some result ∧
      label.fact = result.fact ∧
      AuthoritativeRule6BranchDescriptorJudgment
        (authoritativeOccurrenceRule6PositionRankingBackend
          mol aux fuel result.roots result.ligands)
        result.parity result.sorted result.adjacent result.groupCount label.fact.descriptor := by
  rcases authoritativeModel_assignment_certified_at discovery fuel model target label assigned with
    ordinary | rule6
  · have accepted := (ordinaryDerivation_iff discovery fuel state target label).1 ordinary
    rw [ordinaryNone] at accepted
    simp at accepted
  · exact rule6

end TetraStereo.OneCenter.AuthoritativeCIPRule6Scheduler
