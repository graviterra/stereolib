import TetraStereo.OneCenter.CIPAuthoritativeRule6Scheduler

set_option autoImplicit false

namespace TetraStereo.OneCenter

open ProductionCIPOccurrenceDiscovery
open AuthoritativeCIPCursorSupport
open AuthoritativeCIPMoleculeCursorRanking
open AuthoritativeCIPMancudeTotality

namespace RawMolecule

/-!
# Totality of width-unbounded authoritative branch discovery

The authoritative branch compiler has no global node or frontier-width budget, but its executable
result is still optional: Rule 1a may lack a chemically justified mancude label, a local canonical
node may exceed the P-92 bonding-number-six domain, or sorting may encounter an incomplete child
key.  This module proves that those are the only relevant failure modes on molecule-derived ligand
branches and discharges them from independent chemical premises.
-/

/-- Complete keys can always be compared by the safe executable comparator. -/
theorem compareCanonicalBranchKeys?_exists_of_complete
    (left right : CanonicalBranchKey)
    (leftComplete : left.complete = true) (rightComplete : right.complete = true) :
    ∃ outcome, compareCanonicalBranchKeys? left right = some outcome := by
  unfold compareCanonicalBranchKeys?
  cases rule1a : compareSparseCanonicalLayers compareCIPAtomicLabel left.rule1a right.rule1a with
  | lt => exact ⟨.lt, rfl⟩
  | gt => exact ⟨.gt, rfl⟩
  | eq => exact ⟨compareCanonicalBranchKeys left right, by
      simp [leftComplete, rightComplete]⟩

private theorem insertCanonicalKey?_exists_of_complete
    (key : CanonicalBranchKey) (keyComplete : key.complete = true) :
    ∀ keys : List CanonicalBranchKey, keys.all (·.complete) = true →
      ∃ result, insertCanonicalKey? key keys = some result := by
  intro keys
  induction keys with
  | nil =>
      intro _
      exact ⟨[key], rfl⟩
  | cons head tail inductionHypothesis =>
      intro allComplete
      have completeClauses : head.complete = true ∧ tail.all (·.complete) = true := by
        simpa using allComplete
      obtain ⟨decision, compared⟩ :=
        compareCanonicalBranchKeys?_exists_of_complete key head
          keyComplete completeClauses.1
      cases decision with
      | gt => exact ⟨key :: head :: tail, by simp [insertCanonicalKey?, compared]⟩
      | eq => exact ⟨key :: head :: tail, by simp [insertCanonicalKey?, compared]⟩
      | lt =>
          obtain ⟨inserted, insertedEq⟩ := inductionHypothesis completeClauses.2
          exact ⟨head :: inserted, by simp [insertCanonicalKey?, compared, insertedEq]⟩

/-- Sorting is total whenever every input key is complete. -/
theorem sortCanonicalKeys?_exists_of_all_complete :
    ∀ keys : List CanonicalBranchKey, keys.all (·.complete) = true →
      ∃ sorted, sortCanonicalKeys? keys = some sorted := by
  intro keys
  induction keys with
  | nil =>
      intro _
      exact ⟨[], rfl⟩
  | cons key keys inductionHypothesis =>
      intro allComplete
      have completeClauses : key.complete = true ∧ keys.all (·.complete) = true := by
        simpa using allComplete
      obtain ⟨sorted, sortedEq⟩ := inductionHypothesis completeClauses.2
      have sortedComplete : sorted.all (·.complete) = true := by
        have permutation := sortCanonicalKeys?_perm keys sorted sortedEq
        rw [permutation.all_eq]
        exact completeClauses.2
      obtain ⟨result, insertedEq⟩ :=
        insertCanonicalKey?_exists_of_complete key completeClauses.1 sorted sortedComplete
      exact ⟨result, by simp [sortCanonicalKeys?, sortedEq, insertedEq]⟩

/-- A proper descendant of the generated canonical center tree.  Unlike the synthetic center root,
every such node has an incoming parent occurrence, so bonding number six leaves at most five
forward child slots. -/
def CanonicalCenterDescendantNode (mol : RawMolecule) (center : Nat)
    (node : CanonicalBranchNode) : Prop :=
  ∃ parent, CanonicalCenterTreeNode mol center parent ∧
    node ∈ mol.canonicalChildren parent

namespace CanonicalCenterDescendantNode

theorem generated {mol : RawMolecule} {center : Nat} {node : CanonicalBranchNode}
    (descendant : CanonicalCenterDescendantNode mol center node) :
    CanonicalCenterTreeNode mol center node := by
  rcases descendant with ⟨parent, parentGenerated, member⟩
  exact .child parentGenerated member

theorem child {mol : RawMolecule} {center : Nat} {node child : CanonicalBranchNode}
    (descendant : CanonicalCenterDescendantNode mol center node)
    (member : child ∈ mol.canonicalChildren node) :
    CanonicalCenterDescendantNode mol center child :=
  ⟨node, descendant.generated, member⟩

end CanonicalCenterDescendantNode

private theorem mapM_exists_all_complete {α : Type*}
    (build : α → Option CanonicalBranchKey) :
    ∀ inputs : List α,
      (∀ input, input ∈ inputs → ∃ key, build input = some key ∧ key.complete = true) →
      ∃ keys, inputs.mapM build = some keys ∧ keys.all (·.complete) = true := by
  intro inputs
  induction inputs with
  | nil =>
      intro _
      exact ⟨[], rfl, rfl⟩
  | cons input inputs inductionHypothesis =>
      intro pointwise
      obtain ⟨key, keyEq, keyComplete⟩ := pointwise input (by simp)
      obtain ⟨keys, keysEq, keysComplete⟩ := inductionHypothesis (by
        intro child member
        exact pointwise child (by simp [member]))
      exact ⟨key :: keys, by simp [keyEq, keysEq], by simp [keyComplete, keysComplete]⟩

private theorem canonicalRootKeyAuthoritative?_exists
    (mol : RawMolecule) (supported : MancudeRule1aSupported mol)
    (node : CanonicalBranchNode) (complete : Bool) :
    ∃ root, mol.canonicalRootKeyAuthoritative? node complete = some root ∧
      root.complete = complete := by
  obtain ⟨label, labelEq⟩ :=
    AuthoritativeCIPCursorSupport.canonicalRule1aLabelAuthoritative?_exists
      mol supported node
  unfold canonicalRootKeyAuthoritative?
  simp [labelEq]

/-- A generated proper branch descendant compiles to a complete authoritative key whenever the
fuel covers the remaining duplicate-free real history. -/
theorem buildCanonicalBranchKeyAuthoritative_exists_complete_of_centerDescendant
    (mol : RawMolecule) (center : Nat) (centerBound : center < mol.atomCount)
    (wellFormed : mol.WellFormed)
    (bonding : CanonicalCenterBondingNumberSix mol center)
    (supported : MancudeRule1aSupported mol) :
    ∀ fuel node,
      CanonicalCenterDescendantNode mol center node →
      mol.atomCount + 1 ≤ node.history.length + fuel →
      ∃ key, mol.buildCanonicalBranchKeyAuthoritative fuel node = some key ∧
        key.complete = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro node descendant covered
      have generated := descendant.generated
      by_cases terminal : mol.canonicalTerminal node = true
      · obtain ⟨root, rootEq, rootComplete⟩ :=
          canonicalRootKeyAuthoritative?_exists mol supported node true
        exact ⟨root, by simp [buildCanonicalBranchKeyAuthoritative, terminal, rootEq],
          rootComplete⟩
      · have terminalFalse : mol.canonicalTerminal node = false :=
          Bool.eq_false_of_not_eq_true terminal
        have notLeaf : node.forcedLeaf = false := by
          apply Bool.eq_false_of_not_eq_true
          intro leaf
          have terminalTrue : mol.canonicalTerminal node = true := by
            simp [canonicalTerminal, leaf]
          exact terminal terminalTrue
        have real := real_of_forcedLeaf_eq_false notLeaf
        have lengthLe := generated.real_history_length_le_atomCount
          centerBound wellFormed real
        simp only [Nat.add_zero] at covered
        omega
  | succ fuel inductionHypothesis =>
      intro node descendant covered
      have generated := descendant.generated
      by_cases terminal : mol.canonicalTerminal node = true
      · obtain ⟨root, rootEq, rootComplete⟩ :=
          canonicalRootKeyAuthoritative?_exists mol supported node true
        exact ⟨root, by simp [buildCanonicalBranchKeyAuthoritative, terminal, rootEq],
          rootComplete⟩
      · have terminalFalse : mol.canonicalTerminal node = false :=
          Bool.eq_false_of_not_eq_true terminal
        rcases descendant with ⟨parent, parentGenerated, nodeMember⟩
        have recovered := canonicalOriginalParent?_eq_some_of_child parentGenerated nodeMember
        have localBound := bonding node generated
        have childrenBound : (mol.canonicalChildren node).length ≤ authoritativeChildSlots := by
          simp [recovered, authoritativeChildSlots] at localBound ⊢
          omega
        have notTooWide : ¬ authoritativeChildSlots < (mol.canonicalChildren node).length := by
          omega
        obtain ⟨childKeys, childKeysEq, childKeysComplete⟩ :=
          mapM_exists_all_complete
            (fun child => mol.buildCanonicalBranchKeyAuthoritative fuel child)
            (mol.canonicalChildren node) (by
              intro child childMember
              have childHistory := child_history_length childMember
              exact inductionHypothesis child
                ⟨node, generated, childMember⟩ (by omega))
        obtain ⟨sorted, sortedEq⟩ :=
          sortCanonicalKeys?_exists_of_all_complete childKeys childKeysComplete
        have sortedComplete : sorted.all (·.complete) = true := by
          have permutation := sortCanonicalKeys?_perm childKeys sorted sortedEq
          rw [permutation.all_eq]
          exact childKeysComplete
        obtain ⟨root, rootEq, rootComplete⟩ :=
          canonicalRootKeyAuthoritative?_exists mol supported node
            (sorted.all fun child => child.complete)
        refine ⟨assembleCanonicalBranchKey root sorted, ?_, ?_⟩
        · simp [buildCanonicalBranchKeyAuthoritative, terminalFalse, notTooWide,
            childKeysEq, sortedEq, rootEq]
        · simp [assembleCanonicalBranchKey, rootComplete, sortedComplete]

/-- Every physical or lone-pair ligand slot of a molecule-derived final unit has a complete
width-unbounded authoritative branch on the independent chemical applicability domain. -/
theorem branchCanonicalKeyAuthoritative?_exists_complete_of_chemical_applicability
    (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (writtenExact : mol.WrittenNeighborExact)
    (valence : mol.ValenceOK) (kekule : LocalizedMancudeKekuleAdmissible mol)
    (root : Root mol) (slot : Fin 4) :
    ∃ key,
      branchCanonicalKeyAuthoritative? mol (centerAtom root).val (ligandAtom root slot) =
        some key ∧ key.complete = true := by
  let center := (centerAtom root).val
  let ligand := ligandAtom root slot
  by_cases phantom : ligand = mol.atomCount
  · let key := mol.canonicalRootKey (canonicalRoot center mol.atomCount) true
    refine ⟨key, ?_, rfl⟩
    simpa [center, ligand, phantom, key] using
      mol.branchCanonicalKeyAuthoritative?_lonePair (centerAtom root) wellFormed
  · have ligandMember : ligand ∈ mol.ligandsWithLonePair center :=
      ligandAtom_mem root slot
    have writtenMember : ligand ∈ mol.writtenNeighbors center :=
      mem_writtenNeighbors_of_mem_ligandsWithLonePair_of_ne
        mol center ligand ligandMember phantom
    have centerBound : center < mol.atomCount := (centerAtom root).isLt
    have clauses := WrittenNeighborExact.at mol writtenExact (centerAtom root)
    have ligandBound : ligand < mol.atomCount := clauses.2.1 ligand writtenMember
    let ligandFin : Fin mol.atomCount := ⟨ligand, ligandBound⟩
    have positive : 0 < mol.bondOrder center ligand :=
      (clauses.2.2 ligandFin).mp writtenMember
    have distinct : ligand ≠ center := by
      intro equal
      have positiveSelf : 0 < mol.bondOrder center center := by simpa [equal] using positive
      rw [mol.bondOrder_self] at positiveSelf
      exact (Nat.not_lt_zero 0 positiveSelf).elim
    have rootMember : canonicalRoot center ligand ∈
        mol.canonicalChildren (canonicalCenterRoot center) :=
      AuthoritativeCIPRule6Scheduler.canonicalRoot_mem_canonicalChildren_of_bondOrder_pos
        mol center ligand distinct positive
    have bonding : CanonicalCenterBondingNumberSix mol center :=
      AuthoritativeCIPValenceBondingNumber.canonicalCenterBondingNumberSix_of_valence
        mol center centerBound wellFormed unique valence
    have supported : MancudeRule1aSupported mol :=
      mancudeRule1aSupported_of_localizedKekuleAdmissible mol wellFormed unique kekule
    unfold branchCanonicalKeyAuthoritative?
    exact buildCanonicalBranchKeyAuthoritative_exists_complete_of_centerDescendant
      mol center centerBound wellFormed bonding supported
      (2 * mol.atomCount + 2) (canonicalRoot center ligand)
      ⟨canonicalCenterRoot center, .root, rootMember⟩ (by
        simp [canonicalRoot]
        omega)

end RawMolecule

end TetraStereo.OneCenter
