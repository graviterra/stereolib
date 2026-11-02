import TetraStereo.OneCenter.RawFourLigandFrameLaws
import TetraStereo.UniversalProof.SecondSphereFamilyValenceInstantiation
import TetraStereo.UniversalProof.TerminalStarCycleGuard
import TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupport
import TetraStereo.UniversalProof.ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SecondSphereInitialSeedBridge

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation
open TetraStereo.UniversalProof.SecondSphereFamilyValenceInstantiation
open TetraStereo.UniversalProof.TerminalStarCycleGuard







def roleIndex (i offset : Nat) : Nat := 1 + 12 * i + offset
def rootNode (i offset : Nat) : CanonicalBranchNode :=
  canonicalRoot (roleIndex i 5) (roleIndex i offset)
def childNode (i parent offset : Nat) : CanonicalBranchNode :=
  { atom := roleIndex i offset, parent := roleIndex i parent,
    history := [roleIndex i offset, roleIndex i parent, roleIndex i 5],
    provenance := .realAtom }
def hydrogenNode (i offset : Nat) : CanonicalBranchNode :=
  childNode i (if offset < 8 then 2 else 8) offset

private theorem canonical_bond_one (raw : RawMolecule) (node : CanonicalBranchNode)
    (other : Nat) (one : raw.bondOrder node.atom other = 1) :
    raw.canonicalBondOrder node other = 1 := by
  cases history : node.history with
  | nil => simpa only [canonicalBondOrder, history] using one
  | cons first tail =>
      cases tail with
      | nil => simpa only [canonicalBondOrder, history] using one
      | cons second tail =>
          cases tail with
          | nil => simp [canonicalBondOrder, history, one]
          | cons third rest => simpa only [canonicalBondOrder, history] using one

private theorem unit_copies (raw : RawMolecule) (node : CanonicalBranchNode)
    (bonds : List RawBond)
    (single : ∀ bond ∈ bonds, ∀ other, recordNeighbor? node.atom bond = some other →
      raw.canonicalBondOrder node other = 1) :
    (bonds.flatMap fun bond => match recordNeighbor? node.atom bond with
      | none => []
      | some other => (List.range (raw.canonicalBondOrder node other)).map
          (fun copy => (other, copy))) =
    (bonds.filterMap (recordNeighbor? node.atom)).map (fun other => (other, 0)) := by
  induction bonds with
  | nil => rfl
  | cons bond bonds ih =>
      have tailSingle : ∀ selected ∈ bonds, ∀ other,
          recordNeighbor? node.atom selected = some other →
            raw.canonicalBondOrder node other = 1 := by
        intro selected member other observed
        exact single selected (List.mem_cons_of_mem bond member) other observed
      simp only [List.flatMap_cons, List.filterMap_cons]
      cases observed : recordNeighbor? node.atom bond with
      | none => simpa only [List.nil_append] using ih tailSingle
      | some other =>
          have one := single bond List.mem_cons_self other observed
          simp only [one, List.range_succ, List.range_zero, List.nil_append,
            List.map_cons, List.map_nil, List.cons_append]
          rw [ih tailSingle]

private theorem erase_map_zero (parent : Nat) (atoms : List Nat) :
    eraseCanonicalParentCopy parent (atoms.map (fun atom => (atom, 0))) =
      (atoms.erase parent).map (fun atom => (atom, 0)) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      by_cases equal : atom = parent
      · subst atom; simp [eraseCanonicalParentCopy]
      · simp [eraseCanonicalParentCopy, equal, ih]

/-- Unit physical records generate one child copy, then erase the actual parent copy. -/
theorem actual_child_copies (ps : List TetrahedralInputParity) (node : CanonicalBranchNode) :
    (familyRaw ps).canonicalChildCopies node =
      ((recordNeighbors (familyRaw ps) node.atom).erase node.parent).map
        (fun other => (other, 0)) := by
  have seeds := unit_copies (familyRaw ps) node (familyRaw ps).bonds (by
    intro bond member other observed
    exact canonical_bond_one _ node other
      (familyRaw_incident_order ps node.atom other
        (List.mem_filterMap.mpr ⟨bond, member, observed⟩)))
  change eraseCanonicalParentCopy node.parent
    ((familyRaw ps).bonds.flatMap fun bond => match recordNeighbor? node.atom bond with
      | none => []
      | some other => (List.range ((familyRaw ps).canonicalBondOrder node other)).map
          (fun copy => (other, copy))) = _
  rw [seeds, erase_map_zero]
  rfl

/-- The bridge's actual initial-root children include the backbone, in physical record order. -/
theorem actual_bridge_children (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).canonicalChildren (rootNode i.val 2) =
      [childNode i.val 2 0, hydrogenNode i.val 3, hydrogenNode i.val 4] := by
  unfold canonicalChildren
  rw [show (rootNode i.val 2).forcedLeaf = false from rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [actual_child_copies]
  change (((recordNeighbors (familyRaw ps) (1 + 12 * i.val + 2)).erase
    (1 + 12 * i.val + 5)).map (fun other => (other, 0))).map _ = _
  rw [familyRaw_bridge_records ps i]
  have erased : ([1 + 12 * i.val, 1 + 12 * i.val + 3,
      1 + 12 * i.val + 4, 1 + 12 * i.val + 5].erase (1 + 12 * i.val + 5)) =
      [1 + 12 * i.val, 1 + 12 * i.val + 3, 1 + 12 * i.val + 4] := by
    rw [List.erase_cons_tail (by simp only [beq_iff_eq]; omega),
      List.erase_cons_tail (by simp only [beq_iff_eq]; omega),
      List.erase_cons_tail (by simp only [beq_iff_eq]; omega), List.erase_cons_head]
  rw [erased]
  simp (disch := omega) [rootNode, childNode, hydrogenNode, roleIndex, canonicalRoot,
    List.contains_eq_mem]

theorem actual_methyl_children (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).canonicalChildren (rootNode i.val 8) =
      [hydrogenNode i.val 9, hydrogenNode i.val 10, hydrogenNode i.val 11] := by
  unfold canonicalChildren
  rw [show (rootNode i.val 8).forcedLeaf = false from rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [actual_child_copies]
  change (((recordNeighbors (familyRaw ps) (1 + 12 * i.val + 8)).erase
    (1 + 12 * i.val + 5)).map (fun other => (other, 0))).map _ = _
  rw [familyRaw_methyl_records ps i]
  simp (disch := omega) [rootNode, childNode, hydrogenNode, roleIndex, canonicalRoot,
    List.contains_eq_mem]

/-- A physical leaf row is terminal under the actual parent erasure. -/
theorem actual_leaf_terminal (ps : List TetrahedralInputParity) (node : CanonicalBranchNode)
    (real : node.provenance = .realAtom)
    (row : recordNeighbors (familyRaw ps) node.atom = [node.parent]) :
    (familyRaw ps).canonicalTerminal node = true := by
  have notLeaf : node.forcedLeaf = false := by simp [CanonicalBranchNode.forcedLeaf, real]
  have empty : (familyRaw ps).canonicalChildren node = [] := by
    unfold canonicalChildren
    rw [notLeaf]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [actual_child_copies, row]
    simp
  simp [canonicalTerminal, notLeaf, empty]

/-- Every comparison hydrogen is an actual terminal real node of natural isotope mass. -/
theorem actual_hydrogen_facts (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (offset : Nat) (member : offset ∈ [3, 4, 9, 10, 11]) :
    (familyRaw ps).canonicalTerminal (hydrogenNode i.val offset) = true ∧
    (familyRaw ps).atomZAt (hydrogenNode i.val offset).atom = 1 ∧
    (familyRaw ps).atomMassAt (hydrogenNode i.val offset).atom =
      rule2MassPico Element.H none := by
  have bound : offset < 12 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
  have positive : 0 < offset := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
  have rows := familyRaw_local_records ps i offset positive bound
  have atom := familyRaw_role_atom ps i offset bound
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals
    constructor
    · apply actual_leaf_terminal ps _ rfl
      simpa [hydrogenNode, childNode, roleIndex, closedLocalRow] using rows
    · constructor
      · simpa only [hydrogenNode, childNode, roleIndex] using familyRaw_role_Z ps i _ (by decide)
      · simp [hydrogenNode, childNode, roleIndex, atomMassAt, atomMassAt?, atom,
          roleAtom, roleOfOffset, hydrogenSpec,
          GeneralParserStateBridge.atomSpec, rule2MassPico]

/-- Strict real-node Rule 1a short-circuits the actual supported structural comparator at every
depth. This is about the legacy structural node entry, not an occurrence cursor. -/
theorem supported_strict_real (raw : RawMolecule) (fuel : Nat) (stage : CanonicalRuleStage)
    (left right : CanonicalBranchNode) (leftReal : left.provenance = .realAtom)
    (rightReal : right.provenance = .realAtom) (decision : Ordering)
    (ordered : compare (raw.atomZAt left.atom) (raw.atomZAt right.atom) = decision)
    (strict : decision ≠ .eq) :
    raw.compareCanonicalBranchAtSupported? fuel stage left right = some decision := by
  have labels := compareCanonicalNodeRule?_rule1a_realAtom raw left right leftReal rightReal
  rw [ordered] at labels
  cases fuel with
  | zero => exact compareCanonicalNodeThrough?_eq_of_rule1a raw stage left right decision labels strict
  | succ fuel =>
      have sphere : raw.compareCanonicalPairLabels? .rule1a [(left, right)] = some decision := by
        cases decision <;> simp_all [compareCanonicalPairLabels?]
      cases decision <;>
        simp_all [compareCanonicalBranchAtSupported?, compareCanonicalRuleSupported?,
          defaultBranchWidthCap]

/-- Equal natural terminal siblings tie through Rules 1a, 1b and 2 at every sorting depth. -/
theorem supported_terminal_real_tie (raw : RawMolecule) (fuel : Nat)
    (stage : CanonicalRuleStage) (left right : CanonicalBranchNode)
    (leftReal : left.provenance = .realAtom) (rightReal : right.provenance = .realAtom)
    (leftTerminal : raw.canonicalTerminal left = true)
    (rightTerminal : raw.canonicalTerminal right = true)
    (sameZ : raw.atomZAt left.atom = raw.atomZAt right.atom)
    (sameDepth : left.depth = right.depth)
    (sameMass : raw.atomMassAt left.atom = raw.atomMassAt right.atom) :
    raw.compareCanonicalBranchAtSupported? fuel stage left right = some Ordering.eq := by
  have r1a := compareCanonicalNodeRule?_rule1a_realAtom raw left right leftReal rightReal
  rw [sameZ] at r1a
  have r1aTie : raw.compareCanonicalNodeRule? .rule1a left right = some Ordering.eq := by
    simpa using r1a
  have r1bTie : raw.compareCanonicalNodeRule? .rule1b left right = some Ordering.eq := by
    simp [compareCanonicalNodeRule?, compareCanonicalNodeRule,
      CanonicalBranchNode.rule1bRootDistance, leftReal, rightReal, sameDepth]
  have r2Tie : raw.compareCanonicalNodeRule? .rule2 left right = some Ordering.eq := by
    simp [compareCanonicalNodeRule?, compareCanonicalNodeRule, leftReal, rightReal, sameMass]
  have spheres (rule : CanonicalRuleStage) :
      raw.compareCanonicalPairLabels? rule [(left, right)] = some Ordering.eq := by
    cases rule <;> simp [compareCanonicalPairLabels?, r1aTie, r1bTie, r2Tie]
  have next (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering) :
      raw.nextCanonicalPairs? before [(left, right)] = some [] := by
    simp [nextCanonicalPairs?, leftTerminal, rightTerminal]
  cases fuel with
  | zero => cases stage <;> simp [compareCanonicalBranchAtSupported?,
      compareCanonicalNodeThrough?, r1aTie, r1bTie, r2Tie]
  | succ fuel => cases stage <;> simp [compareCanonicalBranchAtSupported?,
      compareCanonicalRuleSupported?, spheres, next, defaultBranchWidthCap]

theorem actual_hydrogen_tie (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (left right fuel : Nat) (stage : CanonicalRuleStage)
    (leftMember : left ∈ [3, 4, 9, 10, 11]) (rightMember : right ∈ [3, 4, 9, 10, 11]) :
    (familyRaw ps).compareCanonicalBranchAtSupported? fuel stage
      (hydrogenNode i.val left) (hydrogenNode i.val right) = some Ordering.eq := by
  have lf := actual_hydrogen_facts ps i left leftMember
  have rf := actual_hydrogen_facts ps i right rightMember
  apply supported_terminal_real_tie _ fuel stage _ _ rfl rfl lf.1 rf.1
  · exact lf.2.1.trans rf.2.1.symm
  · simp [hydrogenNode, childNode, CanonicalBranchNode.depth]
  · exact lf.2.2.trans rf.2.2.symm

theorem actual_backbone_over_hydrogen (ps : List TetrahedralInputParity)
    (i : Fin ps.length) (offset fuel : Nat) (stage : CanonicalRuleStage)
    (member : offset ∈ [3, 4, 9, 10, 11]) :
    (familyRaw ps).compareCanonicalBranchAtSupported? fuel stage
      (childNode i.val 2 0) (hydrogenNode i.val offset) = some Ordering.gt := by
  apply supported_strict_real _ fuel stage _ _ rfl rfl .gt
  · rw [(actual_hydrogen_facts ps i offset member).2.1]
    have carbon := (familyRaw_interior_carbon_Z ps i).1
    change (familyRaw ps).atomZAt (childNode i.val 2 0).atom = 6 at carbon
    rw [carbon]
    rfl
  · decide

theorem actual_ranked_bridge (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (fuel : Nat) (stage : CanonicalRuleStage) :
    (familyRaw ps).rankedCanonicalChildren?
      ((familyRaw ps).compareCanonicalBranchAtSupported? fuel stage) (rootNode i.val 2) =
      some [childNode i.val 2 0, hydrogenNode i.val 3, hydrogenNode i.val 4] := by
  have tied := actual_hydrogen_tie ps i 3 4 fuel stage (by simp) (by simp)
  have above := actual_backbone_over_hydrogen ps i 3 fuel stage (by simp)
  simp [rankedCanonicalChildren?, actual_bridge_children, sortCanonicalBy?,
    insertCanonicalBy?, tied, above]

theorem actual_ranked_methyl (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (fuel : Nat) (stage : CanonicalRuleStage) :
    (familyRaw ps).rankedCanonicalChildren?
      ((familyRaw ps).compareCanonicalBranchAtSupported? fuel stage) (rootNode i.val 8) =
      some [hydrogenNode i.val 9, hydrogenNode i.val 10, hydrogenNode i.val 11] := by
  have tied12 := actual_hydrogen_tie ps i 9 10 fuel stage (by simp) (by simp)
  have tied23 := actual_hydrogen_tie ps i 10 11 fuel stage (by simp) (by simp)
  simp [rankedCanonicalChildren?, actual_methyl_children, sortCanonicalBy?,
    insertCanonicalBy?, tied12, tied23]

/-- Actual second-sphere result at every positive structural depth, in both directions. -/
theorem actual_supported_both (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (fuel : Nat) (stage : CanonicalRuleStage) :
    (familyRaw ps).compareCanonicalBranchAtSupported? (fuel + 1) stage
      (rootNode i.val 2) (rootNode i.val 8) = some Ordering.gt ∧
    (familyRaw ps).compareCanonicalBranchAtSupported? (fuel + 1) stage
      (rootNode i.val 8) (rootNode i.val 2) = some Ordering.lt := by
  let raw := familyRaw ps
  let b := rootNode i.val 2
  let m := rootNode i.val 8
  let bc := childNode i.val 2 0
  let bh1 := hydrogenNode i.val 3
  let bh2 := hydrogenNode i.val 4
  let mh1 := hydrogenNode i.val 9
  let mh2 := hydrogenNode i.val 10
  let mh3 := hydrogenNode i.val 11
  let before := raw.compareCanonicalBranchAtSupported? fuel stage
  let forward := [(bc, mh1), (bh1, mh2), (bh2, mh3)]
  let reverse := [(mh1, bc), (mh2, bh1), (mh3, bh2)]
  have bridgeZ : raw.atomZAt b.atom = 6 := (familyRaw_interior_carbon_Z ps i).2.1
  have methylZ : raw.atomZAt m.atom = 6 := (familyRaw_interior_carbon_Z ps i).2.2.2
  have backboneZ : raw.atomZAt bc.atom = 6 := (familyRaw_interior_carbon_Z ps i).1
  have hydrogenZ : raw.atomZAt mh1.atom = 1 := (actual_hydrogen_facts ps i 9 (by simp)).2.1
  have rootForward := compareCanonicalNodeRule?_rule1a_realAtom raw b m rfl rfl
  have rootReverse := compareCanonicalNodeRule?_rule1a_realAtom raw m b rfl rfl
  rw [bridgeZ, methylZ] at rootForward
  rw [bridgeZ, methylZ] at rootReverse
  have rootForwardTie : raw.compareCanonicalNodeRule? .rule1a b m = some Ordering.eq := rootForward
  have rootReverseTie : raw.compareCanonicalNodeRule? .rule1a m b = some Ordering.eq := rootReverse
  have leadForward := compareCanonicalNodeRule?_rule1a_realAtom raw bc mh1 rfl rfl
  have leadReverse := compareCanonicalNodeRule?_rule1a_realAtom raw mh1 bc rfl rfl
  rw [backboneZ, hydrogenZ] at leadForward
  rw [backboneZ, hydrogenZ] at leadReverse
  have leadingForward : raw.compareCanonicalNodeRule? .rule1a bc mh1 = some Ordering.gt := leadForward
  have leadingReverse : raw.compareCanonicalNodeRule? .rule1a mh1 bc = some Ordering.lt := leadReverse
  have bNonterminal : raw.canonicalTerminal b = false := by
    change (familyRaw ps).canonicalTerminal (rootNode i.val 2) = false
    rw [canonicalTerminal, show (rootNode i.val 2).forcedLeaf = false from rfl,
      actual_bridge_children ps i]
    rfl
  have mNonterminal : raw.canonicalTerminal m = false := by
    change (familyRaw ps).canonicalTerminal (rootNode i.val 8) = false
    rw [canonicalTerminal, show (rootNode i.val 8).forcedLeaf = false from rfl,
      actual_methyl_children ps i]
    rfl
  have rankedB : raw.rankedCanonicalChildren? before b = some [bc, bh1, bh2] :=
    actual_ranked_bridge ps i fuel stage
  have rankedM : raw.rankedCanonicalChildren? before m = some [mh1, mh2, mh3] :=
    actual_ranked_methyl ps i fuel stage
  have expandedForward : raw.nextCanonicalPairs? before [(b, m)] = some forward := by
    simp [nextCanonicalPairs?, bNonterminal, mNonterminal, rankedB, rankedM, forward]
  have expandedReverse : raw.nextCanonicalPairs? before [(m, b)] = some reverse := by
    simp [nextCanonicalPairs?, bNonterminal, mNonterminal, rankedB, rankedM, reverse]
  have labelForward : raw.compareCanonicalPairLabels? .rule1a forward = some Ordering.gt := by
    simp [forward, compareCanonicalPairLabels?, leadingForward]
  have labelReverse : raw.compareCanonicalPairLabels? .rule1a reverse = some Ordering.lt := by
    simp [reverse, compareCanonicalPairLabels?, leadingReverse]
  have secondForward (depth : Nat) :
      raw.compareCanonicalRuleSupported? before .rule1a defaultBranchWidthCap depth forward =
        some Ordering.gt := by
    cases depth <;> simp [compareCanonicalRuleSupported?, labelForward, forward, defaultBranchWidthCap]
  have secondReverse (depth : Nat) :
      raw.compareCanonicalRuleSupported? before .rule1a defaultBranchWidthCap depth reverse =
        some Ordering.lt := by
    cases depth <;> simp [compareCanonicalRuleSupported?, labelReverse, reverse, defaultBranchWidthCap]
  have firstForward : raw.compareCanonicalRuleSupported? before .rule1a defaultBranchWidthCap
      (fuel + 1) [(b, m)] = some Ordering.gt := by
    simp [compareCanonicalRuleSupported?, compareCanonicalPairLabels?, rootForwardTie,
      expandedForward, defaultBranchWidthCap]
    exact secondForward fuel
  have firstReverse : raw.compareCanonicalRuleSupported? before .rule1a defaultBranchWidthCap
      (fuel + 1) [(m, b)] = some Ordering.lt := by
    simp [compareCanonicalRuleSupported?, compareCanonicalPairLabels?, rootReverseTie,
      expandedReverse, defaultBranchWidthCap]
    exact secondReverse fuel
  dsimp only [before] at firstForward firstReverse
  constructor
  · change raw.compareCanonicalBranchAtSupported? (fuel + 1) stage b m = some Ordering.gt
    simp only [compareCanonicalBranchAtSupported?, firstForward]
  · change raw.compareCanonicalBranchAtSupported? (fuel + 1) stage m b = some Ordering.lt
    simp only [compareCanonicalBranchAtSupported?, firstReverse]

/-- Actual analysis fuel selects the complete structural route, rather than a compiled shortcut. -/
theorem actual_structural_both (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).compareCanonicalBranchesStructurally? (analysisFuel (familyRaw ps))
      (roleIndex i.val 5) (roleIndex i.val 2) (roleIndex i.val 8) = some Ordering.gt ∧
    (familyRaw ps).compareCanonicalBranchesStructurally? (analysisFuel (familyRaw ps))
      (roleIndex i.val 5) (roleIndex i.val 8) (roleIndex i.val 2) = some Ordering.lt := by
  have depth : (familyRaw ps).atomCount + 1 ≤ analysisFuel (familyRaw ps) := by
    unfold analysisFuel; omega
  have both := actual_supported_both ps i (familyRaw ps).atomCount .rule2
  simpa only [compareCanonicalBranchesStructurally?, depth, ↓reduceIte, rootNode] using both

/-- The bridge has a carbon child, so neither orientation enters terminal-hydrogen-shell ranking. -/
theorem actual_terminal_shells_none (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).compareTerminalHydrogenShellRoots? (rootNode i.val 2) (rootNode i.val 8) = none ∧
    (familyRaw ps).compareTerminalHydrogenShellRoots? (rootNode i.val 8) (rootNode i.val 2) = none := by
  have backboneZ := (familyRaw_interior_carbon_Z ps i).1
  have bridgeNone : (familyRaw ps).terminalHydrogenMasses? (rootNode i.val 2) = none := by
    simp [terminalHydrogenMasses?, actual_bridge_children, childNode, hydrogenNode,
      roleIndex, backboneZ]
  constructor
  · simp [compareTerminalHydrogenShellRoots?, bridgeNone]
  · unfold compareTerminalHydrogenShellRoots?
    rw [bridgeNone]
    cases (familyRaw ps).terminalHydrogenMasses? (rootNode i.val 8) <;> rfl

theorem actual_methyl_cycle_false (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (fuel : Nat) : (familyRaw ps).atomLiesInCycle fuel (roleIndex i.val 8) = false := by
  have leaves := familyRaw_comparison_leaf_records ps i
  apply terminalStar_atomLiesInCycle_false (familyRaw ps) (roleIndex i.val 8)
    (roleIndex i.val 5) (roleIndex i.val 9) (roleIndex i.val 10) (roleIndex i.val 11) fuel
  exact ⟨familyRaw_wellFormed ps, familyRaw_methyl_records ps i,
    by simp (disch := omega) [roleIndex], leaves.2.2.1, leaves.2.2.2.1, leaves.2.2.2.2⟩

/-- Actual production compareBranches? at analysisFuel: all earlier dispatch branches are
derived from physical records, and both orientations reach the complete-depth structural proof. -/
theorem actual_compareBranches_both (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).compareBranches? (analysisFuel (familyRaw ps))
      (roleIndex i.val 5) (roleIndex i.val 2) (roleIndex i.val 8) = some Ordering.gt ∧
    (familyRaw ps).compareBranches? (analysisFuel (familyRaw ps))
      (roleIndex i.val 5) (roleIndex i.val 8) (roleIndex i.val 2) = some Ordering.lt := by
  have bridgeZ : (familyRaw ps).atomZAt (roleIndex i.val 2) = 6 :=
    (familyRaw_interior_carbon_Z ps i).2.1
  have methylZ : (familyRaw ps).atomZAt (roleIndex i.val 8) = 6 :=
    (familyRaw_interior_carbon_Z ps i).2.2.2
  have shells := actual_terminal_shells_none ps i
  simp only [rootNode] at shells
  have structural := actual_structural_both ps i
  have cycle := actual_methyl_cycle_false ps i (analysisFuel (familyRaw ps))
  constructor <;>
    simp [compareBranches?,
      NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_root_rule1a,
      bridgeZ, methylZ, shells.1, shells.2, cycle,
      structural.1, structural.2]

/-- Production hydrogen materialization is exactly the physical family record: inline counts
were already zero, the written table is total, and exactness comes from actual appends. -/
theorem actual_materialized_identity (ps : List TetrahedralInputParity) :
    (familyRaw ps).withExplicitHydrogens = familyRaw ps :=
  ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.structurally_fixed_expansion_identity
    (familyRaw ps) ⟨familyRaw_zero_explicit_hydrogens ps,
      familyRaw_writtenNeighborExact ps, (familyRaw_blockGood ps).2.1.1⟩

/-- Actual written-row priority [F, bridge, methyl, H], derived by the legacy sorter. -/
theorem actual_rank_positions (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).rankBranchPositions? (analysisFuel (familyRaw ps)) (roleIndex i.val 5)
      ((familyRaw ps).writtenNeighbors (roleIndex i.val 5)) = some [2, 0, 3, 1] := by
  have carbon := familyRaw_interior_carbon_Z ps i
  have terminal := familyRaw_terminal_Z ps i
  have z2 : (familyRaw ps).atomZAt (roleIndex i.val 2) = 6 := carbon.2.1
  have z8 : (familyRaw ps).atomZAt (roleIndex i.val 8) = 6 := carbon.2.2.2
  have z6 : (familyRaw ps).atomZAt (roleIndex i.val 6) = 1 := terminal.2.2.2.1
  have z7 : (familyRaw ps).atomZAt (roleIndex i.val 7) = 9 := terminal.2.2.2.2.1
  have bm := actual_compareBranches_both ps i
  have p27 : (familyRaw ps).compareBranches? (analysisFuel (familyRaw ps))
      (roleIndex i.val 5) (roleIndex i.val 2) (roleIndex i.val 7) = some Ordering.lt := by
    rw [NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_strict_branch
      _ _ _ _ _ (by rw [z2, z7]; decide), z2, z7]
    rfl
  have p67 : (familyRaw ps).compareBranches? (analysisFuel (familyRaw ps))
      (roleIndex i.val 5) (roleIndex i.val 6) (roleIndex i.val 7) = some Ordering.lt := by
    rw [NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_strict_branch
      _ _ _ _ _ (by rw [z6, z7]; decide), z6, z7]
    rfl
  have p78 : (familyRaw ps).compareBranches? (analysisFuel (familyRaw ps))
      (roleIndex i.val 5) (roleIndex i.val 7) (roleIndex i.val 8) = some Ordering.gt := by
    rw [NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_strict_branch
      _ _ _ _ _ (by rw [z7, z8]; decide), z7, z8]
    rfl
  have p68 : (familyRaw ps).compareBranches? (analysisFuel (familyRaw ps))
      (roleIndex i.val 5) (roleIndex i.val 6) (roleIndex i.val 8) = some Ordering.lt := by
    rw [NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_strict_branch
      _ _ _ _ _ (by rw [z6, z8]; decide), z6, z8]
    rfl
  have p72 : (familyRaw ps).compareBranches? (analysisFuel (familyRaw ps))
      (roleIndex i.val 5) (roleIndex i.val 7) (roleIndex i.val 2) = some Ordering.gt := by
    rw [NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_strict_branch
      _ _ _ _ _ (by rw [z7, z2]; decide), z7, z2]
    rfl
  have p86 : (familyRaw ps).compareBranches? (analysisFuel (familyRaw ps))
      (roleIndex i.val 5) (roleIndex i.val 8) (roleIndex i.val 6) = some Ordering.gt := by
    rw [NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_strict_branch
      _ _ _ _ _ (by rw [z8, z6]; decide), z8, z6]
    rfl
  have written : (familyRaw ps).writtenNeighbors (roleIndex i.val 5) =
      [roleIndex i.val 2, roleIndex i.val 6, roleIndex i.val 7, roleIndex i.val 8] := by
    simpa only [roleIndex] using familyRaw_tag_written ps i
  rw [written]
  simp [rankBranchPositions?, compareBranches, sortDescBy, insertDescBy,
    List.range_succ, p27, p67, p78, p68, p72, p86, bm.1 ]

/-- A strict constitutional decision is retained by the actual Rule-3 dispatch. -/
theorem rule3_of_strict (result : ChemistryNormalizationResult) (raw : RawMolecule)
    (fuel center left right : Nat) (decision : Ordering)
    (computed : raw.compareBranches? fuel center left right = some decision)
    (strict : decision ≠ .eq) :
    result.compareBranchesThroughRule3? raw fuel center left right = some decision := by
  cases decision <;> simp_all [ChemistryNormalizationResult.compareBranchesThroughRule3?,
    compareBranchesStatus]

/-- The priority metadata stored in the actual initial seed uses the Rule-3-aware sorter.
Its constitutional strict comparisons give exactly the same derived positions. -/
theorem actual_rule3_rank_positions (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    rankBranchPositionsThroughRule3? (normalizeRawMolecule (familyRaw ps)) (familyRaw ps)
      (analysisFuel (familyRaw ps)) (roleIndex i.val 5)
      ((familyRaw ps).writtenNeighbors (roleIndex i.val 5)) = some [2, 0, 3, 1] := by
  have carbon := familyRaw_interior_carbon_Z ps i
  have terminal := familyRaw_terminal_Z ps i
  have z2 : (familyRaw ps).atomZAt (roleIndex i.val 2) = 6 := carbon.2.1
  have z8 : (familyRaw ps).atomZAt (roleIndex i.val 8) = 6 := carbon.2.2.2
  have z6 : (familyRaw ps).atomZAt (roleIndex i.val 6) = 1 := terminal.2.2.2.1
  have z7 : (familyRaw ps).atomZAt (roleIndex i.val 7) = 9 := terminal.2.2.2.2.1
  have bm := actual_compareBranches_both ps i
  have p27 : (familyRaw ps).compareBranches? (analysisFuel (familyRaw ps))
      (roleIndex i.val 5) (roleIndex i.val 2) (roleIndex i.val 7) = some Ordering.lt := by
    rw [NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_strict_branch
      _ _ _ _ _ (by rw [z2, z7]; decide), z2, z7]
    rfl
  have p67 : (familyRaw ps).compareBranches? (analysisFuel (familyRaw ps))
      (roleIndex i.val 5) (roleIndex i.val 6) (roleIndex i.val 7) = some Ordering.lt := by
    rw [NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_strict_branch
      _ _ _ _ _ (by rw [z6, z7]; decide), z6, z7]
    rfl
  have p78 : (familyRaw ps).compareBranches? (analysisFuel (familyRaw ps))
      (roleIndex i.val 5) (roleIndex i.val 7) (roleIndex i.val 8) = some Ordering.gt := by
    rw [NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_strict_branch
      _ _ _ _ _ (by rw [z7, z8]; decide), z7, z8]
    rfl
  have p68 : (familyRaw ps).compareBranches? (analysisFuel (familyRaw ps))
      (roleIndex i.val 5) (roleIndex i.val 6) (roleIndex i.val 8) = some Ordering.lt := by
    rw [NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_strict_branch
      _ _ _ _ _ (by rw [z6, z8]; decide), z6, z8]
    rfl
  have p72 : (familyRaw ps).compareBranches? (analysisFuel (familyRaw ps))
      (roleIndex i.val 5) (roleIndex i.val 7) (roleIndex i.val 2) = some Ordering.gt := by
    rw [NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_strict_branch
      _ _ _ _ _ (by rw [z7, z2]; decide), z7, z2]
    rfl
  have p86 : (familyRaw ps).compareBranches? (analysisFuel (familyRaw ps))
      (roleIndex i.val 5) (roleIndex i.val 8) (roleIndex i.val 6) = some Ordering.gt := by
    rw [NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_strict_branch
      _ _ _ _ _ (by rw [z8, z6]; decide), z8, z6]
    rfl
  have q27 := rule3_of_strict (normalizeRawMolecule (familyRaw ps)) (familyRaw ps)
    (analysisFuel (familyRaw ps)) (roleIndex i.val 5) (roleIndex i.val 2)
    (roleIndex i.val 7) .lt p27 (by decide)
  have q67 := rule3_of_strict (normalizeRawMolecule (familyRaw ps)) (familyRaw ps)
    (analysisFuel (familyRaw ps)) (roleIndex i.val 5) (roleIndex i.val 6)
    (roleIndex i.val 7) .lt p67 (by decide)
  have q78 := rule3_of_strict (normalizeRawMolecule (familyRaw ps)) (familyRaw ps)
    (analysisFuel (familyRaw ps)) (roleIndex i.val 5) (roleIndex i.val 7)
    (roleIndex i.val 8) .gt p78 (by decide)
  have q68 := rule3_of_strict (normalizeRawMolecule (familyRaw ps)) (familyRaw ps)
    (analysisFuel (familyRaw ps)) (roleIndex i.val 5) (roleIndex i.val 6)
    (roleIndex i.val 8) .lt p68 (by decide)
  have q72 := rule3_of_strict (normalizeRawMolecule (familyRaw ps)) (familyRaw ps)
    (analysisFuel (familyRaw ps)) (roleIndex i.val 5) (roleIndex i.val 7)
    (roleIndex i.val 2) .gt p72 (by decide)
  have q86 := rule3_of_strict (normalizeRawMolecule (familyRaw ps)) (familyRaw ps)
    (analysisFuel (familyRaw ps)) (roleIndex i.val 5) (roleIndex i.val 8)
    (roleIndex i.val 6) .gt p86 (by decide)
  have q28 := rule3_of_strict (normalizeRawMolecule (familyRaw ps)) (familyRaw ps)
    (analysisFuel (familyRaw ps)) (roleIndex i.val 5) (roleIndex i.val 2)
    (roleIndex i.val 8) .gt bm.1 (by decide)
  have q82 := rule3_of_strict (normalizeRawMolecule (familyRaw ps)) (familyRaw ps)
    (analysisFuel (familyRaw ps)) (roleIndex i.val 5) (roleIndex i.val 8)
    (roleIndex i.val 2) .lt bm.2 (by decide)
  have written : (familyRaw ps).writtenNeighbors (roleIndex i.val 5) =
      [roleIndex i.val 2, roleIndex i.val 6, roleIndex i.val 7, roleIndex i.val 8] := by
    simpa only [roleIndex] using familyRaw_tag_written ps i
  rw [written]
  simp [rankBranchPositionsThroughRule3?, sortDescBy, insertDescBy, List.range_succ,
    q27, q67, q78, q68, q72, q86, q28 ]

theorem actual_tag_ligands (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).ligandsWithLonePair (roleIndex i.val 5) =
      (familyRaw ps).writtenNeighbors (roleIndex i.val 5) :=
  AuthoritativeCIPRule6Scheduler.ligandsWithLonePair_eq_writtenNeighbors_of_length_four
    _ _ (by
      change ((familyRaw ps).writtenNeighbors (1 + 12 * i.val + 5)).length = 4
      rw [familyRaw_tag_written ps i]
      rfl)

theorem priority_permutation_odd : permutationIsEven [2, 0, 3, 1] = false := by decide +kernel

/-- The actual legacy classifier emits the parity-derived uppercase outcome at every tag. -/
theorem actual_legacy_outcome (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).tetrahedralOutcome (analysisFuel (familyRaw ps)) (roleIndex i.val 5) =
      .tetrahedral (descriptorOfParity (ps.get i) false) := by
  have lookup := familyRaw_role_atom ps i 5 (by decide)
  change (familyRaw ps).atomAt? (roleIndex i.val 5) =
    some (roleAtom (ps.get i) (roleOfOffset 5)) at lookup
  have rank := actual_rank_positions ps i
  have ligands := actual_tag_ligands ps i
  have written : (familyRaw ps).writtenNeighbors (roleIndex i.val 5) =
      [roleIndex i.val 2, roleIndex i.val 6, roleIndex i.val 7, roleIndex i.val 8] := by
    simpa only [roleIndex] using familyRaw_tag_written ps i
  have four : ((familyRaw ps).writtenNeighbors (roleIndex i.val 5)).length = 4 := by
    rw [written]
    rfl
  simp [tetrahedralOutcome, lookup, roleAtom, roleOfOffset,
    GeneralParserStateBridge.atomSpec, ligands, rank, four,
    priority_permutation_odd, centreElementSupported]

theorem actual_rule3_outcome (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    tetrahedralOutcomeThroughRule3 (normalizeRawMolecule (familyRaw ps)) (familyRaw ps)
      (analysisFuel (familyRaw ps)) (roleIndex i.val 5) =
      .tetrahedral (descriptorOfParity (ps.get i) false) := by
  simp only [tetrahedralOutcomeThroughRule3, actual_legacy_outcome]

def seedFact (ps : List TetrahedralInputParity) (i : Fin ps.length) : RawDescriptorFact :=
  { atom := roleIndex i.val 5
    descriptor := descriptorOfParity (ps.get i) false
    uppercase := true
    evidenceSize := 0
    priorityPositions := [2, 0, 3, 1] }

/-- Factored spelling of the actual initial-state entry, retaining both production consumers. -/
def seedEntry (ps : List TetrahedralInputParity) (index : Nat) : Option RawDescriptorFact :=
  match tetrahedralOutcomeThroughRule3 (normalizeRawMolecule (familyRaw ps)) (familyRaw ps)
      (analysisFuel (familyRaw ps)) index with
  | .tetrahedral descriptor =>
      some ({ atom := index
              descriptor := descriptor
              uppercase := true
              evidenceSize := 0
              priorityPositions :=
                (rankBranchPositionsThroughRule3? (normalizeRawMolecule (familyRaw ps))
                  (familyRaw ps) (analysisFuel (familyRaw ps)) index
                  ((familyRaw ps).ligandsWithLonePair index)).getD [] } : RawDescriptorFact)
  | _ => none

theorem actual_seed_entry (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    seedEntry ps (roleIndex i.val 5) = some (seedFact ps i) := by
  simp only [seedEntry, actual_rule3_outcome, actual_tag_ligands,
    actual_rule3_rank_positions, Option.getD_some]
  rfl

theorem seed_entry_atom (ps : List TetrahedralInputParity) (index : Nat)
    (fact : RawDescriptorFact) (computed : seedEntry ps index = some fact) :
    fact.atom = index := by
  unfold seedEntry at computed
  cases outcome : tetrahedralOutcomeThroughRule3 (normalizeRawMolecule (familyRaw ps))
    (familyRaw ps) (analysisFuel (familyRaw ps)) index <;> simp_all
  subst fact
  rfl

private theorem find_filterMap_entry (entry : Nat → Option RawDescriptorFact)
    (key : ∀ index fact, entry index = some fact → fact.atom = index)
    (indices : List Nat) (index : Nat) (fact : RawDescriptorFact)
    (computed : entry index = some fact) (member : index ∈ indices) :
    (indices.filterMap entry).find? (fun candidate => candidate.atom == index) = some fact := by
  induction indices with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons first rest ih =>
      by_cases same : first = index
      · subst first
        simp [computed, key index fact computed]
      · have retained : index ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        cases firstComputed : entry first with
        | none => simpa [List.filterMap_cons, firstComputed] using ih retained
        | some candidate =>
            have atom := key first candidate firstComputed
            simpa [List.filterMap_cons, firstComputed, atom, same] using ih retained

/-- Actual normalized/materialized initial-state lookup. Only the parity list and block index
enter: no successful lookup, desired seed/state/report, comparator callback or sorted roots. -/
theorem actual_initial_seed_lookup (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (initialRawDescriptorState (normalizeRawMolecule (familyRaw ps))
      (normalizeRawMolecule (familyRaw ps)).parsed.withExplicitHydrogens
      (analysisFuel (normalizeRawMolecule (familyRaw ps)).parsed.withExplicitHydrogens)).factAt?
        (roleIndex i.val 5) = some (seedFact ps i) := by
  rw [familyRaw_normalized_parsed, actual_materialized_identity]
  change ((List.range (normalizeRawMolecule (familyRaw ps)).parsed.atomCount).filterMap
    (seedEntry ps)).find? (fun candidate => candidate.atom == roleIndex i.val 5) = _
  rw [familyRaw_normalized_parsed]
  exact find_filterMap_entry (seedEntry ps) (seed_entry_atom ps)
    (List.range (familyRaw ps).atomCount) (roleIndex i.val 5) (seedFact ps i)
    (actual_seed_entry ps i) (List.mem_range.mpr (familyRaw_role_bound ps i 5 (by decide)))

end TetraStereo.UniversalProof.SecondSphereInitialSeedBridge
