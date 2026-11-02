import TetraStereo.UniversalProof.NextFrontier.NativeFamilyPhysicalHydrogenArms
import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalGenerationCoverage
import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorRuntime
import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorSorting

set_option autoImplicit false

















namespace TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeFramedCursorObservations
open TetraStereo.UniversalProof.NativeFamilyPhysicalHydrogenArms
open TetraStereo.UniversalProof.NativeChronologicalGenerationCoverage
open TetraStereo.UniversalProof.NativeChronologicalChildMultiplicity
open TetraStereo.UniversalProof.NativeGeneratedRealNodeInventory
open TetraStereo.UniversalProof.NativeGeneratedCursorPhysicalCut
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.WholeFamilyChronologicalTreeDomainProofs.WholeFamilyChronologicalTreeDomain
open TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation
open TetraStereo.UniversalProof.GeneralParserStateBridge (atomSpec)

/-! ## Strict shared-profile decision from a proven non-tied constitutional result

The only bridge we need from the new runtime: a strict `decisionComplete?` result is the plain
strict comparison for ANY state, given a proven non-tied `compareBranch?` Rule-2 outcome.  The
boolean `!=` guard is discharged by finite `Ordering` cases, not by an assumed success. -/
theorem decisionComplete_strict_of_neq (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) (ordering : Ordering)
    (h : FrameRuntime.compareBranch? mol profile authoritative fuel .rule2 (.actual left) (.actual right) =
      some ordering)
    (hne : ordering ≠ Ordering.eq) :
    FrameRuntime.decisionComplete? mol profile authoritative state fuel left right =
      some { ordering := ordering } := by
  have hbool : (ordering != Ordering.eq) = true := by
    cases ordering with
    | lt => rfl
    | eq => exact (hne rfl).elim
    | gt => rfl
  exact FrameRuntime.decisionComplete?_strict mol profile authoritative state fuel left right
    ordering h hbool

/-! ## Independent raw causal lemmas copied from the frozen reference caller -/

/-- The actual reversed first H/C pair decides Rule1a without examining later padded pairs. -/
theorem actual_hydrogen_carbon_first_pair {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {carbon hydrogen : CanonicalRerootCursor}
    (carbonEligible : CanonicalCenterRerootCursor mol root carbon)
    (carbonLabel : mol.atomZAt carbon.node.atom = 6)
    (hydrogenPhysical : PhysicalHydrogenCursor mol root center hydrogen)
    (authoritative : Bool) (pairs : List (FrameRuntime.Cursor × FrameRuntime.Cursor)) :
    FrameRuntime.pairLabels? mol (generatedProfile mol root center) authoritative .rule1a
      ((.actual hydrogen, .actual carbon) :: pairs) = some .lt := by
  have hydrogenFacts := physical_hydrogen_cursor_facts hydrogenPhysical
  have label := actual_rule1a_labels tree rootBound centerGenerated hydrogenFacts.1
    carbonEligible authoritative
  have strict : FrameRuntime.label? mol (generatedProfile mol root center) authoritative .rule1a
      (.actual hydrogen) (.actual carbon) = some .lt := by
    simpa only [carbonLabel, hydrogenFacts.2] using label
  simp [FrameRuntime.pairLabels?, strict]

/-- The reversed genuine physical-sphere comparison is derived from actual ranked lists
and the first H/C label. No antisymmetry or desired reversed outcome is a premise. -/
theorem actual_three_child_sphere_reverse_decision {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {bridge methyl carbon : CanonicalRerootCursor}
    (bridgeEligible : CanonicalCenterRerootCursor mol root bridge)
    (methylEligible : CanonicalCenterRerootCursor mol root methyl)
    (bridgeLabel : mol.atomZAt bridge.node.atom = 6)
    (methylLabel : mol.atomZAt methyl.node.atom = 6)
    (bridgeThree : (bridge.children mol).length = 3)
    (methylThree : (methyl.children mol).length = 3)
    (carbonMember : carbon ∈ bridge.children mol)
    (carbonLabel : mol.atomZAt carbon.node.atom = 6)
    (bridgeHydrogens : ∀ child ∈ bridge.children mol, child ≠ carbon →
      PhysicalHydrogenCursor mol root center child)
    (methylHydrogens : ∀ child ∈ methyl.children mol,
      PhysicalHydrogenCursor mol root center child)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage) :
    FrameRuntime.compareBranch? mol (generatedProfile mol root center) authoritative (fuel + 1) stage
      (.actual methyl) (.actual bridge) = some .lt := by
  have bridgeWidth : (bridge.children mol).length ≤
      (if authoritative then RawMolecule.authoritativeChildSlots else 3) := by
    rw [bridgeThree]
    exact three_children_fit_actual_slots authoritative
  have methylWidth : (methyl.children mol).length ≤
      (if authoritative then RawMolecule.authoritativeChildSlots else 3) := by
    rw [methylThree]
    exact three_children_fit_actual_slots authoritative
  obtain ⟨leading, suffix, decomposition, bridgeRanked⟩ := actual_one_carbon_ranked tree rootBound
    centerGenerated bridgeEligible carbonMember carbonLabel bridgeHydrogens authoritative fuel stage bridgeWidth
  have methylRanked := actual_hydrogen_ranked tree rootBound centerGenerated methylEligible
    methylHydrogens authoritative fuel stage methylWidth
  have bridgeTerminal := actual_three_child_nonterminal tree rootBound bridgeEligible bridgeThree
  have methylTerminal := actual_three_child_nonterminal tree rootBound methylEligible methylThree
  have parentLabel := actual_rule1a_labels tree rootBound centerGenerated methylEligible bridgeEligible authoritative
  have parentTie : FrameRuntime.label? mol (generatedProfile mol root center) authoritative .rule1a
      (.actual methyl) (.actual bridge) = some .eq := by
    simpa only [bridgeLabel, methylLabel] using parentLabel
  cases methylChildren : methyl.children mol with
  | nil => simp only [methylChildren, List.length_nil] at methylThree; omega
  | cons hydrogen hydrogens =>
      have headPhysical := methylHydrogens hydrogen (by simp only [methylChildren, List.mem_cons_self])
      let paddingCount := (if authoritative then RawMolecule.authoritativeChildSlots else 3) - 3
      let tailPairs := ((hydrogens.map FrameRuntime.Cursor.actual ++
          List.replicate paddingCount (FrameRuntime.Cursor.padding (FrameRuntime.Cursor.actual methyl))).zip
        ((leading ++ suffix).map FrameRuntime.Cursor.actual ++
          List.replicate paddingCount (FrameRuntime.Cursor.padding (FrameRuntime.Cursor.actual bridge))))
      have methylLength : hydrogens.length + 1 = 3 := by
        simp only [methylChildren, List.length_cons] at methylThree
        omega
      have expanded : FrameRuntime.nextPairs? mol (generatedProfile mol root center) authoritative
          (FrameRuntime.compareBranch? mol (generatedProfile mol root center) authoritative fuel stage)
          [(.actual methyl, .actual bridge)] = some ((.actual hydrogen, .actual carbon) :: tailPairs) := by
        simp [FrameRuntime.nextPairs?, bridgeTerminal, methylTerminal, bridgeRanked, methylRanked,
          methylChildren, bridgeThree, methylLength, tailPairs, paddingCount, List.zip_cons_cons]
      have pairStrict := actual_hydrogen_carbon_first_pair tree rootBound centerGenerated
        (bridgeEligible.child carbonMember) carbonLabel headPhysical authoritative tailPairs
      have leftTailCount : leading.length + suffix.length = 2 := by
        rw [decomposition] at bridgeThree
        simp only [List.length_append, List.length_cons] at bridgeThree
        omega
      have rightTailCount : hydrogens.length = 2 := by
        simp only [methylChildren, List.length_cons] at methylThree
        omega
      have count : ((.actual hydrogen, .actual carbon) :: tailPairs).length ≤ 5 := by
        simp only [List.length_cons, tailPairs, List.length_zip, List.length_append,
          List.length_map, List.length_replicate]
        rw [leftTailCount, rightTailCount]
        cases authoritative <;> simp [paddingCount, RawMolecule.authoritativeChildSlots]
      have within : ¬ defaultBranchWidthCap < ((.actual hydrogen, .actual carbon) :: tailPairs).length := by
        unfold defaultBranchWidthCap
        omega
      have tailWidth : tailPairs.length < defaultBranchWidthCap := by
        simp only [List.length_cons] at within
        omega
      have firstRule : FrameRuntime.compareRule? mol (generatedProfile mol root center) authoritative
          (FrameRuntime.compareBranch? mol (generatedProfile mol root center) authoritative fuel stage)
          .rule1a (fuel + 1) [(.actual methyl, .actual bridge)] = some .lt := by
        rw [FrameRuntime.compareRule?]
        simp [FrameRuntime.pairLabels?, parentTie, expanded, defaultBranchWidthCap]
        rw [FrameRuntime.compareRule?]
        simp [pairStrict, tailWidth]
      rw [FrameRuntime.compareBranch?]
      simp [firstRule]

/-- Strict actual atomic comparisons retain ordinary protocol flags for every auxiliary state. -/
theorem complete_atomic_decision {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {left right : CanonicalRerootCursor}
    (leftEligible : CanonicalCenterRerootCursor mol root left)
    (rightEligible : CanonicalCenterRerootCursor mol root right)
    (different : mol.atomZAt left.node.atom ≠ mol.atomZAt right.node.atom)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat) :
    FrameRuntime.decisionComplete? mol (generatedProfile mol root center) authoritative state fuel
      left right =
      some { ordering := compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) } := by
  have branch := actual_strict_atomic_branch tree rootBound centerGenerated leftEligible rightEligible
    different authoritative fuel .rule2
  have hne : compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) ≠ Ordering.eq := by
    intro same
    exact different (Nat.compare_eq_eq.mp same)
  exact decisionComplete_strict_of_neq mol (generatedProfile mol root center) authoritative state fuel
    left right (compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom)) branch hne

/-! ## Four-role indexing device (not an input domain or copied constructor) -/

inductive WrittenLigandRole where
  | bridge | hydrogen | fluorine | methyl
  deriving DecidableEq, Repr

def rolePriority : WrittenLigandRole → Nat
  | .bridge => 2
  | .hydrogen => 0
  | .fluorine => 3
  | .methyl => 1

def writtenRoles : List WrittenLigandRole := [.bridge, .hydrogen, .fluorine, .methyl]
def priorityRoles : List WrittenLigandRole := [.fluorine, .bridge, .methyl, .hydrogen]

/-! Closed numeral reductions of the generic `compare` (the `Nat` `Ord` instance). -/
@[simp] theorem role_compare_0_0 : compare (0 : Nat) 0 = Ordering.eq := by decide
@[simp] theorem role_compare_0_1 : compare (0 : Nat) 1 = Ordering.lt := by decide
@[simp] theorem role_compare_0_2 : compare (0 : Nat) 2 = Ordering.lt := by decide
@[simp] theorem role_compare_0_3 : compare (0 : Nat) 3 = Ordering.lt := by decide
@[simp] theorem role_compare_1_0 : compare (1 : Nat) 0 = Ordering.gt := by decide
@[simp] theorem role_compare_1_1 : compare (1 : Nat) 1 = Ordering.eq := by decide
@[simp] theorem role_compare_1_2 : compare (1 : Nat) 2 = Ordering.lt := by decide
@[simp] theorem role_compare_1_3 : compare (1 : Nat) 3 = Ordering.lt := by decide
@[simp] theorem role_compare_2_0 : compare (2 : Nat) 0 = Ordering.gt := by decide
@[simp] theorem role_compare_2_1 : compare (2 : Nat) 1 = Ordering.gt := by decide
@[simp] theorem role_compare_2_2 : compare (2 : Nat) 2 = Ordering.eq := by decide
@[simp] theorem role_compare_2_3 : compare (2 : Nat) 3 = Ordering.lt := by decide
@[simp] theorem role_compare_3_0 : compare (3 : Nat) 0 = Ordering.gt := by decide
@[simp] theorem role_compare_3_1 : compare (3 : Nat) 1 = Ordering.gt := by decide
@[simp] theorem role_compare_3_2 : compare (3 : Nat) 2 = Ordering.gt := by decide
@[simp] theorem role_compare_3_3 : compare (3 : Nat) 3 = Ordering.eq := by decide

/-- HELPER ONLY: actual complete tracked sorting is invariant over every permutation of four
distinct roles once actual admission and the strict complete decision matrix are established.
The tail counter stays `0` because every strict decision carries `pseudo = false`. -/
theorem helper_trackedSortComplete_four_permutation (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat)
    (cursor : WrittenLigandRole → CanonicalRerootCursor) (distance : WrittenLigandRole → Nat)
    (observed : ∀ role, FrameRuntime.cursor? mol profile (.actual (cursor role)) = some (distance role))
    (decisions : ∀ left right, left ≠ right →
      FrameRuntime.decisionComplete? mol profile authoritative state fuel (cursor left) (cursor right) =
        some { ordering := compare (rolePriority left) (rolePriority right) })
    (roles : List WrittenLigandRole) (permutation : roles.Perm writtenRoles) :
    FramedCompleteRuntime.trackedSortComplete? mol profile authoritative state fuel (roles.map cursor) =
      some (priorityRoles.map cursor, 0) := by
  have count : roles.length = 4 := by simpa only [writtenRoles, List.length_cons, List.length_nil] using permutation.length_eq
  cases roles with
  | nil => simp only [List.length_nil] at count; omega
  | cons a rest =>
    cases rest with
    | nil => simp only [List.length_cons, List.length_nil] at count; omega
    | cons b rest =>
      cases rest with
      | nil => simp only [List.length_cons, List.length_nil] at count; omega
      | cons c rest =>
        cases rest with
        | nil => simp only [List.length_cons, List.length_nil] at count; omega
        | cons d rest =>
          have empty : rest = [] := List.length_eq_zero_iff.mp (by
            simp only [List.length_cons] at count
            omega)
          subst rest
          cases a <;> cases b <;> cases c <;> cases d <;>
            first
            | exfalso; revert permutation; decide
            | simp [FramedCompleteRuntime.trackedSortComplete?, FramedCompleteRuntime.trackedInsertComplete?,
                observed, decisions, rolePriority, priorityRoles]

/-- HELPER ONLY: complete adjacent decisions are exactly the three ordinary priority boundaries. -/
theorem helper_adjacentComplete_priority_roles (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat)
    (cursor : WrittenLigandRole → CanonicalRerootCursor)
    (decisions : ∀ left right, left ≠ right →
      FrameRuntime.decisionComplete? mol profile authoritative state fuel (cursor left) (cursor right) =
        some { ordering := compare (rolePriority left) (rolePriority right) }) :
    FramedCompleteRuntime.adjacentComplete? mol profile authoritative state fuel (priorityRoles.map cursor) =
      some [⟨cursor .fluorine, cursor .bridge, { ordering := .gt }⟩,
        ⟨cursor .bridge, cursor .methyl, { ordering := .gt }⟩,
        ⟨cursor .methyl, cursor .hydrogen, { ordering := .gt }⟩] := by
  simp [priorityRoles, FramedCompleteRuntime.adjacentComplete?, decisions, rolePriority]

/-- Every actual uncut occurrence child is a genuine oriented original-tree edge. -/
theorem actual_occurrence_child_eligible {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat}
    (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root center) {child : CanonicalRerootCursor}
    (member : child ∈ occurrenceLigandCursors mol center) :
    CanonicalCenterRerootCursor mol root child := by
  have real := chronological_generated_all_real tree rootBound generated
  have leaf : center.forcedLeaf = false := by
    simp [CanonicalBranchNode.forcedLeaf, real]
  unfold occurrenceLigandCursors CanonicalRerootCursor.children at member
  simp only [leaf, Bool.false_eq_true, ↓reduceIte] at member
  obtain ⟨neighbor, neighborMember, selected⟩ := List.mem_filterMap.mp member
  have shape : child = { node := neighbor, previous? := some center } := by
    exact (Option.some.inj selected).symm
  rw [shape]
  rcases generated.neighbor_cases neighborMember with parentCase | childCase
  · exact .ascending parentCase.1 parentCase.2
  · exact .descending generated childCase

/-- Atom equality identifies actual genuine cursors with the same remembered previous node. -/
theorem genuine_same_previous_cursor_unique {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat}
    (rootBound : root < mol.atomCount) {left right : CanonicalRerootCursor}
    (leftEligible : CanonicalCenterRerootCursor mol root left)
    (rightEligible : CanonicalCenterRerootCursor mol root right)
    (previous : left.previous? = right.previous?)
    (atom : left.node.atom = right.node.atom) : left = right := by
  have leftGenerated : CanonicalCenterTreeNode mol root left.node := by
    cases leftEligible with
    | descending generated member => exact CanonicalCenterTreeNode.child generated member
    | ascending generated _member => exact generated
  have rightGenerated : CanonicalCenterTreeNode mol root right.node := by
    cases rightEligible with
    | descending generated member => exact CanonicalCenterTreeNode.child generated member
    | ascending generated _member => exact generated
  have node := generated_real_node_unique tree rootBound leftGenerated rightGenerated
    (chronological_generated_all_real tree rootBound leftGenerated)
    (chronological_generated_all_real tree rootBound rightGenerated) atom
  cases left
  cases right
  simp_all

/-- HELPER ONLY: an atom-inventory permutation lifts to a cursor permutation. -/
theorem helper_genuine_inventory_perm {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat}
    (rootBound : root < mol.atomCount) (previous : CanonicalBranchNode)
    (left right : List CanonicalRerootCursor)
    (leftGenuine : ∀ cursor ∈ left, CanonicalCenterRerootCursor mol root cursor)
    (rightGenuine : ∀ cursor ∈ right, CanonicalCenterRerootCursor mol root cursor)
    (leftPrevious : ∀ cursor ∈ left, cursor.previous? = some previous)
    (rightPrevious : ∀ cursor ∈ right, cursor.previous? = some previous)
    (distinct : (right.map fun cursor => cursor.node.atom).Nodup)
    (atoms : (left.map fun cursor => cursor.node.atom).Perm
      (right.map fun cursor => cursor.node.atom)) : left.Perm right := by
  have leftDistinct : left.Nodup := List.Nodup.of_map _ (atoms.nodup_iff.mpr distinct)
  have rightDistinct : right.Nodup := List.Nodup.of_map _ distinct
  apply (List.perm_ext_iff_of_nodup leftDistinct rightDistinct).mpr
  intro cursor
  constructor
  · intro member
    have atomMember : cursor.node.atom ∈ right.map (fun item => item.node.atom) :=
      atoms.mem_iff.mp (List.mem_map.mpr ⟨cursor, member, rfl⟩)
    obtain ⟨other, otherMember, same⟩ := List.mem_map.mp atomMember
    have identity := genuine_same_previous_cursor_unique tree rootBound
      (leftGenuine cursor member) (rightGenuine other otherMember)
      ((leftPrevious cursor member).trans (rightPrevious other otherMember).symm) same.symm
    rw [identity]
    exact otherMember
  · intro member
    have atomMember : cursor.node.atom ∈ left.map (fun item => item.node.atom) :=
      atoms.mem_iff.mpr (List.mem_map.mpr ⟨cursor, member, rfl⟩)
    obtain ⟨other, otherMember, same⟩ := List.mem_map.mp atomMember
    have identity := genuine_same_previous_cursor_unique tree rootBound
      (rightGenuine cursor member) (leftGenuine other otherMember)
      ((rightPrevious cursor member).trans (leftPrevious other otherMember).symm) same.symm
    rw [identity]
    exact otherMember

/-- Actual reverse family comparison, deriving all local sphere facts from maintained raw rows. -/
theorem family_actual_reverse_decisive_child_spheres (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center bridge methyl : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (bridgeEligible : CanonicalCenterRerootCursor (familyRaw ps) root
      { node := bridge, previous? := some center })
    (methylEligible : CanonicalCenterRerootCursor (familyRaw ps) root
      { node := methyl, previous? := some center })
    (centerAtom : center.atom = 1 + 12 * i.val + 5)
    (bridgeAtom : bridge.atom = 1 + 12 * i.val + 2)
    (methylAtom : methyl.atom = 1 + 12 * i.val + 8)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage) :
    FrameRuntime.compareBranch? (familyRaw ps) (generatedProfile (familyRaw ps) root center)
      authoritative (fuel + 1) stage
      (.actual { node := methyl, previous? := some center })
      (.actual { node := bridge, previous? := some center }) = some .lt := by
  let bridgeCursor : CanonicalRerootCursor := { node := bridge, previous? := some center }
  let methylCursor : CanonicalRerootCursor := { node := methyl, previous? := some center }
  have bridgeGenerated := (genuine_edge_generated bridgeEligible).1
  have methylGenerated := (genuine_edge_generated methylEligible).1
  have bridgeIDs := family_bridge_child_ids ps i rootBound bridgeGenerated centerGenerated bridgeAtom centerAtom
  have methylIDs := family_methyl_child_ids ps i rootBound methylGenerated centerGenerated methylAtom centerAtom
  have bridgeThree : (bridgeCursor.children (familyRaw ps)).length = 3 := by
    simpa only [bridgeCursor, List.length_map, List.length_cons, List.length_nil] using bridgeIDs.length_eq
  have methylThree : (methylCursor.children (familyRaw ps)).length = 3 := by
    simpa only [methylCursor, List.length_map, List.length_cons, List.length_nil] using methylIDs.length_eq
  have carbonMapped : 1 + 12 * i.val ∈
      (bridgeCursor.children (familyRaw ps)).map (fun child => child.node.atom) :=
    bridgeIDs.mem_iff.mpr List.mem_cons_self
  obtain ⟨carbon, carbonMember, carbonAtom⟩ := List.mem_map.mp carbonMapped
  have expectedNodup : [1 + 12 * i.val, 1 + 12 * i.val + 3, 1 + 12 * i.val + 4].Nodup := by
    simp
  have atomNodup := bridgeIDs.nodup_iff.mpr expectedNodup
  have bridgeHydrogens : ∀ child ∈ bridgeCursor.children (familyRaw ps), child ≠ carbon →
      PhysicalHydrogenCursor (familyRaw ps) root center child := by
    intro child member different
    have atomMember : child.node.atom ∈ [1 + 12 * i.val, 1 + 12 * i.val + 3, 1 + 12 * i.val + 4] :=
      bridgeIDs.mem_iff.mp (List.mem_map.mpr ⟨child, member, rfl⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at atomMember
    rcases atomMember with zero | three | four
    · exact (different (List.inj_on_of_nodup_map atomNodup member carbonMember (zero.trans carbonAtom.symm))).elim
    · exact family_actual_hydrogen_child ps i 3 (by simp) bridgeEligible member centerAtom
        (by simpa only [bridgeCursor, comparisonHydrogenParent] using bridgeAtom) three
    · exact family_actual_hydrogen_child ps i 4 (by simp) bridgeEligible member centerAtom
        (by simpa only [bridgeCursor, comparisonHydrogenParent] using bridgeAtom) four
  have methylHydrogens : ∀ child ∈ methylCursor.children (familyRaw ps),
      PhysicalHydrogenCursor (familyRaw ps) root center child := by
    intro child member
    have atomMember : child.node.atom ∈ [1 + 12 * i.val + 9, 1 + 12 * i.val + 10, 1 + 12 * i.val + 11] :=
      methylIDs.mem_iff.mp (List.mem_map.mpr ⟨child, member, rfl⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at atomMember
    rcases atomMember with nine | ten | eleven
    · exact family_actual_hydrogen_child ps i 9 (by simp) methylEligible member centerAtom
        (by simpa only [methylCursor, comparisonHydrogenParent] using methylAtom) nine
    · exact family_actual_hydrogen_child ps i 10 (by simp) methylEligible member centerAtom
        (by simpa only [methylCursor, comparisonHydrogenParent] using methylAtom) ten
    · exact family_actual_hydrogen_child ps i 11 (by simp) methylEligible member centerAtom
        (by simpa only [methylCursor, comparisonHydrogenParent] using methylAtom) eleven
  have bridgeLabel : (familyRaw ps).atomZAt bridge.atom = 6 := by
    rw [bridgeAtom]
    simpa [roleAtom, roleOfOffset, carbonSpec, atomSpec, Element.atomicNumber] using
      familyRaw_role_Z ps i 2 (by decide)
  have methylLabel : (familyRaw ps).atomZAt methyl.atom = 6 := by
    rw [methylAtom]
    simpa [roleAtom, roleOfOffset, carbonSpec, atomSpec, Element.atomicNumber] using
      familyRaw_role_Z ps i 8 (by decide)
  have carbonLabel : (familyRaw ps).atomZAt carbon.node.atom = 6 := by
    rw [carbonAtom]
    exact (familyRaw_interior_carbon_Z ps i).1
  exact actual_three_child_sphere_reverse_decision (familyRaw_chronologicalPhysicalTree ps) rootBound
    centerGenerated bridgeEligible methylEligible bridgeLabel methylLabel bridgeThree methylThree
    carbonMember carbonLabel bridgeHydrogens methylHydrogens authoritative fuel stage

/-- The actual occurrence inventory is a permutation of the physical written ligand IDs. -/
theorem family_actual_occurrence_atoms (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (centerAtom : center.atom = 1 + 12 * i.val + 5) :
    ((occurrenceLigandCursors (familyRaw ps) center).map (fun cursor => cursor.node.atom)).Perm
      [1 + 12 * i.val + 2, 1 + 12 * i.val + 6,
       1 + 12 * i.val + 7, 1 + 12 * i.val + 8] := by
  have actual := generated_no_previous_atoms_perm (familyRaw_chronologicalPhysicalTree ps)
    rootBound generated
  rw [centerAtom, rawIncident_eq_recordNeighbors, familyRaw_tag_records] at actual
  exact actual

/-- The family tag has exactly four physical occurrence cursors, at every bounded discovery root. -/
theorem family_actual_occurrence_length (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (centerAtom : center.atom = 1 + 12 * i.val + 5) :
    (occurrenceLigandCursors (familyRaw ps) center).length = 4 := by
  simpa only [List.length_map, List.length_cons, List.length_nil] using
    (family_actual_occurrence_atoms ps i rootBound generated centerAtom).length_eq

/-- The actual written row has four entries, so the lone-pair path cannot change it. -/
theorem family_actual_written_ligands (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).ligandsWithLonePair (1 + 12 * i.val + 5) =
      [1 + 12 * i.val + 2, 1 + 12 * i.val + 6,
       1 + 12 * i.val + 7, 1 + 12 * i.val + 8] := by
  unfold RawMolecule.ligandsWithLonePair
  rw [familyRaw_tag_written]
  cases (familyRaw ps).atomAt? (1 + 12 * i.val + 5) <;> simp

/-- The literal frame constructor succeeds with its actual parent-first physical inventory. -/
theorem family_actual_occurrence_frame (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (centerAtom : center.atom = 1 + 12 * i.val + 5) :
    occurrenceLigandFrame? (familyRaw ps) center =
      some (occurrenceLigandCursors (familyRaw ps) center) := by
  have count := family_actual_occurrence_length ps i rootBound generated centerAtom
  unfold occurrenceLigandFrame?
  rw [centerAtom, family_actual_written_ligands]
  simp [count]

def roleOffset : WrittenLigandRole → Nat
  | .bridge => 2
  | .hydrogen => 6
  | .fluorine => 7
  | .methyl => 8

/-- Every actual family frame admits a four-role description, internally chosen from
physical inventory membership. -/
theorem family_actual_frame_roles (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (centerAtom : center.atom = 1 + 12 * i.val + 5) :
    ∃ cursor : WrittenLigandRole → CanonicalRerootCursor,
      (∀ role, CanonicalCenterRerootCursor (familyRaw ps) root (cursor role)) ∧
      (∀ role, (cursor role).previous? = some center) ∧
      (∀ role, (cursor role).node.atom = 1 + 12 * i.val + roleOffset role) ∧
      (occurrenceLigandCursors (familyRaw ps) center).Perm (writtenRoles.map cursor) := by
  classical
  let physical := occurrenceLigandCursors (familyRaw ps) center
  have atoms := family_actual_occurrence_atoms ps i rootBound generated centerAtom
  have chooseRole : ∀ role : WrittenLigandRole, ∃ child ∈ physical,
      child.node.atom = 1 + 12 * i.val + roleOffset role := by
    intro role
    have member : 1 + 12 * i.val + roleOffset role ∈ physical.map (fun child => child.node.atom) := by
      apply atoms.mem_iff.mpr
      cases role <;> simp [roleOffset]
    obtain ⟨child, member, atom⟩ := List.mem_map.mp member
    exact ⟨child, member, atom⟩
  choose cursor membership atom using chooseRole
  have eligible : ∀ role, CanonicalCenterRerootCursor (familyRaw ps) root (cursor role) := by
    intro role
    exact actual_occurrence_child_eligible (familyRaw_chronologicalPhysicalTree ps)
      rootBound generated (membership role)
  have previous : ∀ role, (cursor role).previous? = some center := by
    intro role
    exact actual_child_previous (membership role)
  refine ⟨cursor, eligible, previous, atom, ?_⟩
  have mapped : (writtenRoles.map cursor).map (fun child => child.node.atom) =
      [1 + 12 * i.val + 2, 1 + 12 * i.val + 6,
       1 + 12 * i.val + 7, 1 + 12 * i.val + 8] := by
    simp [writtenRoles, atom, roleOffset]
  apply helper_genuine_inventory_perm (familyRaw_chronologicalPhysicalTree ps) rootBound center
  · intro child member
    exact actual_occurrence_child_eligible (familyRaw_chronologicalPhysicalTree ps)
      rootBound generated member
  · intro child member
    obtain ⟨role, _roleMember, rfl⟩ := List.mem_map.mp member
    exact eligible role
  · intro child member
    exact actual_child_previous member
  · intro child member
    obtain ⟨role, _roleMember, rfl⟩ := List.mem_map.mp member
    exact previous role
  · rw [mapped]
    simp
  · rw [mapped]
    exact atoms

/-- HELPER ONLY: a actual cursor-inventory permutation can be represented by a role permutation. -/
theorem helper_frame_role_representation (cursor : WrittenLigandRole → CanonicalRerootCursor)
    (physical : List CanonicalRerootCursor) (inventory : physical.Perm (writtenRoles.map cursor)) :
    ∃ roles : List WrittenLigandRole, physical = roles.map cursor ∧ roles.Perm writtenRoles := by
  have lifted : Relation.Comp (fun actual roles => actual = roles.map cursor)
      List.Perm physical writtenRoles := by
    rw [List.eq_map_comp_perm]
    exact inventory
  exact lifted

def roleAtomicNumber : WrittenLigandRole → Nat
  | .bridge | .methyl => 6
  | .hydrogen => 1
  | .fluorine => 9

/-- Raw maintained role metadata supplies the real atomic labels; no comparison is an input. -/
theorem family_role_atomic_labels (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (cursor : WrittenLigandRole → CanonicalRerootCursor)
    (atoms : ∀ role, (cursor role).node.atom = 1 + 12 * i.val + roleOffset role) :
    ∀ role, (familyRaw ps).atomZAt (cursor role).node.atom = roleAtomicNumber role := by
  intro role
  rw [atoms]
  cases role <;> simp only [roleOffset, roleAtomicNumber]
  · simpa [roleAtom, roleOfOffset, carbonSpec, atomSpec, Element.atomicNumber] using
      familyRaw_role_Z ps i 2 (by decide)
  · simpa [roleAtom, roleOfOffset, hydrogenSpec, atomSpec, Element.atomicNumber] using
      familyRaw_role_Z ps i 6 (by decide)
  · simpa [roleAtom, roleOfOffset, fluorineSpec, atomSpec, Element.atomicNumber] using
      familyRaw_role_Z ps i 7 (by decide)
  · simpa [roleAtom, roleOfOffset, carbonSpec, atomSpec, Element.atomicNumber] using
      familyRaw_role_Z ps i 8 (by decide)



theorem family_complete_role_decisions (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (centerAtom : center.atom = 1 + 12 * i.val + 5)
    (cursor : WrittenLigandRole → CanonicalRerootCursor)
    (eligible : ∀ role, CanonicalCenterRerootCursor (familyRaw ps) root (cursor role))
    (previous : ∀ role, (cursor role).previous? = some center)
    (atoms : ∀ role, (cursor role).node.atom = 1 + 12 * i.val + roleOffset role)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat) :
    ∀ left right, left ≠ right →
      FrameRuntime.decisionComplete? (familyRaw ps) (generatedProfile (familyRaw ps) root center)
        authoritative state (fuel + 1) (cursor left) (cursor right) =
        some { ordering := compare (rolePriority left) (rolePriority right) } := by
  have labels := family_role_atomic_labels ps i cursor atoms
  have shape : ∀ role, cursor role = { node := (cursor role).node, previous? := some center } := by
    intro role
    cases h : cursor role with
    | mk node prev =>
        have prevEq : prev = some center := by
          have hp := previous role
          rw [h] at hp
          exact hp
        simp [prevEq]
  have bridgeEligible := eligible .bridge
  have methylEligible := eligible .methyl
  rw [shape .bridge] at bridgeEligible
  rw [shape .methyl] at methylEligible
  have forward := family_actual_decisive_child_spheres ps i rootBound generated bridgeEligible
    methylEligible centerAtom (atoms .bridge) (atoms .methyl) authoritative fuel .rule2
  have reverse := family_actual_reverse_decisive_child_spheres ps i rootBound generated bridgeEligible
    methylEligible centerAtom (atoms .bridge) (atoms .methyl) authoritative fuel .rule2
  have forwardDecision : FrameRuntime.decisionComplete? (familyRaw ps)
      (generatedProfile (familyRaw ps) root center) authoritative state (fuel + 1)
      (cursor .bridge) (cursor .methyl) = some { ordering := .gt } := by
    have h : FrameRuntime.compareBranch? (familyRaw ps) (generatedProfile (familyRaw ps) root center)
        authoritative (fuel + 1) .rule2 (.actual (cursor .bridge)) (.actual (cursor .methyl)) =
        some Ordering.gt := by
      rw [shape .bridge, shape .methyl]
      exact forward
    exact decisionComplete_strict_of_neq (familyRaw ps) (generatedProfile (familyRaw ps) root center)
      authoritative state (fuel + 1) (cursor .bridge) (cursor .methyl) Ordering.gt h (by decide)
  have reverseDecision : FrameRuntime.decisionComplete? (familyRaw ps)
      (generatedProfile (familyRaw ps) root center) authoritative state (fuel + 1)
      (cursor .methyl) (cursor .bridge) = some { ordering := .lt } := by
    have h : FrameRuntime.compareBranch? (familyRaw ps) (generatedProfile (familyRaw ps) root center)
        authoritative (fuel + 1) .rule2 (.actual (cursor .methyl)) (.actual (cursor .bridge)) =
        some Ordering.lt := by
      rw [shape .methyl, shape .bridge]
      exact reverse
    exact decisionComplete_strict_of_neq (familyRaw ps) (generatedProfile (familyRaw ps) root center)
      authoritative state (fuel + 1) (cursor .methyl) (cursor .bridge) Ordering.lt h (by decide)
  have atomic : ∀ left right, roleAtomicNumber left ≠ roleAtomicNumber right →
      FrameRuntime.decisionComplete? (familyRaw ps) (generatedProfile (familyRaw ps) root center)
        authoritative state (fuel + 1) (cursor left) (cursor right) =
        some { ordering := compare (roleAtomicNumber left) (roleAtomicNumber right) } := by
    intro left right different
    have distinct : (familyRaw ps).atomZAt (cursor left).node.atom ≠
        (familyRaw ps).atomZAt (cursor right).node.atom := by
      simpa only [labels] using different
    simpa only [labels] using complete_atomic_decision (familyRaw_chronologicalPhysicalTree ps)
      rootBound generated (eligible left) (eligible right) distinct authoritative state (fuel + 1)
  intro left right different
  cases left <;> cases right <;>
    first
    | exact (different rfl).elim
    | simpa [rolePriority] using forwardDecision
    | simpa [rolePriority] using reverseDecision
    | simpa [roleAtomicNumber, rolePriority] using atomic .bridge .hydrogen (by decide)
    | simpa [roleAtomicNumber, rolePriority] using atomic .bridge .fluorine (by decide)
    | simpa [roleAtomicNumber, rolePriority] using atomic .hydrogen .bridge (by decide)
    | simpa [roleAtomicNumber, rolePriority] using atomic .hydrogen .fluorine (by decide)
    | simpa [roleAtomicNumber, rolePriority] using atomic .hydrogen .methyl (by decide)
    | simpa [roleAtomicNumber, rolePriority] using atomic .fluorine .bridge (by decide)
    | simpa [roleAtomicNumber, rolePriority] using atomic .fluorine .hydrogen (by decide)
    | simpa [roleAtomicNumber, rolePriority] using atomic .fluorine .methyl (by decide)
    | simpa [roleAtomicNumber, rolePriority] using atomic .methyl .hydrogen (by decide)
    | simpa [roleAtomicNumber, rolePriority] using atomic .methyl .fluorine (by decide)

/-- Complete tracked sorting and adjacent comparisons for every maintained family tag,
independent of its original-parent-first enumeration, for both modes and every state. -/
theorem family_complete_sort_and_adjacent (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (centerAtom : center.atom = 1 + 12 * i.val + 5)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat) :
    ∃ cursor : WrittenLigandRole → CanonicalRerootCursor,
      (∀ role, (cursor role).node.atom = 1 + 12 * i.val + roleOffset role) ∧
      FramedCompleteRuntime.trackedSortComplete? (familyRaw ps) (generatedProfile (familyRaw ps) root center)
        authoritative state (fuel + 1) (occurrenceLigandCursors (familyRaw ps) center) =
        some (priorityRoles.map cursor, 0) ∧
      FramedCompleteRuntime.adjacentComplete? (familyRaw ps) (generatedProfile (familyRaw ps) root center)
        authoritative state (fuel + 1) (priorityRoles.map cursor) =
        some [⟨cursor .fluorine, cursor .bridge, { ordering := .gt }⟩,
          ⟨cursor .bridge, cursor .methyl, { ordering := .gt }⟩,
          ⟨cursor .methyl, cursor .hydrogen, { ordering := .gt }⟩] := by
  obtain ⟨cursor, eligible, previous, atoms, inventory⟩ :=
    family_actual_frame_roles ps i rootBound generated centerAtom
  obtain ⟨roles, actualRoles, permutation⟩ := helper_frame_role_representation cursor
    (occurrenceLigandCursors (familyRaw ps) center) inventory
  have observations : ∀ role, FrameRuntime.cursor? (familyRaw ps)
      (generatedProfile (familyRaw ps) root center) (.actual (cursor role)) =
        some ((TetraStereo.UniversalProof.NativeChronologicalTreeAcyclic.physicalGraph (familyRaw ps)).dist center.atom (cursor role).node.atom) := by
    intro role
    exact genuine_cursor_observed (familyRaw_chronologicalPhysicalTree ps) rootBound generated
      (eligible role)
  have decisions := family_complete_role_decisions ps i rootBound generated centerAtom cursor
    eligible previous atoms authoritative state fuel
  refine ⟨cursor, atoms, ?_, ?_⟩
  · rw [actualRoles]
    exact helper_trackedSortComplete_four_permutation (familyRaw ps)
      (generatedProfile (familyRaw ps) root center) authoritative state (fuel + 1) cursor
      (fun role => (TetraStereo.UniversalProof.NativeChronologicalTreeAcyclic.physicalGraph (familyRaw ps)).dist center.atom (cursor role).node.atom)
      observations decisions roles permutation
  · exact helper_adjacentComplete_priority_roles (familyRaw ps) (generatedProfile (familyRaw ps) root center)
      authoritative state (fuel + 1) cursor decisions

/-- Literal written-ID searches produce the source parity positions. -/
theorem family_actual_priority_positions (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (cursor : WrittenLigandRole → CanonicalRerootCursor)
    (atoms : ∀ role, (cursor role).node.atom = 1 + 12 * i.val + roleOffset role) :
    (priorityRoles.map cursor).mapM (fun child =>
      (((familyRaw ps).ligandsWithLonePair (1 + 12 * i.val + 5)).zipIdx.find?
        (fun entry => entry.1 == child.node.atom)).map Prod.snd) = some [2, 0, 3, 1] := by
  rw [family_actual_written_ligands]
  simp [priorityRoles, atoms, roleOffset]




theorem family_complete_occurrence_fact (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (centerAtom : center.atom = 1 + 12 * i.val + 5)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat) :
    FramedCompleteRuntime.occurrenceFactComplete? (familyRaw ps) authoritative (fuel + 1) state center =
      some { key := canonicalOccurrenceKey center
             atom := center.atom
             descriptor := RawMolecule.descriptorOfParity (ps.get i) false
             uppercase := true
             priorityPositions := [2, 0, 3, 1] } := by
  obtain ⟨cursor, atoms, sorted, adjacent⟩ := family_complete_sort_and_adjacent ps i rootBound
    generated centerAtom authoritative state fuel
  have profile := actual_profile_obtained (familyRaw_chronologicalPhysicalTree ps) rootBound generated
  have frame := family_actual_occurrence_frame ps i rootBound generated centerAtom
  have atom : (familyRaw ps).atomAt? center.atom =
      some (atomSpec (.taggedCarbon (ps.get i))) := by
    rw [centerAtom, familyRaw_role_atom ps i 5 (by decide)]
    rfl
  have positions := family_actual_priority_positions ps i cursor atoms
  have positioned : (priorityRoles.map cursor).mapM (fun child =>
      (((familyRaw ps).ligandsWithLonePair center.atom).zipIdx.find?
        (fun entry => entry.1 == child.node.atom)).map Prod.snd) = some [2, 0, 3, 1] := by
    simpa only [centerAtom] using positions
  simp [FramedCompleteRuntime.occurrenceFactComplete?, profile, atom, atomSpec, frame, sorted,
    positioned, adjacent, RawMolecule.permutationIsEven, RawMolecule.inversionCount]

/-- Every actual maintained written tag is inhabited by a genuine node at any bounded root, and the
complete caller returns the same precise written-parity fact in both modes. For ps=[] there is no
`Fin ps.length` tag; no phantom request is introduced. -/
theorem family_every_written_tag_complete_facts (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    (state : OccurrenceAuxState) (fuel : Nat) :
    ∃ center, CanonicalCenterTreeNode (familyRaw ps) root center ∧
      center.atom = 1 + 12 * i.val + 5 ∧
      FramedCompleteRuntime.occurrenceFactComplete? (familyRaw ps) false (fuel + 1) state center =
        some { key := canonicalOccurrenceKey center
               atom := center.atom
               descriptor := RawMolecule.descriptorOfParity (ps.get i) false
               uppercase := true
               priorityPositions := [2, 0, 3, 1] } ∧
      FramedCompleteRuntime.occurrenceFactComplete? (familyRaw ps) true (fuel + 1) state center =
        some { key := canonicalOccurrenceKey center
               atom := center.atom
               descriptor := RawMolecule.descriptorOfParity (ps.get i) false
               uppercase := true
               priorityPositions := [2, 0, 3, 1] } := by
  obtain ⟨center, generated, atom⟩ := family_written_tag_generated ps i rootBound
  have centerAtom : center.atom = 1 + 12 * i.val + 5 := by
    unfold tagIndex at atom
    omega
  exact ⟨center, generated, centerAtom,
    family_complete_occurrence_fact ps i rootBound generated centerAtom false state fuel,
    family_complete_occurrence_fact ps i rootBound generated centerAtom true state fuel⟩

end TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller
