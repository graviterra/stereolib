import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalProfileSuccess
import TetraStereo.UniversalProof.NextFrontier.NativeGeneratedPhysicalFrameMetric
import TetraStereo.UniversalProof.NextFrontier.NativeGeneratedCursorPhysicalCut

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeFramedCursorObservations
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeChronologicalProfileSuccess
open TetraStereo.UniversalProof.NativeChronologicalChildMultiplicity
open TetraStereo.UniversalProof.NativeGeneratedPhysicalFrameMetric
open TetraStereo.UniversalProof.NativeChronologicalTreeAcyclic

/-- Computed shared profile value; admission is proved below, not supplied as a caller field. -/
def generatedProfile (mol : RawMolecule) (root : Nat) (center : CanonicalBranchNode) :
    FrameRuntime.Profile :=
  ⟨center, ⟨center.history⟩,
    NativeGlobalProfileInventory.inventory mol root (mol.atomCount + 1)⟩

/-- The actual private runtime request obtains exactly the shared computed profile. -/
theorem actual_profile_obtained {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center) :
    FrameRuntime.profile? mol center = some (generatedProfile mol root center) :=
  chronological_profile_success tree rootBound centerGenerated

/-- Actual cursor checks admit a genuinely generated incoming edge and return physical distance. -/
theorem actual_edge_observed {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center node previous : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (nodeGenerated : CanonicalCenterTreeNode mol root node)
    (previousGenerated : CanonicalCenterTreeNode mol root previous)
    (incoming : previous ∈ ({ node := node } : CanonicalRerootCursor).neighbors mol) :
    FrameRuntime.cursor? mol (generatedProfile mol root center)
      (.actual { node := node, previous? := some previous }) =
        some ((physicalGraph mol).dist center.atom node.atom) := by
  have nodeMember := chronological_center_mem_inventory tree rootBound nodeGenerated
  have previousMember := chronological_center_mem_inventory tree rootBound previousGenerated
  have incoming' : previous ∈
      ({ node := node, previous? := some previous } : CanonicalRerootCursor).neighbors mol := incoming
  have real := chronological_generated_all_real tree rootBound nodeGenerated
  have distance := generated_frame_realDistance_eq_physical_distance tree rootBound
    centerGenerated nodeGenerated (chronological_generated_all_real tree rootBound centerGenerated) real
  simp [FrameRuntime.cursor?, generatedProfile, nodeMember, previousMember, incoming', real,
    CanonicalComparisonFrame.observeNode, distance]

/-- Both original-tree directions pass the actual profile membership and previous-edge checks. -/
theorem genuine_cursor_observed {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center) {cursor : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor mol root cursor) :
    FrameRuntime.cursor? mol (generatedProfile mol root center) (.actual cursor) =
      some ((physicalGraph mol).dist center.atom cursor.node.atom) := by
  cases eligible with
  | @descending parent node parentGenerated member =>
      have recovered := canonicalOriginalParent?_eq_some_of_child parentGenerated member
      have incoming : parent ∈ ({ node := node } : CanonicalRerootCursor).neighbors mol := by
        simp [CanonicalRerootCursor.neighbors, recovered]
      exact actual_edge_observed tree rootBound centerGenerated
        (CanonicalCenterTreeNode.child parentGenerated member) parentGenerated incoming
  | @ascending node previous nodeGenerated member =>
      have incoming : previous ∈ ({ node := node } : CanonicalRerootCursor).neighbors mol := by
        exact List.mem_append_right _ member
      exact actual_edge_observed tree rootBound centerGenerated nodeGenerated
        (CanonicalCenterTreeNode.child nodeGenerated member) incoming

/-- Every actual child observation used by ranked? succeeds; no mapM result is a hypothesis. -/
theorem genuine_children_observed {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center) {cursor : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor mol root cursor) :
    ((cursor.children mol).map FrameRuntime.Cursor.actual).mapM
      (FrameRuntime.cursor? mol (generatedProfile mol root center)) =
        some ((cursor.children mol).map (fun child => (physicalGraph mol).dist center.atom child.node.atom)) := by
  have observations : ∀ child ∈ cursor.children mol,
      FrameRuntime.cursor? mol (generatedProfile mol root center) (.actual child) =
        some ((physicalGraph mol).dist center.atom child.node.atom) := by
    intro child member
    exact genuine_cursor_observed tree rootBound centerGenerated (eligible.child member)
  have lists : ∀ nodes : List CanonicalRerootCursor,
      (∀ child ∈ nodes, FrameRuntime.cursor? mol (generatedProfile mol root center) (.actual child) =
        some ((physicalGraph mol).dist center.atom child.node.atom)) →
      (nodes.map FrameRuntime.Cursor.actual).mapM (FrameRuntime.cursor? mol (generatedProfile mol root center)) =
        some (nodes.map (fun child => (physicalGraph mol).dist center.atom child.node.atom)) := by
    intro nodes checked
    induction nodes with
    | nil => rfl
    | cons child nodes ih =>
        have observed := checked child List.mem_cons_self
        have tail := ih (fun other member => checked other (List.mem_cons_of_mem child member))
        simp only [List.map_cons, List.mapM_cons, observed, tail, Bind.bind, Option.bind, Option.pure_def]
  exact lists _ observations

/-- Both actual fast and authoritative Rule1a labels are the real physical atomic-number comparison. -/
theorem actual_rule1a_labels {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {left right : CanonicalRerootCursor}
    (leftEligible : CanonicalCenterRerootCursor mol root left)
    (rightEligible : CanonicalCenterRerootCursor mol root right) (authoritative : Bool) :
    FrameRuntime.label? mol (generatedProfile mol root center) authoritative .rule1a
      (.actual left) (.actual right) = some (compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom)) := by
  have leftObserved := genuine_cursor_observed tree rootBound centerGenerated leftEligible
  have rightObserved := genuine_cursor_observed tree rootBound centerGenerated rightEligible
  have leftGenerated : CanonicalCenterTreeNode mol root left.node := by
    cases leftEligible with
    | descending generated member => exact CanonicalCenterTreeNode.child generated member
    | ascending generated _member => exact generated
  have rightGenerated : CanonicalCenterTreeNode mol root right.node := by
    cases rightEligible with
    | descending generated member => exact CanonicalCenterTreeNode.child generated member
    | ascending generated _member => exact generated
  have leftReal := chronological_generated_all_real tree rootBound leftGenerated
  have rightReal := chronological_generated_all_real tree rootBound rightGenerated
  cases authoritative <;>
    simp [FrameRuntime.label?, FrameRuntime.Cursor.original, leftObserved, rightObserved,
      RawMolecule.compareCanonicalNodeRule?, RawMolecule.compareCanonicalNodeRuleAuthoritative?,
      RawMolecule.canonicalRule1aLabel?, RawMolecule.canonicalRule1aLabelAuthoritative?,
      leftReal, rightReal, compareCIPAtomicLabel, CIPAtomicLabel.effectiveDenominator]

/-- Rule1b uses the common physical center's actual distances in both runtime modes. -/
theorem actual_rule1b_labels {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {left right : CanonicalRerootCursor}
    (leftEligible : CanonicalCenterRerootCursor mol root left)
    (rightEligible : CanonicalCenterRerootCursor mol root right) (authoritative : Bool) :
    FrameRuntime.label? mol (generatedProfile mol root center) authoritative .rule1b
      (.actual left) (.actual right) =
        some (if (physicalGraph mol).dist center.atom left.node.atom <
            (physicalGraph mol).dist center.atom right.node.atom then .gt
          else if (physicalGraph mol).dist center.atom right.node.atom <
            (physicalGraph mol).dist center.atom left.node.atom then .lt else .eq) := by
  have leftObserved := genuine_cursor_observed tree rootBound centerGenerated leftEligible
  have rightObserved := genuine_cursor_observed tree rootBound centerGenerated rightEligible
  simp [FrameRuntime.label?, leftObserved, rightObserved]

/-- Different actual atomic numbers decide every stage at every fuel without expanding further spheres.
The independent atomic-number inequality is not a supplied comparator or output result. -/
theorem actual_strict_atomic_branch {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {left right : CanonicalRerootCursor}
    (leftEligible : CanonicalCenterRerootCursor mol root left)
    (rightEligible : CanonicalCenterRerootCursor mol root right)
    (different : mol.atomZAt left.node.atom ≠ mol.atomZAt right.node.atom)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage) :
    FrameRuntime.compareBranch? mol (generatedProfile mol root center) authoritative fuel stage
      (.actual left) (.actual right) = some (compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom)) := by
  have atomic := actual_rule1a_labels tree rootBound centerGenerated leftEligible rightEligible authoritative
  have strict : compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) ≠ Ordering.eq := by
    intro equal
    exact different (Nat.compare_eq_eq.mp equal)
  have strictRule (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
      (remaining : Nat) :
      FrameRuntime.compareRule? mol (generatedProfile mol root center) authoritative before
        .rule1a remaining [(.actual left, .actual right)] =
          some (compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom)) := by
    rw [FrameRuntime.compareRule?]
    simp [FrameRuntime.pairLabels?, atomic, strict, defaultBranchWidthCap]
  cases fuel with
  | zero =>
      rw [FrameRuntime.compareBranch?]
      simp [FrameRuntime.throughLabels?, atomic, strict]
  | succ remaining =>
      rw [FrameRuntime.compareBranch?]
      simp only [strictRule]
      simp [strict]

/-- A physical leaf has no outgoing cursor children after cutting its actual incoming edge.
The premise specifies the independently inspectable raw bond inventory, not a child-list outcome. -/
theorem actual_physical_leaf_children_empty {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    {node previous : CanonicalBranchNode}
    (nodeGenerated : CanonicalCenterTreeNode mol root node)
    (previousGenerated : CanonicalCenterTreeNode mol root previous)
    (physicalLeaf : NativeGeneratedCursorPhysicalCut.rawIncident mol node.atom = [previous.atom]) :
    ({ node := node, previous? := some previous } : CanonicalRerootCursor).children mol = [] := by
  have cut := NativeGeneratedCursorPhysicalCut.generated_cut_atoms_perm tree rootBound
    nodeGenerated previousGenerated
  have lengthZero := cut.length_eq
  simp only [physicalLeaf, List.erase_cons_head, List.length_nil, List.length_map] at lengthZero
  exact List.length_eq_zero_iff.mp lengthZero

/-- The actual runtime terminal check follows from physical degree one, in either traversal direction. -/
theorem actual_physical_leaf_terminal {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    {node previous : CanonicalBranchNode}
    (nodeGenerated : CanonicalCenterTreeNode mol root node)
    (previousGenerated : CanonicalCenterTreeNode mol root previous)
    (physicalLeaf : NativeGeneratedCursorPhysicalCut.rawIncident mol node.atom = [previous.atom]) :
    FrameRuntime.terminal mol (.actual { node := node, previous? := some previous }) = true := by
  have emptyChildren := actual_physical_leaf_children_empty tree rootBound
    nodeGenerated previousGenerated physicalLeaf
  simp [FrameRuntime.terminal, FrameRuntime.Cursor.original, cursorTerminal, emptyChildren]

/-- The independently derived three-child family layer fits both actual runtime modes.
No fuel or total-family-size hypothesis enters this local slot bound. -/
theorem three_children_fit_actual_slots (authoritative : Bool) :
    3 ≤ (if authoritative then RawMolecule.authoritativeChildSlots else 3) := by
  cases authoritative <;> decide

/-- Actual paired expansion of two physical leaves succeeds with an empty frontier.
No sorting-comparator success is supplied: the runtime terminal branch never calls it. -/
theorem actual_physical_leaves_nextPairs {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    (profile : FrameRuntime.Profile) (authoritative : Bool)
    (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
    {left leftPrevious right rightPrevious : CanonicalBranchNode}
    (leftGenerated : CanonicalCenterTreeNode mol root left)
    (leftPreviousGenerated : CanonicalCenterTreeNode mol root leftPrevious)
    (rightGenerated : CanonicalCenterTreeNode mol root right)
    (rightPreviousGenerated : CanonicalCenterTreeNode mol root rightPrevious)
    (leftLeaf : NativeGeneratedCursorPhysicalCut.rawIncident mol left.atom = [leftPrevious.atom])
    (rightLeaf : NativeGeneratedCursorPhysicalCut.rawIncident mol right.atom = [rightPrevious.atom]) :
    FrameRuntime.nextPairs? mol profile authoritative before
      [(.actual { node := left, previous? := some leftPrevious },
        .actual { node := right, previous? := some rightPrevious })] = some [] := by
  have leftTerminal := actual_physical_leaf_terminal tree rootBound
    leftGenerated leftPreviousGenerated leftLeaf
  have rightTerminal := actual_physical_leaf_terminal tree rootBound
    rightGenerated rightPreviousGenerated rightLeaf
  simp [FrameRuntime.nextPairs?, leftTerminal, rightTerminal]

/-- Independent raw data for a hydrogen arm at physical distance two: an actual supported
three-vertex path, a degree-one bond inventory, and the actual elemental/isotope labels.
No metric, cursor membership, comparator, sorting or runtime result is stored here. -/
structure PhysicalHydrogenArm (mol : RawMolecule) (center parent leaf : Nat) : Prop where
  path : NativeGeneratedRealPaths.RawSupportedPath mol center leaf [center, parent, leaf]
  incident : NativeGeneratedCursorPhysicalCut.rawIncident mol leaf = [parent]
  atomicNumber : mol.atomZAt leaf = 1
  mass : mol.atomMassAt leaf = RawMolecule.rule2MassPico .H none

/-- Distance two follows from the raw supported path and internally derived tree acyclicity. -/
theorem physical_hydrogen_arm_distance {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {center parent leaf : Nat}
    (arm : PhysicalHydrogenArm mol center parent leaf) :
    (physicalGraph mol).dist center leaf = 2 := by
  have distance := supported_edgeCount_eq_physical_distance tree arm.path
  simpa only [NativeGeneratedRealPaths.edgeCount, List.length_cons, List.length_nil] using distance.symm

/-- Eligibility in either traversal direction supplies both actual retained endpoint nodes. -/
theorem genuine_edge_generated {mol : RawMolecule} {root : Nat}
    {node previous : CanonicalBranchNode}
    (eligible : CanonicalCenterRerootCursor mol root
      { node := node, previous? := some previous }) :
    CanonicalCenterTreeNode mol root node ∧ CanonicalCenterTreeNode mol root previous := by
  cases eligible with
  | descending generated member => exact ⟨CanonicalCenterTreeNode.child generated member, generated⟩
  | ascending generated member => exact ⟨generated, CanonicalCenterTreeNode.child generated member⟩

/-- Actual Rule2 labels on genuine real cursors use the actual isotope masses in both modes. -/
theorem actual_rule2_labels {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {left right : CanonicalRerootCursor}
    (leftEligible : CanonicalCenterRerootCursor mol root left)
    (rightEligible : CanonicalCenterRerootCursor mol root right) (authoritative : Bool) :
    FrameRuntime.label? mol (generatedProfile mol root center) authoritative .rule2
      (.actual left) (.actual right) =
        some (compare (mol.atomMassAt left.node.atom) (mol.atomMassAt right.node.atom)) := by
  have leftObserved := genuine_cursor_observed tree rootBound centerGenerated leftEligible
  have rightObserved := genuine_cursor_observed tree rootBound centerGenerated rightEligible
  have leftGenerated : CanonicalCenterTreeNode mol root left.node := by
    cases leftEligible with
    | descending generated member => exact CanonicalCenterTreeNode.child generated member
    | ascending generated _member => exact generated
  have rightGenerated : CanonicalCenterTreeNode mol root right.node := by
    cases rightEligible with
    | descending generated member => exact CanonicalCenterTreeNode.child generated member
    | ascending generated _member => exact generated
  have leftReal := chronological_generated_all_real tree rootBound leftGenerated
  have rightReal := chronological_generated_all_real tree rootBound rightGenerated
  cases authoritative <;>
    simp [FrameRuntime.label?, FrameRuntime.Cursor.original, leftObserved, rightObserved,
      RawMolecule.compareCanonicalNodeRule?, RawMolecule.compareCanonicalNodeRuleAuthoritative?,
      RawMolecule.compareCanonicalNodeRule, leftReal, rightReal]




theorem actual_hydrogen_arm_branch_tie {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center left leftParent right rightParent : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (leftEligible : CanonicalCenterRerootCursor mol root
      { node := left, previous? := some leftParent })
    (rightEligible : CanonicalCenterRerootCursor mol root
      { node := right, previous? := some rightParent })
    (leftArm : PhysicalHydrogenArm mol center.atom leftParent.atom left.atom)
    (rightArm : PhysicalHydrogenArm mol center.atom rightParent.atom right.atom)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage) :
    FrameRuntime.compareBranch? mol (generatedProfile mol root center) authoritative fuel stage
      (.actual { node := left, previous? := some leftParent })
      (.actual { node := right, previous? := some rightParent }) = some .eq := by
  have leftGenerated := genuine_edge_generated leftEligible
  have rightGenerated := genuine_edge_generated rightEligible
  have leftTerminal := actual_physical_leaf_terminal tree rootBound
    leftGenerated.1 leftGenerated.2 leftArm.incident
  have rightTerminal := actual_physical_leaf_terminal tree rootBound
    rightGenerated.1 rightGenerated.2 rightArm.incident
  have first := actual_rule1a_labels tree rootBound centerGenerated leftEligible rightEligible authoritative
  have distance := actual_rule1b_labels tree rootBound centerGenerated leftEligible rightEligible authoritative
  have mass := actual_rule2_labels tree rootBound centerGenerated leftEligible rightEligible authoritative
  have leftDistance := physical_hydrogen_arm_distance tree leftArm
  have rightDistance := physical_hydrogen_arm_distance tree rightArm
  simp only [leftArm.atomicNumber, rightArm.atomicNumber] at first
  simp only [leftDistance, rightDistance] at distance
  simp only [leftArm.mass, rightArm.mass] at mass
  have tiedLabel (rule : CanonicalRuleStage) :
      FrameRuntime.label? mol (generatedProfile mol root center) authoritative rule
        (.actual { node := left, previous? := some leftParent })
        (.actual { node := right, previous? := some rightParent }) = some .eq := by
    cases rule
    · simpa using first
    · simpa using distance
    · simpa using mass
  have tiedRule (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering)
      (rule : CanonicalRuleStage) (remaining : Nat) :
      FrameRuntime.compareRule? mol (generatedProfile mol root center) authoritative before rule
        remaining [(.actual { node := left, previous? := some leftParent },
          .actual { node := right, previous? := some rightParent })] = some .eq := by
    rw [FrameRuntime.compareRule?]
    simp [FrameRuntime.pairLabels?, tiedLabel, FrameRuntime.nextPairs?,
      leftTerminal, rightTerminal, defaultBranchWidthCap]
  cases fuel with
  | zero =>
      rw [FrameRuntime.compareBranch?]
      cases stage <;> simp [FrameRuntime.throughLabels?, tiedLabel, leftTerminal, rightTerminal]
  | succ remaining =>
      rw [FrameRuntime.compareBranch?]
      simp only [tiedRule]
      cases stage <;> simp



def PhysicalHydrogenCursor (mol : RawMolecule) (root : Nat) (center : CanonicalBranchNode)
    (cursor : CanonicalRerootCursor) : Prop :=
  ∃ node previous, cursor = { node := node, previous? := some previous } ∧
    CanonicalCenterRerootCursor mol root { node := node, previous? := some previous } ∧
    PhysicalHydrogenArm mol center.atom previous.atom node.atom

/-- The actual recursive comparator ties any two independently classified hydrogen cursors. -/
theorem actual_hydrogen_cursor_tie {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {left right : CanonicalRerootCursor}
    (leftHydrogen : PhysicalHydrogenCursor mol root center left)
    (rightHydrogen : PhysicalHydrogenCursor mol root center right)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage) :
    FrameRuntime.compareBranch? mol (generatedProfile mol root center) authoritative fuel stage
      (.actual left) (.actual right) = some .eq := by
  rcases leftHydrogen with ⟨left, leftParent, rfl, leftEligible, leftArm⟩
  rcases rightHydrogen with ⟨right, rightParent, rfl, rightEligible, rightArm⟩
  exact actual_hydrogen_arm_branch_tie tree rootBound centerGenerated leftEligible rightEligible
    leftArm rightArm authoritative fuel stage

/-- Hydrogen classification supplies actual cursor eligibility and the actual atomic label. -/
theorem physical_hydrogen_cursor_facts {mol : RawMolecule} {root : Nat}
    {center : CanonicalBranchNode} {cursor : CanonicalRerootCursor}
    (hydrogen : PhysicalHydrogenCursor mol root center cursor) :
    CanonicalCenterRerootCursor mol root cursor ∧ mol.atomZAt cursor.node.atom = 1 := by
  rcases hydrogen with ⟨node, previous, rfl, eligible, arm⟩
  exact ⟨eligible, arm.atomicNumber⟩

/-- Insertion among physical hydrogen arms succeeds directly; the actual tie branch inserts
without invoking recursive comparison or a supplied callback-result hypothesis. -/
theorem actual_hydrogen_insert {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {candidate : CanonicalRerootCursor} (candidateHydrogen : PhysicalHydrogenCursor mol root center candidate)
    (nodes : List CanonicalRerootCursor)
    (hydrogens : ∀ node ∈ nodes, PhysicalHydrogenCursor mol root center node)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage) :
    FrameRuntime.insert? (FrameRuntime.compareBranch? mol (generatedProfile mol root center)
      authoritative fuel stage) (.actual candidate) (nodes.map FrameRuntime.Cursor.actual) =
        some ((candidate :: nodes).map FrameRuntime.Cursor.actual) := by
  cases nodes with
  | nil => rfl
  | cons node nodes =>
      have tied := actual_hydrogen_cursor_tie tree rootBound centerGenerated candidateHydrogen
        (hydrogens node List.mem_cons_self) authoritative fuel stage
      simp [FrameRuntime.insert?, tied]



theorem actual_hydrogen_sort {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    (nodes : List CanonicalRerootCursor)
    (hydrogens : ∀ node ∈ nodes, PhysicalHydrogenCursor mol root center node)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage) :
    FrameRuntime.sort? (FrameRuntime.compareBranch? mol (generatedProfile mol root center)
      authoritative fuel stage) (nodes.map FrameRuntime.Cursor.actual) =
        some (nodes.map FrameRuntime.Cursor.actual) := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih =>
      have tailHydrogens : ∀ other ∈ nodes, PhysicalHydrogenCursor mol root center other :=
        fun other member => hydrogens other (List.mem_cons_of_mem node member)
      have sorted := ih tailHydrogens
      have inserted := actual_hydrogen_insert tree rootBound centerGenerated
        (hydrogens node List.mem_cons_self) nodes tailHydrogens authoritative fuel stage
      simpa only [List.map_cons, FrameRuntime.sort?, sorted, Bind.bind, Option.bind] using inserted

/-- Actual carbon/hydrogen strict callbacks are derived from actual element labels. -/
theorem actual_carbon_hydrogen_labels {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {carbon hydrogen : CanonicalRerootCursor}
    (carbonEligible : CanonicalCenterRerootCursor mol root carbon)
    (carbonLabel : mol.atomZAt carbon.node.atom = 6)
    (hydrogenPhysical : PhysicalHydrogenCursor mol root center hydrogen)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage) :
    FrameRuntime.compareBranch? mol (generatedProfile mol root center) authoritative fuel stage
      (.actual carbon) (.actual hydrogen) = some .gt ∧
    FrameRuntime.compareBranch? mol (generatedProfile mol root center) authoritative fuel stage
      (.actual hydrogen) (.actual carbon) = some .lt := by
  have hydrogenFacts := physical_hydrogen_cursor_facts hydrogenPhysical
  have unequal : mol.atomZAt carbon.node.atom ≠ mol.atomZAt hydrogen.node.atom := by
    rw [carbonLabel, hydrogenFacts.2]
    decide
  have forward := actual_strict_atomic_branch tree rootBound centerGenerated carbonEligible
    hydrogenFacts.1 unequal authoritative fuel stage
  have backward := actual_strict_atomic_branch tree rootBound centerGenerated hydrogenFacts.1
    carbonEligible unequal.symm authoritative fuel stage
  simpa only [carbonLabel, hydrogenFacts.2] using And.intro forward backward

/-- A real carbon is inserted before any physical hydrogen list by the actual callback. -/
theorem actual_carbon_insert_hydrogens {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {carbon : CanonicalRerootCursor}
    (carbonEligible : CanonicalCenterRerootCursor mol root carbon)
    (carbonLabel : mol.atomZAt carbon.node.atom = 6)
    (nodes : List CanonicalRerootCursor)
    (hydrogens : ∀ node ∈ nodes, PhysicalHydrogenCursor mol root center node)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage) :
    FrameRuntime.insert? (FrameRuntime.compareBranch? mol (generatedProfile mol root center)
      authoritative fuel stage) (.actual carbon) (nodes.map FrameRuntime.Cursor.actual) =
        some ((carbon :: nodes).map FrameRuntime.Cursor.actual) := by
  cases nodes with
  | nil => rfl
  | cons node nodes =>
      have strict := (actual_carbon_hydrogen_labels tree rootBound centerGenerated carbonEligible
        carbonLabel (hydrogens node List.mem_cons_self) authoritative fuel stage).1
      simp [FrameRuntime.insert?, strict]

/-- Hydrogen insertion crosses the genuine carbon and then takes the internally derived tie. -/
theorem actual_hydrogen_insert_after_carbon {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {carbon hydrogen : CanonicalRerootCursor}
    (carbonEligible : CanonicalCenterRerootCursor mol root carbon)
    (carbonLabel : mol.atomZAt carbon.node.atom = 6)
    (hydrogenPhysical : PhysicalHydrogenCursor mol root center hydrogen)
    (nodes : List CanonicalRerootCursor)
    (hydrogens : ∀ node ∈ nodes, PhysicalHydrogenCursor mol root center node)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage) :
    FrameRuntime.insert? (FrameRuntime.compareBranch? mol (generatedProfile mol root center)
      authoritative fuel stage) (.actual hydrogen) ((carbon :: nodes).map FrameRuntime.Cursor.actual) =
        some ((carbon :: hydrogen :: nodes).map FrameRuntime.Cursor.actual) := by
  have strict := (actual_carbon_hydrogen_labels tree rootBound centerGenerated carbonEligible
    carbonLabel hydrogenPhysical authoritative fuel stage).2
  have inserted := actual_hydrogen_insert tree rootBound centerGenerated hydrogenPhysical
    nodes hydrogens authoritative fuel stage
  simp [FrameRuntime.insert?, strict, inserted]

/-- Complete actual sorting with one genuine carbon at any position in a physical hydrogen list.
This is a general list theorem, not a chosen permutation or molecule-size fixture. -/
theorem actual_one_carbon_hydrogen_sort {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {carbon : CanonicalRerootCursor}
    (carbonEligible : CanonicalCenterRerootCursor mol root carbon)
    (carbonLabel : mol.atomZAt carbon.node.atom = 6)
    (leading suffix : List CanonicalRerootCursor)
    (prefixHydrogens : ∀ node ∈ leading, PhysicalHydrogenCursor mol root center node)
    (suffixHydrogens : ∀ node ∈ suffix, PhysicalHydrogenCursor mol root center node)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage) :
    FrameRuntime.sort? (FrameRuntime.compareBranch? mol (generatedProfile mol root center)
      authoritative fuel stage) ((leading ++ carbon :: suffix).map FrameRuntime.Cursor.actual) =
        some ((carbon :: (leading ++ suffix)).map FrameRuntime.Cursor.actual) := by
  induction leading with
  | nil =>
      have sorted := actual_hydrogen_sort tree rootBound centerGenerated suffix suffixHydrogens
        authoritative fuel stage
      have inserted := actual_carbon_insert_hydrogens tree rootBound centerGenerated carbonEligible
        carbonLabel suffix suffixHydrogens authoritative fuel stage
      simpa only [List.nil_append, List.map_cons, FrameRuntime.sort?, sorted, Bind.bind, Option.bind] using inserted
  | cons hydrogen leading ih =>
      have tailHydrogens : ∀ node ∈ leading, PhysicalHydrogenCursor mol root center node :=
        fun node member => prefixHydrogens node (List.mem_cons_of_mem hydrogen member)
      have sorted := ih tailHydrogens
      have allHydrogens : ∀ node ∈ leading ++ suffix, PhysicalHydrogenCursor mol root center node := by
        intro node member
        rcases List.mem_append.mp member with left | right
        · exact tailHydrogens node left
        · exact suffixHydrogens node right
      have inserted := actual_hydrogen_insert_after_carbon tree rootBound centerGenerated carbonEligible
        carbonLabel (prefixHydrogens hydrogen List.mem_cons_self) (leading ++ suffix) allHydrogens
        authoritative fuel stage
      simpa only [List.cons_append, List.map_cons, FrameRuntime.sort?, sorted, Bind.bind, Option.bind] using inserted

/-- Actual ranked? completes on a physically classified hydrogen child sphere.
The only width condition is the actual local child count fitting the imported slots. -/
theorem actual_hydrogen_ranked {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center) {cursor : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor mol root cursor)
    (hydrogens : ∀ child ∈ cursor.children mol, PhysicalHydrogenCursor mol root center child)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage)
    (width : (cursor.children mol).length ≤
      (if authoritative then RawMolecule.authoritativeChildSlots else 3)) :
    FrameRuntime.ranked? mol (generatedProfile mol root center) authoritative
      (FrameRuntime.compareBranch? mol (generatedProfile mol root center) authoritative fuel stage)
      (.actual cursor) =
        some (((cursor.children mol).map FrameRuntime.Cursor.actual) ++
          List.replicate ((if authoritative then RawMolecule.authoritativeChildSlots else 3) -
            (cursor.children mol).length) (.padding (.actual cursor))) := by
  have observed := genuine_cursor_observed tree rootBound centerGenerated eligible
  have childrenObserved := genuine_children_observed tree rootBound centerGenerated eligible
  have sorted := actual_hydrogen_sort tree rootBound centerGenerated (cursor.children mol)
    hydrogens authoritative fuel stage
  have fits := Nat.not_lt.mpr width
  simp [FrameRuntime.ranked?, FrameRuntime.Cursor.original, observed, childrenObserved,
    sorted, List.length_map, fits]

/-- Successful hydrogen ranking has exactly the actual mode's padded width, not a guessed six. -/
theorem actual_hydrogen_ranked_width {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center) {cursor : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor mol root cursor)
    (hydrogens : ∀ child ∈ cursor.children mol, PhysicalHydrogenCursor mol root center child)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage)
    (width : (cursor.children mol).length ≤
      (if authoritative then RawMolecule.authoritativeChildSlots else 3)) :
    (FrameRuntime.ranked? mol (generatedProfile mol root center) authoritative
      (FrameRuntime.compareBranch? mol (generatedProfile mol root center) authoritative fuel stage)
      (.actual cursor)).map List.length =
        some (if authoritative then RawMolecule.authoritativeChildSlots else 3) := by
  rw [actual_hydrogen_ranked tree rootBound centerGenerated eligible hydrogens
    authoritative fuel stage width]
  simp only [Option.map_some, List.length_append, List.length_map, List.length_replicate]
  congr 1
  omega

/-- Two actual hydrogen rankings zip to the same exact local mode width.
This is a completed actual paired-list computation, independent of total family size. -/
theorem actual_hydrogen_ranked_zip_width {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center) {left right : CanonicalRerootCursor}
    (leftEligible : CanonicalCenterRerootCursor mol root left)
    (rightEligible : CanonicalCenterRerootCursor mol root right)
    (leftHydrogens : ∀ child ∈ left.children mol, PhysicalHydrogenCursor mol root center child)
    (rightHydrogens : ∀ child ∈ right.children mol, PhysicalHydrogenCursor mol root center child)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage)
    (leftWidth : (left.children mol).length ≤
      (if authoritative then RawMolecule.authoritativeChildSlots else 3))
    (rightWidth : (right.children mol).length ≤
      (if authoritative then RawMolecule.authoritativeChildSlots else 3)) :
    (do
      let leftRanked ← FrameRuntime.ranked? mol (generatedProfile mol root center) authoritative
        (FrameRuntime.compareBranch? mol (generatedProfile mol root center) authoritative fuel stage)
        (.actual left)
      let rightRanked ← FrameRuntime.ranked? mol (generatedProfile mol root center) authoritative
        (FrameRuntime.compareBranch? mol (generatedProfile mol root center) authoritative fuel stage)
        (.actual right)
      pure (leftRanked.zip rightRanked).length : Option Nat) =
        some (if authoritative then RawMolecule.authoritativeChildSlots else 3) := by
  rw [actual_hydrogen_ranked tree rootBound centerGenerated leftEligible leftHydrogens
    authoritative fuel stage leftWidth,
    actual_hydrogen_ranked tree rootBound centerGenerated rightEligible rightHydrogens
      authoritative fuel stage rightWidth]
  simp only [Bind.bind, Option.bind, List.length_zip, List.length_append,
    List.length_map, List.length_replicate]
  have leftCount : (left.children mol).length +
      ((if authoritative then RawMolecule.authoritativeChildSlots else 3) -
        (left.children mol).length) = (if authoritative then RawMolecule.authoritativeChildSlots else 3) := by omega
  have rightCount : (right.children mol).length +
      ((if authoritative then RawMolecule.authoritativeChildSlots else 3) -
        (right.children mol).length) = (if authoritative then RawMolecule.authoritativeChildSlots else 3) := by omega
  simp only [leftCount, rightCount, min_self, Option.pure_def]

/-- A genuine cut has distinct actual children, derived from the independent raw bond inventory. -/
theorem genuine_children_nodup {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {cursor : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor mol root cursor) :
    (cursor.children mol).Nodup := by
  have cut := NativeGeneratedCursorPhysicalCut.genuine_cursor_cut_atoms_perm tree rootBound eligible
  have atoms := cut.nodup_iff.mpr
    ((NativeGeneratedCursorPhysicalCut.rawIncident_nodup tree cursor.node.atom).erase
      ((cursor.previous?.map CanonicalBranchNode.atom).getD root))
  exact List.Nodup.of_map (fun child : CanonicalRerootCursor => child.node.atom) atoms

/-- A list member determines a leading/suffix decomposition; no supplied sorting decomposition is needed. -/
theorem member_decomposition {α : Type} {value : α} {values : List α} (member : value ∈ values) :
    ∃ leading suffix, values = leading ++ value :: suffix := by
  induction values with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with same | inside
      · subst head
        exact ⟨[], tail, rfl⟩
      · obtain ⟨leading, suffix, decomposition⟩ := ih inside
        exact ⟨head :: leading, suffix, by simp only [List.cons_append, decomposition]⟩

/-- The actual carbon child is moved to the front by actual ranked?, with every other child
physically hydrogen. Its decomposition and unique occurrence are internally derived from actual
membership and the raw tree. No sorted keys, comparator success or output equality is a premise. -/
theorem actual_one_carbon_ranked {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center) {cursor carbon : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor mol root cursor)
    (carbonMember : carbon ∈ cursor.children mol)
    (carbonLabel : mol.atomZAt carbon.node.atom = 6)
    (otherHydrogens : ∀ child ∈ cursor.children mol, child ≠ carbon →
      PhysicalHydrogenCursor mol root center child)
    (authoritative : Bool) (fuel : Nat) (stage : CanonicalRuleStage)
    (width : (cursor.children mol).length ≤
      (if authoritative then RawMolecule.authoritativeChildSlots else 3)) :
    ∃ leading suffix,
      cursor.children mol = leading ++ carbon :: suffix ∧
      FrameRuntime.ranked? mol (generatedProfile mol root center) authoritative
        (FrameRuntime.compareBranch? mol (generatedProfile mol root center) authoritative fuel stage)
        (.actual cursor) =
          some (((carbon :: (leading ++ suffix)).map FrameRuntime.Cursor.actual) ++
            List.replicate ((if authoritative then RawMolecule.authoritativeChildSlots else 3) -
              (cursor.children mol).length) (.padding (.actual cursor))) := by
  obtain ⟨leading, suffix, decomposition⟩ := member_decomposition carbonMember
  have distinct := genuine_children_nodup tree rootBound eligible
  rw [decomposition] at distinct
  have carbonAbsent : carbon ∉ leading ++ suffix :=
    (List.nodup_cons.mp (List.nodup_middle.mp distinct)).1
  have prefixHydrogens : ∀ child ∈ leading, PhysicalHydrogenCursor mol root center child := by
    intro child member
    have original : child ∈ cursor.children mol := by rw [decomposition]; exact List.mem_append_left _ member
    apply otherHydrogens child original
    intro same
    subst child
    exact carbonAbsent (List.mem_append_left _ member)
  have suffixHydrogens : ∀ child ∈ suffix, PhysicalHydrogenCursor mol root center child := by
    intro child member
    have original : child ∈ cursor.children mol := by
      rw [decomposition]
      exact List.mem_append_right _ (List.mem_cons_of_mem carbon member)
    apply otherHydrogens child original
    intro same
    subst child
    exact carbonAbsent (List.mem_append_right _ member)
  have sorted := actual_one_carbon_hydrogen_sort tree rootBound centerGenerated
    (eligible.child carbonMember) carbonLabel leading suffix prefixHydrogens suffixHydrogens
    authoritative fuel stage
  have sortedOriginal :
      FrameRuntime.sort? (FrameRuntime.compareBranch? mol (generatedProfile mol root center)
        authoritative fuel stage) ((cursor.children mol).map FrameRuntime.Cursor.actual) =
        some ((carbon :: (leading ++ suffix)).map FrameRuntime.Cursor.actual) := by
    simpa only [decomposition] using sorted
  have observed := genuine_cursor_observed tree rootBound centerGenerated eligible
  have childrenObserved := genuine_children_observed tree rootBound centerGenerated eligible
  have sortedLength : (carbon :: (leading ++ suffix)).length = (cursor.children mol).length := by
    rw [decomposition]
    simp only [List.length_cons, List.length_append]
    omega
  have normalizedLength : leading.length + suffix.length + 1 = (cursor.children mol).length := by
    simp only [List.length_cons, List.length_append] at sortedLength
    omega
  have fits := Nat.not_lt.mpr width
  refine ⟨leading, suffix, decomposition, ?_⟩
  simp [FrameRuntime.ranked?, FrameRuntime.Cursor.original, observed, childrenObserved,
    sortedOriginal, List.length_map, normalizedLength, fits]

/-- The actual first C/H child pair decides Rule1a without inspecting any later padded pair. -/
theorem actual_carbon_hydrogen_first_pair {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {carbon hydrogen : CanonicalRerootCursor}
    (carbonEligible : CanonicalCenterRerootCursor mol root carbon)
    (carbonLabel : mol.atomZAt carbon.node.atom = 6)
    (hydrogenPhysical : PhysicalHydrogenCursor mol root center hydrogen)
    (authoritative : Bool) (pairs : List (FrameRuntime.Cursor × FrameRuntime.Cursor)) :
    FrameRuntime.pairLabels? mol (generatedProfile mol root center) authoritative .rule1a
      ((.actual carbon, .actual hydrogen) :: pairs) = some .gt := by
  have hydrogenFacts := physical_hydrogen_cursor_facts hydrogenPhysical
  have label := actual_rule1a_labels tree rootBound centerGenerated carbonEligible
    hydrogenFacts.1 authoritative
  have strict : FrameRuntime.label? mol (generatedProfile mol root center) authoritative .rule1a
      (.actual carbon) (.actual hydrogen) = some .gt := by
    simpa only [carbonLabel, hydrogenFacts.2] using label
  simp [FrameRuntime.pairLabels?, strict]

/-- A genuine three-child cursor is nonterminal in the actual runtime. -/
theorem actual_three_child_nonterminal {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {cursor : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor mol root cursor)
    (three : (cursor.children mol).length = 3) :
    FrameRuntime.terminal mol (.actual cursor) = false := by
  have generated : CanonicalCenterTreeNode mol root cursor.node := by
    cases eligible with
    | descending parentGenerated member => exact CanonicalCenterTreeNode.child parentGenerated member
    | ascending nodeGenerated _member => exact nodeGenerated
  have real := chronological_generated_all_real tree rootBound generated
  cases children : cursor.children mol with
  | nil => simp only [children, List.length_nil] at three; omega
  | cons head tail =>
      simp [FrameRuntime.terminal, FrameRuntime.Cursor.original, cursorTerminal,
        CanonicalBranchNode.forcedLeaf, real, children]

/-- Complete actual one-refinement comparison of a three-child C/H/H sphere against a
three-child H/H/H sphere. Both ligand roots are actual carbon. The sphere facts are
independent genuine traversal/physical arm/atom data; no key, sorting, comparator or
outcome equality is supplied. One refinement suffices regardless of total molecule size. -/
theorem actual_three_child_sphere_decision {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
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
      (.actual bridge) (.actual methyl) = some .gt := by
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
  have parentLabel := actual_rule1a_labels tree rootBound centerGenerated bridgeEligible methylEligible authoritative
  have parentTie : FrameRuntime.label? mol (generatedProfile mol root center) authoritative .rule1a
      (.actual bridge) (.actual methyl) = some .eq := by
    simpa only [bridgeLabel, methylLabel] using parentLabel
  cases methylChildren : methyl.children mol with
  | nil => simp only [methylChildren, List.length_nil] at methylThree; omega
  | cons hydrogen hydrogens =>
      have headPhysical := methylHydrogens hydrogen (by simp only [methylChildren, List.mem_cons_self])
      let paddingCount := (if authoritative then RawMolecule.authoritativeChildSlots else 3) - 3
      let tailPairs : List (FrameRuntime.Cursor × FrameRuntime.Cursor) :=
        (((leading ++ suffix).map FrameRuntime.Cursor.actual ++
          List.replicate paddingCount (FrameRuntime.Cursor.padding (FrameRuntime.Cursor.actual bridge))).zip
        (hydrogens.map FrameRuntime.Cursor.actual ++
          List.replicate paddingCount (FrameRuntime.Cursor.padding (FrameRuntime.Cursor.actual methyl))))
      have methylLength : hydrogens.length + 1 = 3 := by
        simp only [methylChildren, List.length_cons] at methylThree
        omega
      have expanded : FrameRuntime.nextPairs? mol (generatedProfile mol root center) authoritative
          (FrameRuntime.compareBranch? mol (generatedProfile mol root center) authoritative fuel stage)
          [(.actual bridge, .actual methyl)] = some ((.actual carbon, .actual hydrogen) :: tailPairs) := by
        simp [FrameRuntime.nextPairs?, bridgeTerminal, methylTerminal, bridgeRanked, methylRanked,
          methylChildren, bridgeThree, methylLength, tailPairs, paddingCount, List.zip_cons_cons]
      have pairStrict := actual_carbon_hydrogen_first_pair tree rootBound centerGenerated
        (bridgeEligible.child carbonMember) carbonLabel headPhysical authoritative tailPairs
      have leftTailCount : leading.length + suffix.length = 2 := by
        rw [decomposition] at bridgeThree
        simp only [List.length_append, List.length_cons] at bridgeThree
        omega
      have rightTailCount : hydrogens.length = 2 := by
        simp only [methylChildren, List.length_cons] at methylThree
        omega
      have count : ((.actual carbon, .actual hydrogen) :: tailPairs).length ≤ 5 := by
        simp only [List.length_cons, tailPairs, List.length_zip, List.length_append,
          List.length_map, List.length_replicate]
        rw [leftTailCount, rightTailCount]
        cases authoritative <;> simp [paddingCount, RawMolecule.authoritativeChildSlots]
      have within : ¬ defaultBranchWidthCap < ((.actual carbon, .actual hydrogen) :: tailPairs).length := by
        unfold defaultBranchWidthCap
        omega
      have tailWidth : tailPairs.length < defaultBranchWidthCap := by
        simp only [List.length_cons] at within
        omega
      have firstRule : FrameRuntime.compareRule? mol (generatedProfile mol root center) authoritative
          (FrameRuntime.compareBranch? mol (generatedProfile mol root center) authoritative fuel stage)
          .rule1a (fuel + 1) [(.actual bridge, .actual methyl)] = some .gt := by
        rw [FrameRuntime.compareRule?]
        simp [FrameRuntime.pairLabels?, parentTie, expanded, defaultBranchWidthCap]
        rw [FrameRuntime.compareRule?]
        simp [pairStrict, tailWidth]
      rw [FrameRuntime.compareBranch?]
      simp [firstRule]

end TetraStereo.UniversalProof.NativeFramedCursorObservations
