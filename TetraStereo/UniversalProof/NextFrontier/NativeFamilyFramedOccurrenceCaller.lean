import TetraStereo.UniversalProof.NextFrontier.NativeFamilyPhysicalHydrogenArms
import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalGenerationCoverage
import TetraStereo.UniversalProof.NextFrontier.FamilyCompleteOccurrenceCaller

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeFamilyFramedOccurrenceCaller
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



theorem maintained_fast_eq_complete (mol : RawMolecule) (fuel : Nat)
    (state : OccurrenceAuxState) (node : CanonicalBranchNode)
    (profile : FrameRuntime.Profile) (available : FrameRuntime.profile? mol node = some profile) :
    occurrenceFact? mol fuel state node =
      FramedCompleteRuntime.occurrenceFactComplete? mol false fuel state node := by
  rw [occurrenceFact?_eq_framed_of_profile_some mol fuel state node profile available,
    framedOccurrenceFact?_eq_complete]

/-- Authoritative correspondence for the available-profile dispatch branch. -/
theorem maintained_authoritative_eq_complete (mol : RawMolecule) (fuel : Nat)
    (state : OccurrenceAuxState) (node : CanonicalBranchNode)
    (profile : FrameRuntime.Profile) (available : FrameRuntime.profile? mol node = some profile) :
    occurrenceFactAuthoritative? mol fuel state node =
      FramedCompleteRuntime.occurrenceFactComplete? mol true fuel state node := by
  rw [occurrenceFactAuthoritative?_eq_framed_of_profile_some mol fuel state node profile available,
    framedOccurrenceFactAuthoritative?_eq_complete]

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
  apply TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.actual_hydrogen_carbon_first_pair <;> assumption

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
  apply TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.actual_three_child_sphere_reverse_decision <;> assumption

/-- Strict actual atomic comparisons retain ordinary protocol flags for every auxiliary state. -/
theorem actual_atomic_decision {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center)
    {left right : CanonicalRerootCursor}
    (leftEligible : CanonicalCenterRerootCursor mol root left)
    (rightEligible : CanonicalCenterRerootCursor mol root right)
    (different : mol.atomZAt left.node.atom ≠ mol.atomZAt right.node.atom)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat) :
    FrameRuntime.decision? mol (generatedProfile mol root center) authoritative state fuel left right =
      some { ordering := compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) } := by
  apply TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.complete_atomic_decision <;> assumption

/-- A pure four-role indexing device for the helper below; it is not an input domain or
substitute molecular constructor, and its strict decision matrix must be derived by final callers. -/
abbrev WrittenLigandRole := TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.WrittenLigandRole
namespace WrittenLigandRole
abbrev bridge := TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.WrittenLigandRole.bridge
abbrev hydrogen := TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.WrittenLigandRole.hydrogen
abbrev fluorine := TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.WrittenLigandRole.fluorine
abbrev methyl := TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.WrittenLigandRole.methyl
end WrittenLigandRole

abbrev rolePriority := TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.rolePriority

abbrev writtenRoles := TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.writtenRoles

abbrev priorityRoles := TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.priorityRoles

/-- Closed numeral reductions of the generic `compare` (the `Nat` `Ord` instance).  There is no
`Nat.compare` constant in this Lean; the finite role-priority matrix `{0,1,2,3}` is reduced by
kernel `decide` so the 24-role permutations below are closed by `simp`. -/
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

/-- HELPER ONLY: actual tracked sorting is invariant over every permutation of four distinct
roles once actual admission and the strict decision matrix have been established. These are
explicit conditional algebra premises, not the headline family domain. Final family theorems
must derive them from raw labels, genuine traversal and both decisive carbon orientations. -/
theorem helper_trackedSort_four_permutation (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat)
    (cursor : WrittenLigandRole → CanonicalRerootCursor) (distance : WrittenLigandRole → Nat)
    (observed : ∀ role, FrameRuntime.cursor? mol profile (.actual (cursor role)) = some (distance role))
    (decisions : ∀ left right, left ≠ right →
      FrameRuntime.decision? mol profile authoritative state fuel (cursor left) (cursor right) =
        some { ordering := compare (rolePriority left) (rolePriority right) })
    (roles : List WrittenLigandRole) (permutation : roles.Perm writtenRoles) :
    FrameRuntime.trackedSort? mol profile authoritative state fuel (roles.map cursor) =
      some (priorityRoles.map cursor, 0) := by
  apply TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.helper_trackedSortComplete_four_permutation <;> assumption

/-- HELPER ONLY: adjacent strict decisions are exactly the three ordinary priority boundaries.
The final family use must derive this matrix internally rather than supply it as an outcome field. -/
theorem helper_adjacent_priority_roles (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat)
    (cursor : WrittenLigandRole → CanonicalRerootCursor)
    (decisions : ∀ left right, left ≠ right →
      FrameRuntime.decision? mol profile authoritative state fuel (cursor left) (cursor right) =
        some { ordering := compare (rolePriority left) (rolePriority right) }) :
    FrameRuntime.adjacent? mol profile authoritative state fuel (priorityRoles.map cursor) =
      some [⟨cursor .fluorine, cursor .bridge, { ordering := .gt }⟩,
        ⟨cursor .bridge, cursor .methyl, { ordering := .gt }⟩,
        ⟨cursor .methyl, cursor .hydrogen, { ordering := .gt }⟩] := by
  apply TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.helper_adjacentComplete_priority_roles; assumption

/-- Every actual uncut occurrence child is a genuine oriented original-tree edge,
including the ascending child emitted first when the discovery parent is present. -/
theorem actual_occurrence_child_eligible {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat}
    (rootBound : root < mol.atomCount) {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root center) {child : CanonicalRerootCursor}
    (member : child ∈ occurrenceLigandCursors mol center) :
    CanonicalCenterRerootCursor mol root child := by
  apply TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.actual_occurrence_child_eligible <;> assumption

/-- Atom equality identifies actual genuine cursors with the same remembered previous node.
Original histories are retained; this does not construct fresh histories from atom IDs. -/
theorem genuine_same_previous_cursor_unique {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat}
    (rootBound : root < mol.atomCount) {left right : CanonicalRerootCursor}
    (leftEligible : CanonicalCenterRerootCursor mol root left)
    (rightEligible : CanonicalCenterRerootCursor mol root right)
    (previous : left.previous? = right.previous?)
    (atom : left.node.atom = right.node.atom) : left = right := by
  apply TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.genuine_same_previous_cursor_unique <;> assumption

/-- HELPER ONLY: an atom-inventory permutation lifts to a cursor permutation when every
member is an actual genuine edge with the same previous node. Final callers must derive
both inventories and this generation condition from the physical raw graph. -/
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
  apply TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.helper_genuine_inventory_perm <;> assumption

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
  apply TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.family_actual_reverse_decisive_child_spheres <;> assumption

/-- The actual occurrence inventory is a permutation of the physical written ligand IDs.
It does not assert written enumeration order: original-parent-first generation may rotate it. -/
theorem family_actual_occurrence_atoms (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (centerAtom : center.atom = 1 + 12 * i.val + 5) :
    ((occurrenceLigandCursors (familyRaw ps) center).map (fun cursor => cursor.node.atom)).Perm
      [1 + 12 * i.val + 2, 1 + 12 * i.val + 6,
       1 + 12 * i.val + 7, 1 + 12 * i.val + 8] := by
  apply TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.family_actual_occurrence_atoms <;> assumption

/-- The family tag has exactly four physical occurrence cursors, at every bounded discovery root. -/
theorem family_actual_occurrence_length (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (centerAtom : center.atom = 1 + 12 * i.val + 5) :
    (occurrenceLigandCursors (familyRaw ps) center).length = 4 := by
  apply TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.family_actual_occurrence_length <;> assumption

/-- The actual written row has four entries, so the lone-pair path cannot change it. -/
theorem family_actual_written_ligands (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyRaw ps).ligandsWithLonePair (1 + 12 * i.val + 5) =
      [1 + 12 * i.val + 2, 1 + 12 * i.val + 6,
       1 + 12 * i.val + 7, 1 + 12 * i.val + 8] := by
  apply TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.family_actual_written_ligands

/-- The literal frame constructor succeeds with its actual parent-first physical inventory.
No desired frame/order/profile output is supplied as a premise. -/
theorem family_actual_occurrence_frame (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (centerAtom : center.atom = 1 + 12 * i.val + 5) :
    occurrenceLigandFrame? (familyRaw ps) center =
      some (occurrenceLigandCursors (familyRaw ps) center) := by
  apply TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.family_actual_occurrence_frame <;> assumption

abbrev roleOffset := TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.roleOffset

/-- Every actual family frame admits a four-role description, internally chosen from
physical inventory membership. The description retains original full cursors and is a
permutation, not an asserted written enumeration order. -/
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
  apply TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.family_actual_frame_roles <;> assumption

/-- HELPER ONLY: a actual cursor-inventory permutation can be represented by a role
permutation without assuming a canonical enumeration or injecting rediscovery histories. -/
theorem helper_frame_role_representation (cursor : WrittenLigandRole → CanonicalRerootCursor)
    (physical : List CanonicalRerootCursor) (inventory : physical.Perm (writtenRoles.map cursor)) :
    ∃ roles : List WrittenLigandRole, physical = roles.map cursor ∧ roles.Perm writtenRoles := by
  apply TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.helper_frame_role_representation; assumption

abbrev roleAtomicNumber := TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.roleAtomicNumber

/-- Raw maintained role metadata supplies the real atomic labels; no comparison is an input. -/
theorem family_role_atomic_labels (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (cursor : WrittenLigandRole → CanonicalRerootCursor)
    (atoms : ∀ role, (cursor role).node.atom = 1 + 12 * i.val + roleOffset role) :
    ∀ role, (familyRaw ps).atomZAt (cursor role).node.atom = roleAtomicNumber role := by
  apply TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.family_role_atomic_labels <;> assumption

/-- The complete strict four-role decision matrix is derived internally from independent
raw labels and the two actual second-sphere execution directions, for either mode and any state. -/
theorem family_actual_role_decisions (ps : List TetrahedralInputParity) (i : Fin ps.length)
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
      FrameRuntime.decision? (familyRaw ps) (generatedProfile (familyRaw ps) root center)
        authoritative state (fuel + 1) (cursor left) (cursor right) =
        some { ordering := compare (rolePriority left) (rolePriority right) } := by
  exact TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.family_complete_role_decisions
    ps i rootBound generated centerAtom cursor eligible previous atoms authoritative state fuel

/-- Actual tracked sorting and adjacent comparisons for every maintained family tag,
independent of its original-parent-first enumeration. The local four-entry bound and
complete strict decision matrix are internally derived, for both modes and every auxiliary state. -/
theorem family_actual_sort_and_adjacent (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (centerAtom : center.atom = 1 + 12 * i.val + 5)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat) :
    ∃ cursor : WrittenLigandRole → CanonicalRerootCursor,
      (∀ role, (cursor role).node.atom = 1 + 12 * i.val + roleOffset role) ∧
      FrameRuntime.trackedSort? (familyRaw ps) (generatedProfile (familyRaw ps) root center)
        authoritative state (fuel + 1) (occurrenceLigandCursors (familyRaw ps) center) =
        some (priorityRoles.map cursor, 0) ∧
      FrameRuntime.adjacent? (familyRaw ps) (generatedProfile (familyRaw ps) root center)
        authoritative state (fuel + 1) (priorityRoles.map cursor) =
        some [⟨cursor .fluorine, cursor .bridge, { ordering := .gt }⟩,
          ⟨cursor .bridge, cursor .methyl, { ordering := .gt }⟩,
          ⟨cursor .methyl, cursor .hydrogen, { ordering := .gt }⟩] := by
  apply TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.family_complete_sort_and_adjacent <;> assumption

/-- Literal written-ID searches produce the source parity positions; this search belongs
to the final caller, not to occurrenceLigandCursors enumeration. -/
theorem family_actual_priority_positions (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (cursor : WrittenLigandRole → CanonicalRerootCursor)
    (atoms : ∀ role, (cursor role).node.atom = 1 + 12 * i.val + roleOffset role) :
    (priorityRoles.map cursor).mapM (fun child =>
      (((familyRaw ps).ligandsWithLonePair (1 + 12 * i.val + 5)).zipIdx.find?
        (fun entry => entry.1 == child.node.atom)).map Prod.snd) = some [2, 0, 3, 1] := by
  exact TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.family_actual_priority_positions
    ps i cursor atoms

/-- The actual fast production occurrence caller consumes the independently derived
frame, sorting, adjacent decisions and written positions for every genuine family tag. -/
theorem family_actual_fast_occurrence_fact (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (centerAtom : center.atom = 1 + 12 * i.val + 5)
    (state : OccurrenceAuxState) (fuel : Nat) :
    occurrenceFact? (familyRaw ps) (fuel + 1) state center =
      some { key := canonicalOccurrenceKey center
             atom := center.atom
             descriptor := RawMolecule.descriptorOfParity (ps.get i) false
             uppercase := true
             priorityPositions := [2, 0, 3, 1] } := by
  rw [maintained_fast_eq_complete (familyRaw ps) (fuel + 1) state center _
    (actual_profile_obtained (familyRaw_chronologicalPhysicalTree ps) rootBound generated)]
  exact TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.family_complete_occurrence_fact ps i rootBound generated centerAtom false state fuel

/-- The actual authoritative production caller has the same precise source fact. Its
five-slot recursion is consumed through actual authoritative decisions, not a fast fallback. -/
theorem family_actual_authoritative_occurrence_fact (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (centerAtom : center.atom = 1 + 12 * i.val + 5)
    (state : OccurrenceAuxState) (fuel : Nat) :
    occurrenceFactAuthoritative? (familyRaw ps) (fuel + 1) state center =
      some { key := canonicalOccurrenceKey center
             atom := center.atom
             descriptor := RawMolecule.descriptorOfParity (ps.get i) false
             uppercase := true
             priorityPositions := [2, 0, 3, 1] } := by
  rw [maintained_authoritative_eq_complete (familyRaw ps) (fuel + 1) state center _
    (actual_profile_obtained (familyRaw_chronologicalPhysicalTree ps) rootBound generated)]
  exact TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.family_complete_occurrence_fact ps i rootBound generated centerAtom true state fuel

/-- Every actual maintained written tag is inhabited by a genuine node at any bounded
root, and both real production occurrence callers return the same precise written-parity fact.
For ps=[] there is no Fin ps.length tag; no phantom request is introduced. -/
theorem family_every_written_tag_actual_facts (ps : List TetrahedralInputParity) (i : Fin ps.length)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    (state : OccurrenceAuxState) (fuel : Nat) :
    ∃ center, CanonicalCenterTreeNode (familyRaw ps) root center ∧
      center.atom = 1 + 12 * i.val + 5 ∧
      occurrenceFact? (familyRaw ps) (fuel + 1) state center =
        some { key := canonicalOccurrenceKey center
               atom := center.atom
               descriptor := RawMolecule.descriptorOfParity (ps.get i) false
               uppercase := true
               priorityPositions := [2, 0, 3, 1] } ∧
      occurrenceFactAuthoritative? (familyRaw ps) (fuel + 1) state center =
        some { key := canonicalOccurrenceKey center
               atom := center.atom
               descriptor := RawMolecule.descriptorOfParity (ps.get i) false
               uppercase := true
               priorityPositions := [2, 0, 3, 1] } := by
  obtain ⟨center, generated, centerAtom, _, _⟩ :=
    TetraStereo.UniversalProof.FamilyCompleteOccurrenceCaller.family_every_written_tag_complete_facts
      ps i rootBound state fuel
  exact ⟨center, generated, centerAtom,
    family_actual_fast_occurrence_fact ps i rootBound generated centerAtom state fuel,
    family_actual_authoritative_occurrence_fact ps i rootBound generated centerAtom state fuel⟩
end TetraStereo.UniversalProof.NativeFamilyFramedOccurrenceCaller



























namespace TetraStereo.UniversalProof.NativeFamilyFramedOccurrenceCallerProofs.FramedFamilyAuxiliaryStateJoin

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeFamilyFramedOccurrenceCaller
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

/-- The primary (tagged) center atom of maintained family tag `i`.  This is the atom at which
the final tetrahedral occurrence descriptor is requested; every other tag is a deeper occurrence
committed into the auxiliary state first. -/
def familyTagPrimaryCenter (i : Nat) : Nat := 1 + 12 * i + 5

/-- The maintained `tagIndex` names exactly this primary center. -/
theorem familyTagPrimaryCenter_eq_tagIndex (i : Nat) : familyTagPrimaryCenter i = tagIndex i := by
  unfold familyTagPrimaryCenter tagIndex
  omega






theorem family_tag_authoritative_fact_state_independent (ps : List TetrahedralInputParity)
    (i : Fin ps.length) {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (centerAtom : center.atom = 1 + 12 * i.val + 5)
    (state₁ state₂ : OccurrenceAuxState) (fuel : Nat) :
    occurrenceFactAuthoritative? (familyRaw ps) (fuel + 1) state₁ center =
      occurrenceFactAuthoritative? (familyRaw ps) (fuel + 1) state₂ center := by
  rw [family_actual_authoritative_occurrence_fact ps i rootBound generated centerAtom state₁ fuel,
    family_actual_authoritative_occurrence_fact ps i rootBound generated centerAtom state₂ fuel]

/-- The fast production caller is likewise state-independent, by the same constant-fact theorem. -/
theorem family_tag_fast_fact_state_independent (ps : List TetrahedralInputParity)
    (i : Fin ps.length) {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (centerAtom : center.atom = 1 + 12 * i.val + 5)
    (state₁ state₂ : OccurrenceAuxState) (fuel : Nat) :
    occurrenceFact? (familyRaw ps) (fuel + 1) state₁ center =
      occurrenceFact? (familyRaw ps) (fuel + 1) state₂ center := by
  rw [family_actual_fast_occurrence_fact ps i rootBound generated centerAtom state₁ fuel,
    family_actual_fast_occurrence_fact ps i rootBound generated centerAtom state₂ fuel]

/-- Fast and fully-authoritative production callers agree on the same precise fact, so the
auxiliary-state join cannot diverge between the two paths. -/
theorem family_tag_fast_authoritative_agree (ps : List TetrahedralInputParity)
    (i : Fin ps.length) {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root center)
    (centerAtom : center.atom = 1 + 12 * i.val + 5)
    (state : OccurrenceAuxState) (fuel : Nat) :
    occurrenceFact? (familyRaw ps) (fuel + 1) state center =
      occurrenceFactAuthoritative? (familyRaw ps) (fuel + 1) state center := by
  rw [family_actual_fast_occurrence_fact ps i rootBound generated centerAtom state fuel,
    family_actual_authoritative_occurrence_fact ps i rootBound generated centerAtom state fuel]




theorem family_tag_authoritative_label_state_independent (ps : List TetrahedralInputParity)
    (i : Fin ps.length) {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    (state₁ state₂ : OccurrenceAuxState) (fuel : Nat) :
    ∃ center, center.atom = 1 + 12 * i.val + 5 ∧
      occurrenceFactAuthoritative? (familyRaw ps) (fuel + 1) state₁ center =
        occurrenceFactAuthoritative? (familyRaw ps) (fuel + 1) state₂ center := by
  obtain ⟨center, generated, centerAtom, _, auth₁⟩ :=
    family_every_written_tag_actual_facts ps i rootBound state₁ fuel
  have auth₂ := family_actual_authoritative_occurrence_fact ps i rootBound generated
    centerAtom state₂ fuel
  refine ⟨center, centerAtom, ?_⟩
  rw [auth₁, auth₂]

/-- The fast and authoritative labels agree, in the same existence form. -/
theorem family_tag_fast_authoritative_label_agree (ps : List TetrahedralInputParity)
    (i : Fin ps.length) {root : Nat} (rootBound : root < (familyRaw ps).atomCount)
    (state : OccurrenceAuxState) (fuel : Nat) :
    ∃ center, center.atom = 1 + 12 * i.val + 5 ∧
      occurrenceFact? (familyRaw ps) (fuel + 1) state center =
        occurrenceFactAuthoritative? (familyRaw ps) (fuel + 1) state center := by
  obtain ⟨center, generated, centerAtom, fast₁, auth₁⟩ :=
    family_every_written_tag_actual_facts ps i rootBound state fuel
  refine ⟨center, centerAtom, ?_⟩
  rw [fast₁, auth₁]

end TetraStereo.UniversalProof.NativeFamilyFramedOccurrenceCallerProofs.FramedFamilyAuxiliaryStateJoin
