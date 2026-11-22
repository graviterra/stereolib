import TetraStereo.Engine.RingClosedGroupTie

set_option autoImplicit false
namespace TetraStereo.Engine.RingClosedGroupRecognition
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingNestedActivePair (Reader Frame)
open RingClosedPairGroup (Group children)
open RingActivePairReport (Matrix Slot)

/-- A supplied molecular group forces the actual sibling search to find a
group. The three roles can enter the original adjacency list in any order. -/
theorem group_complete {i q read} (g : Group i q read) :
    (RingClosedPairGroup.group? i q read).isSome = true := by
  obtain ⟨a,b,c,eqn⟩ := List.length_eq_three.mp g.allChildren.length_eq
  have perm : [g.pos,g.neg,g.leaf].Perm [a,b,c] := eqn ▸ g.allChildren.symm
  simp only [RingClosedPairGroup.group?,eqn]
  apply List.findSome?_isSome_iff.mpr
  refine ⟨[g.pos,g.neg,g.leaf],List.mem_permutations'.mpr perm,?_⟩
  dsimp only
  conv_lhs => arg 1; whnf
  have att := Option.attach_eq_some _ ⟨g.earlier,g.earlierRead⟩
  simp [g.rootRead,RingClosedPairGroup.lower,g.posRead,g.negRead,g.allChildren,g.live,g.real,g.leafSilent,
    g.closed,g.noLaterPos,g.noLaterNeg,g.numbers.1,g.numbers.2.1,g.numbers.2.2.1,g.numbers.2.2.2,att,g.oneClass]
  split; rfl

theorem group_iff {i q read} : (RingClosedPairGroup.group? i q read).isSome = true ↔ Nonempty (Group i q read) :=
  ⟨fun h => ⟨(RingClosedPairGroup.group? i q read).get h⟩,fun ⟨g⟩ => group_complete g⟩

private theorem same_root_hand {i q read} (x y : Group i q read) : x.p = y.p := by
  have eqn := x.rootRead.symm.trans y.rootRead
  cases hx : x.p <;> cases hy : y.p <;> first | rfl | simp [hx,hy,RingClosedPairGroup.lower] at eqn

/-- Every declaratively certified equal-root input produces an actual
edge certificate, irrespective of which successful sibling witnesses are
found first. -/
theorem tied_complete {i f a b read} (c : RingClosedGroupTie.Certificate i f a b read) :
    (RingClosedGroupTie.edge? i f a b read).isSome = true := by
  obtain ⟨l,hl⟩ := Option.isSome_iff_exists.mp (group_complete c.left)
  obtain ⟨r,hr⟩ := Option.isSome_iff_exists.mp (group_complete c.right)
  have same := (same_root_hand l c.left).trans (c.same.trans (same_root_hand c.right r))
  have ht := Option.attach_eq_some _ ⟨c.trace,c.earlier⟩
  simp [RingClosedGroupTie.edge?,ht,c.tie,hl,hr,same]

theorem tied_iff {i f a b read} : (RingClosedGroupTie.edge? i f a b read).isSome = true ↔
    Nonempty (RingClosedGroupTie.Certificate i f a b read) :=
  ⟨fun h => ⟨(RingClosedGroupTie.edge? i f a b read).get h⟩,fun ⟨c⟩ => tied_complete c⟩

theorem tied_score {i f a b read} (c : RingClosedGroupTie.Certificate i f a b read) :
    RingClosedGroupTie.score? i f a b read = some (0,0) := by
  obtain ⟨found,h⟩ := Option.isSome_iff_exists.mp (tied_complete c)
  simp [RingClosedGroupTie.score?,c.candidate,h]

theorem strict_excluded {i f a b read} (c : RingClosedGroupTie.Certificate i f a b read) :
    ¬ Nonempty (RingClosedPairGroup.Certificate i f a b read) := by
  rintro ⟨s⟩
  exact s.strict ((same_root_hand s.left c.left).trans (c.same.trans (same_root_hand c.right s.right)))

/-- The complementary strict 4c family has the same existential completeness
guarantee. Its two recognized roots have the same actual publications as the
supplied molecular witnesses. -/
theorem strict_complete {i f a b read} (c : RingClosedPairGroup.Certificate i f a b read) :
    (RingClosedPairGroup.edge? i f a b read).isSome = true := by
  obtain ⟨l,hl⟩ := Option.isSome_iff_exists.mp (group_complete c.left)
  obtain ⟨r,hr⟩ := Option.isSome_iff_exists.mp (group_complete c.right)
  have ne : l.p ≠ r.p := fun h =>
    c.strict ((same_root_hand c.left l).trans (h.trans (same_root_hand r c.right)))
  have ht := Option.attach_eq_some _ ⟨c.prior,c.comparison⟩
  simp [RingClosedPairGroup.edge?,ht,c.tied,hl,hr,ne]

theorem strict_iff {i f a b read} : (RingClosedPairGroup.edge? i f a b read).isSome = true ↔
    Nonempty (RingClosedPairGroup.Certificate i f a b read) :=
  ⟨fun h => ⟨(RingClosedPairGroup.edge? i f a b read).get h⟩,fun ⟨c⟩ => strict_complete c⟩

/-- The frame collector recovers the actual occurrence's exact atom IDs
from their provenance. The order in their returned list is fixed. -/
theorem frame_complete {i f} (fr : Frame i f) : RingNestedActivePair.frame? i f = some fr := by
  rcases fr with ⟨c,recognized,four,ids,actual,physical⟩
  have hc := Option.attach_eq_some _ ⟨c,recognized⟩
  have hi := Option.attach_eq_some _ ⟨ids,actual⟩
  simp [RingNestedActivePair.frame?,hc,four,hi,physical]

/-- A complete four-slot molecular matrix and its ordinary one-pair
partition force the executable refusal. Only off-diagonal entries participate
in the molecular ordering, so arbitrary diagonal conventions do not matter. -/
theorem refusal_complete {i f read} (r : RingClosedGroupTie.Refusal i f read) :
    (RingClosedGroupTie.refusal? i f read).isSome = true := by
  have full := (RingActivePairReport.matrix?_complete (RingClosedGroupTie.source r.frame read)).mpr
    (fun a b ne => by rw [r.matrix.found a b ne]; rfl)
  obtain ⟨m,hm⟩ := Option.isSome_iff_exists.mp full
  have scores (rev : Bool) (a b : Slot) : RingOrdinaryPairRefusal.score r.matrix rev a b =
      RingOrdinaryPairRefusal.score m rev a b := by
    by_cases same : a = b
    · simp [RingOrdinaryPairRefusal.score,same]
    · have eqn := Option.some.inj ((r.matrix.found a b same).symm.trans (m.found a b same))
      simp [RingOrdinaryPairRefusal.score,same,eqn]
  have eqScores : RingOrdinaryPairRefusal.score r.matrix = RingOrdinaryPairRefusal.score m :=
    funext fun rev => funext fun a => funext fun b => scores rev a b
  have tables (rev : Bool) : RingOrdinaryPairRefusal.table r.matrix rev = RingOrdinaryPairRefusal.table m rev := by
    simp only [RingOrdinaryPairRefusal.table,eqScores]
  have val : RingOrdinaryPairRefusal.Valid m r.ordinary.a r.ordinary.b := by
    simpa only [RingOrdinaryPairRefusal.Valid,tables,eqScores] using r.ordinary.partition
  obtain ⟨cert,hit⟩ := Option.isSome_iff_exists.mp
    ((RingOrdinaryPairRefusal.find_iff m).mpr ⟨_,_,r.ordinary.ordered,val⟩)
  simp [RingClosedGroupTie.refusal?,frame_complete r.frame,hm,hit]

theorem refusal_iff {i f read} : (RingClosedGroupTie.refusal? i f read).isSome = true ↔
    Nonempty (RingClosedGroupTie.Refusal i f read) :=
  ⟨fun h => ⟨(RingClosedGroupTie.refusal? i f read).get h⟩,fun ⟨r⟩ => refusal_complete r⟩

theorem scheduled_absence_iff {i : Input} {root : i.certified.Atom} {f : Site i} (on : f.val.root = root) :
    RingClosedGroupTie.atRoot i root f = some none ↔
      RingClosedPairAssignment.publish? i f (RingClosedGroupTie.atRoot i root) = some none ∨
      (RingClosedPairAssignment.publish? i f (RingClosedGroupTie.atRoot i root) = none ∧
        Nonempty (RingClosedGroupTie.Refusal i f (RingNestedActivePair.masked f (RingClosedGroupTie.atRoot i root)))) := by
  rw [RingClosedGroupTie.atRoot_absence_iff on,refusal_iff]

end TetraStereo.Engine.RingClosedGroupRecognition
assert_kernel_only TetraStereo.Engine.RingClosedGroupRecognition.group_iff
assert_kernel_only TetraStereo.Engine.RingClosedGroupRecognition.tied_iff
assert_kernel_only TetraStereo.Engine.RingClosedGroupRecognition.strict_iff
assert_kernel_only TetraStereo.Engine.RingClosedGroupRecognition.frame_complete
assert_kernel_only TetraStereo.Engine.RingClosedGroupRecognition.refusal_iff
assert_kernel_only TetraStereo.Engine.RingClosedGroupRecognition.scheduled_absence_iff
assert_kernel_only TetraStereo.Engine.RingClosedGroupRecognition.tied_score
assert_kernel_only TetraStereo.Engine.RingClosedGroupRecognition.strict_excluded
