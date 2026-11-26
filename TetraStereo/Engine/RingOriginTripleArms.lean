import TetraStereo.Engine.RingOriginTwinFrame
import TetraStereo.Engine.RingOriginMarkWords

/-! Two unmarked ordinary terminal twins remain tied under selected-atom
promotion, including when a third terminal twin is selected. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginTripleArms
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Frame Reader)
open RingHydrogenSpelling (TwinPair)
open RingGroupedCentre (cursor)
open private join extend unit lower mark from TetraStereo.Engine.RingOriginMarkWords

/-- Slot facts recovered from physical twin endpoints, without repeating key
or reader equality as assumptions. -/
theorem twin_slot_facts {i : Input} (p : TwinPair i) {f : Site i} (fr : Frame i f)
    (center : fr.center = p.c) (offU : f.val.root ≠ p.u) (offV : f.val.root ≠ p.v)
    (r : Reader i) (ready : RingGroupedStereo.Ready f r) (a b : Fin 4)
    (atU : (fr.arm a).occurrence.val.node.current? = some p.u)
    (atV : (fr.arm b).occurrence.val.node.current? = some p.v) :
    i.certified.executableLocalizedRerootChildren (cursor fr a) = [] ∧
    i.certified.executableLocalizedRerootChildren (cursor fr b) = [] ∧
    r (cursor fr a).occurrence = some none ∧ r (cursor fr b).occurrence = some none ∧
    RingSingleCycleComparison.rebuilt i f (cursor fr a) =
      RingSingleCycleComparison.rebuilt i f (cursor fr b) := by
  obtain ⟨ru,lu⟩ := RingOriginTwinFrame.terminal_slot fr p.u (center.symm ▸ p.supportU) offU a atU
  obtain ⟨rv,lv⟩ := RingOriginTwinFrame.terminal_slot fr p.v (center.symm ▸ p.supportV) offV b atV
  have reads (k : Fin 4) (empty : i.certified.executableLocalizedRerootChildren (cursor fr k) = []) :
      r (cursor fr k).occurrence = some none := by
    obtain ⟨v,seen,_,terminal⟩ := ready (cursor fr k) (fr.direction k).property.1
    exact seen.trans (congrArg some (terminal empty))
  exact ⟨lu,lv,reads a lu,reads b lv,
    RingOriginTwinLeaves.twin_rebuilt_eq p f _ _ lu lv atU atV ru rv⟩

/-- Exhausted arms with equal rebuilt keys and equal mark bits emit identical
complete marked words, independently of their remaining recursion budgets. -/
theorem terminal_mark_eq {i : Input} (f : Site i) (r : Reader i) (m : Nat) (a b : Arm i)
    (la : i.certified.executableLocalizedRerootChildren a = [])
    (lb : i.certified.executableLocalizedRerootChildren b = [])
    (ra : r a.occurrence = some none) (rb : r b.occurrence = some none)
    (keys : RingSingleCycleComparison.rebuilt i f a = RingSingleCycleComparison.rebuilt i f b)
    (bits : RingGroupedMark.bit m a = RingGroupedMark.bit m b) :
    RingOriginMarkWords.word? i f r m a = RingOriginMarkWords.word? i f r m b := by
  simp [RingOriginMarkWords.word?,RingOriginMarkWords.build,la,lb,ra,rb,keys,
    join,extend,bits]

/-- Promoting an atom different from both terminal twins leaves their actual
active-origin marked words equal. -/
theorem twin_mark_eq {i : Input} (p : TwinPair i) {f : Site i} (fr : Frame i f)
    (center : fr.center = p.c) (offU : f.val.root ≠ p.u) (offV : f.val.root ≠ p.v)
    (r : Reader i) (ready : RingGroupedStereo.Ready f r) (a b : Fin 4)
    (atU : (fr.arm a).occurrence.val.node.current? = some p.u)
    (atV : (fr.arm b).occurrence.val.node.current? = some p.v)
    (m : Nat) (notU : m ≠ p.u.val) (notV : m ≠ p.v.val) :
    RingOriginMarkWords.word? i f r m (cursor fr a) =
      RingOriginMarkWords.word? i f r m (cursor fr b) := by
  obtain ⟨la,lb,ra,rb,keys⟩ := twin_slot_facts p fr center offU offV r ready a b atU atV
  apply terminal_mark_eq f r m _ _ la lb ra rb keys
  have u : (p.u.val == m) = false := beq_eq_false_iff_ne.mpr notU.symm
  have v : (p.v.val == m) = false := beq_eq_false_iff_ne.mpr notV.symm
  simp [RingGroupedMark.bit,atU,atV,u,v,cursor,RingNestedActivePair.Frame.direction]

end TetraStereo.Engine.RingOriginTripleArms
assert_kernel_only TetraStereo.Engine.RingOriginTripleArms.twin_slot_facts
assert_kernel_only TetraStereo.Engine.RingOriginTripleArms.terminal_mark_eq
assert_kernel_only TetraStereo.Engine.RingOriginTripleArms.twin_mark_eq
