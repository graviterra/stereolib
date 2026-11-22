import TetraStereo.Engine.RingSphereOrdinalRange

set_option autoImplicit false

namespace TetraStereo.Engine.RingSphereReadings
open RingSphereOrdinalRange (ordinal? seeded? local?)

/-- Compute the signed consensus using attainable extremal projected words.
Each rule sorts its spheres and compares two pairs of endpoints. -/
def fast? (a b : Profile) (rev : Bool) : Option Int := do
  guard (ordinal? (unitRows a rev) (unitRows b rev) == some 0)
  let x := upperRows a rev
  let y := upperRows b rev
  guard (oneReference x && oneReference y)
  let first ← local? x y
  if first ≠ 0 then return first
  let low ← ordinal? (lowerRows a rev) (lowerRows b rev)
  if low ≠ 0 then return low
  let plus ← seeded? .R x y
  let minus ← seeded? .S x y
  return CentresRing.PairList.combine plus minus

@[csimp] theorem score_fast : @score? = @fast? := by
  funext a b rev
  by_cases h : (oneReference (upperRows a rev) && oneReference (upperRows b rev)) = true
  · rw [Bool.and_eq_true] at h
    obtain ⟨hx,hy⟩ := h
    simp only [score?,fast?,RingSphereOrdinalRange.ordinal_eq_across,
      RingSphereOrdinalRange.seeded_eq_across,RingSphereOrdinalRange.local_eq_across _ _ hx hy]
  · cases u : across? ord (unitRows a rev) (unitRows b rev) <;>
      simp [score?,fast?,RingSphereOrdinalRange.ordinal_eq_across,u,h,guard,Option.bind_eq_bind]

end TetraStereo.Engine.RingSphereReadings

assert_kernel_only TetraStereo.Engine.RingSphereReadings.score_fast
