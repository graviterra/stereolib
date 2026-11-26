import TetraStereo.Engine.RingRule4bPathDecoding
import TetraStereo.Engine.RingChemicalGraphProof

/-! # Complete molecular Rule 4b readings up to reference exchange -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingRule4bHandOrbit
open OneCenter RingFullPathPairs RingRule5SeedExchange RingRule5Shape
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)

/-- At a through-4a tie, agreement at any two reference choices forces
agreement at their opposite choices. No previous signed-row equality is assumed. -/
theorem opposite_words {i f r rev s t} (ready : @RingGroupedStereo.Ready i f r)
    {a b : Arm i} (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    (tie : RingUnitTypeTransitions.key i r rev a = RingUnitTypeTransitions.key i r rev b)
    {w u v : List Bool} (a₁ : FullSource i r rev s a w)
    (b₁ : FullSource i r rev t b w) (a₂ : FullSource i r rev s.swap a u)
    (b₂ : FullSource i r rev t.swap b v) : u = v := by
  obtain ⟨x,tx,hx⟩ := a₁
  obtain ⟨y,ty,hy⟩ := b₁
  obtain ⟨z,tz,rfl⟩ := a₂
  obtain ⟨q,tq,rfl⟩ := b₂
  obtain ⟨rx,lx⟩ := record tx
  obtain ⟨ry,ly⟩ := record ty
  obtain ⟨rz,lz⟩ := record tz
  obtain ⟨rq,lq⟩ := record tq
  have eqn : rx = ry := (RingRule4bPathDecoding.layers_iff ready va vb oa ob tie lx ly).mpr
    (hx.symm.trans hy)
  have ax := molecular_exchange _ r rev s a lx lz
  have bx := molecular_exchange _ r rev t b ly lq
  rw [eqn,← bx] at ax
  rw [Oracle.walk_bits tz,Oracle.walk_bits tq,← flatten_layers lz,← flatten_layers lq,ax]

private theorem max_tie {a b c d : List Bool}
    (same : a = c ↔ b = d) (cross : a = d ↔ b = c) :
    max a b = max c d ↔ a = c ∨ a = d := by
  constructor
  · intro h
    rcases le_total a b with hab | hba <;> rcases le_total c d with hcd | hdc
    · rw [max_eq_right hab,max_eq_right hcd] at h
      exact Or.inl (same.mpr h)
    · rw [max_eq_right hab,max_eq_left hdc] at h
      exact Or.inr (cross.mpr h)
    · rw [max_eq_left hba,max_eq_right hcd] at h
      exact Or.inr h
    · rw [max_eq_left hba,max_eq_left hdc] at h
      exact Or.inl h
  · rintro (h | h)
    · rw [h,same.mp h]
    · rw [h,cross.mp h,max_comm]

/-- The best-of-both comparison ties exactly when fixed R agrees with
one of the other arm's two references. Both opposite readings then agree too. -/
theorem hanson_zero_iff {i f r rev} (ready : @RingGroupedStereo.Ready i f r)
    {a b : Arm i} (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    (tie : RingUnitTypeTransitions.key i r rev a = RingUnitTypeTransitions.key i r rev b) :
    hanson? i r rev a b = some 0 ↔
      pairs? i r rev .R a = pairs? i r rev .R b ∨
      pairs? i r rev .R a = pairs? i r rev .S b := by
  obtain ⟨ar,har,ear⟩ := source_exact ready rev .R a va oa
  obtain ⟨as',has,eas⟩ := source_exact ready rev .S a va oa
  obtain ⟨br,hbr,ebr⟩ := source_exact ready rev .R b vb ob
  obtain ⟨bs,hbs,ebs⟩ := source_exact ready rev .S b vb ob
  have same : ar = br ↔ as' = bs := by
    constructor
    · rintro rfl
      exact opposite_words ready va vb oa ob tie ((ear _).mpr rfl) ((ebr _).mpr rfl)
        ((eas _).mpr rfl) ((ebs _).mpr rfl)
    · rintro rfl
      exact opposite_words ready va vb oa ob tie ((eas _).mpr rfl) ((ebs _).mpr rfl)
        ((ear _).mpr rfl) ((ebr _).mpr rfl)
  have cross : ar = bs ↔ as' = br := by
    constructor
    · rintro rfl
      exact opposite_words ready va vb oa ob tie ((ear _).mpr rfl) ((ebs _).mpr rfl)
        ((eas _).mpr rfl) ((ebr _).mpr rfl)
    · rintro rfl
      exact opposite_words ready va vb oa ob tie ((eas _).mpr rfl) ((ebr _).mpr rfl)
        ((ear _).mpr rfl) ((ebs _).mpr rfl)
  simp only [hanson?,har,has,hbr,hbs,Option.some.injEq]
  change some (match RingOccurrenceStereo.fourLists ar as' br bs with
    | .lt => (-1 : Int) | .eq => 0 | .gt => 1) = some 0 ↔ ar = br ∨ ar = bs
  rw [RingOccurrenceStereo.fourLists_order]
  simp only [Option.some.injEq]
  have result := max_tie same cross
  generalize hc : compare (max ar as') (max br bs) = c
  change (match c with | .lt => (-1 : Int) | .eq => 0 | .gt => 1) = 0 ↔
    ar = br ∨ ar = bs
  have eqc : c = .eq ↔ max ar as' = max br bs := by
    rw [← hc,Std.compare_eq_eq_iff_eq]
  cases c <;> simpa using (eqc.trans result)

/-- The executable tie is exactly equality of all signed path spheres,
allowing one global exchange of the other arm's reference. -/
theorem layers_orbit_iff {i f r rev} (ready : @RingGroupedStereo.Ready i f r)
    {a b : Arm i} (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    (tie : RingUnitTypeTransitions.key i r rev a = RingUnitTypeTransitions.key i r rev b)
    {ar br bs ra rb rs}
    (left : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev .R))
      [Oracle.root (likeAt i r rev .R) a] ar ra)
    (right : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev .R))
      [Oracle.root (likeAt i r rev .R) b] br rb)
    (exchanged : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev .S))
      [Oracle.root (likeAt i r rev .S) b] bs rs) :
    hanson? i r rev a b = some 0 ↔ ra = rb ∨ ra = rs := by
  have canonical {q : Arm i} {seed : RS} {out rows} (valid : Valid q) (on : On f q)
      (walk : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev seed))
        [Oracle.root (likeAt i r rev seed) q] out rows) :
      pairs? i r rev seed q = some (out.filterMap (fun v => likeAt i r rev seed v.cursor)) := by
    obtain ⟨w,hw,ew⟩ := source_exact ready rev seed q valid on
    rw [hw]
    apply congrArg some
    symm
    apply (ew _).mp
    refine ⟨out,?_,rfl⟩
    have forget {row out rows}
        (walk : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev seed))
          row out rows) :
        FullTrace FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev seed)) row out := by
      induction walk with
      | stop => exact .stop
      | sphere grown sorted _ ih => exact .sphere grown sorted ih
    exact forget walk
  rw [hanson_zero_iff ready va vb oa ob tie,canonical va oa left,canonical vb ob right,
    canonical vb ob exchanged]
  simp only [Option.some.injEq]
  rw [← RingRule4bPathDecoding.layers_iff ready va vb oa ob tie left right,
    ← RingRule4bPathDecoding.layers_iff ready va vb oa ob tie left exchanged]

/-- A tie identifies the complete fixed-R signed sphere populations up to
one global sign reversal, followed by sorting each entire sphere again. -/
theorem signed_orbit_iff {i f r rev} (ready : @RingGroupedStereo.Ready i f r)
    {a b : Arm i} (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    (tie : RingUnitTypeTransitions.key i r rev a = RingUnitTypeTransitions.key i r rev b)
    {ar br bs ra rb rs}
    (left : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev .R))
      [Oracle.root (likeAt i r rev .R) a] ar ra)
    (right : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev .R))
      [Oracle.root (likeAt i r rev .R) b] br rb)
    (exchanged : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev .S))
      [Oracle.root (likeAt i r rev .S) b] bs rs) :
    hanson? i r rev a b = some 0 ↔ ra = rb ∨ ra = rb.map exchangeRow := by
  have orbit := layers_orbit_iff ready va vb oa ob tie left right exchanged
  rw [molecular_exchange _ r rev .R b right exchanged] at orbit
  exact orbit

/-- The public frozen reader inherits the same complete-word orbit criterion. -/
theorem frozen_zero_iff {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (rev : Bool) {a b : Arm i} (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b) :
    let r := RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) f
    RingUnitTypeTransitions.key i r rev a = RingUnitTypeTransitions.key i r rev b →
    (hanson? i r rev a b = some 0 ↔
      pairs? i r rev .R a = pairs? i r rev .R b ∨
      pairs? i r rev .R a = pairs? i r rev .S b) :=
  hanson_zero_iff (RingChemicalGraphProof.ready geom f) va vb oa ob

end TetraStereo.Engine.RingRule4bHandOrbit
assert_kernel_only TetraStereo.Engine.RingRule4bHandOrbit.opposite_words
assert_kernel_only TetraStereo.Engine.RingRule4bHandOrbit.hanson_zero_iff
assert_kernel_only TetraStereo.Engine.RingRule4bHandOrbit.frozen_zero_iff
assert_kernel_only TetraStereo.Engine.RingRule4bHandOrbit.layers_orbit_iff
assert_kernel_only TetraStereo.Engine.RingRule4bHandOrbit.signed_orbit_iff
