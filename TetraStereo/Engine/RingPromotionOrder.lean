import TetraStereo.Engine.RingMolecularPromotion

set_option autoImplicit false
namespace TetraStereo.Engine.RingChemicalPriority.Promotion

/-- Every observed marked word is built from the exact outward arm of this
occurrence with the same frozen descriptors in its before/after trees. -/
theorem Arm.observed_layout {m focus} (a : Arm m focus) (p : List Nat) (d mark : Nat)
    {z : List (List Nat)} {o : Observation} (ok : a.observe p d (some mark) = some (z,some o)) :
    ∃ n ss, ∃ layout : Layout m ss, a.start = some n ∧ sites m (m.atomCount+1) n 0 [] true = some ss ∧
      layout? m ss = some layout ∧ o.spheres = layout.read mark ∧
      decorated m n a.facts none = some o.before ∧ decorated m n a.facts (some mark) = some o.after := by
  cases hz : ligandRows? m p a.ligand d with
  | none => simp [Arm.observe,hz] at ok
  | some prefixRows =>
    cases hn : a.start with
    | none => simp [Arm.observe,hz,hn] at ok
    | some n =>
      cases hb : decorated m n a.facts none with
      | none => simp [Arm.observe,hz,hn,hb] at ok
      | some b =>
        cases hs : sites m (m.atomCount+1) n 0 [] true with
        | none => simp [Arm.observe,hz,hn,hb,hs] at ok
        | some ss =>
          cases hl : layout? m ss with
          | none => simp [Arm.observe,hz,hn,hb,hs,hl] at ok
          | some lay =>
            cases ha : decorated m n a.facts (some mark) with
            | none => simp [Arm.observe,hz,hn,hb,hs,ha] at ok
            | some afterCode =>
              simp [Arm.observe,hz,hn,hb,hs,hl,ha] at ok
              obtain ⟨_,rfl⟩ := ok
              exact ⟨n,ss,lay,rfl,hs,hl,rfl,hb,ha⟩

/-- For two observationally tied arms through Rule 5, a strict promoted
decision is the sign of the full word of marked occurrences in every legal
molecular traversal of the actual arms. -/
theorem molecular_winner {m focus} (a b : Arm m focus) (p : List Nat) (d mark : Nat)
    {za zb oa ob} (ha : a.observe p d (some mark) = some (za,some oa))
    (hb : b.observe p d (some mark) = some (zb,some ob))
    (prior : oa.constitution = ob.constitution) (picked : compare? oa ob = some .gt) :
    ∃ na nb ls rs, a.start = some na ∧ b.start = some nb ∧
      sites m (m.atomCount+1) na 0 [] true = some ls ∧ sites m (m.atomCount+1) nb 0 [] true = some rs ∧
      oa.before = ob.before ∧ ∀ l r, Legal m ls l → Legal m rs r →
        r.map (fun s => (s.atom == mark).toNat) < l.map (fun s => (s.atom == mark).toNat) := by
  obtain ⟨na,ls,la,an,al,_,aw,_,_⟩ := a.observed_layout p d mark ha
  obtain ⟨nb,rs,lb,bn,bl,_,bw,_,_⟩ := b.observed_layout p d mark hb
  have before := (strict_promotion prior picked (by decide)).1
  have diff : oa.after ≠ ob.after := by
    intro h
    simp [compare?,prior,before,h] at picked
  by_cases keys : oa.keys = ob.keys
  · have win : PairSpheres.seniorLeft? oa.spheres ob.spheres = some true := by
      cases h : PairSpheres.seniorLeft? oa.spheres ob.spheres with
      | none => simp [compare?,prior,before,diff,keys,h] at picked
      | some side => cases side <;> simp_all [compare?]
    exact ⟨na,nb,ls,rs,an,bn,al,bl,before,strict_in_legal_orders la lb mark (aw ▸ bw ▸ win)⟩
  · simp [compare?,prior,before,diff,keys] at picked

open OneCenter LocalizedGenericMarkedRecalculation
open DeclarativeCIP.ProductionOccurrenceRules456 (promotionAggregate)

/-- Residual molecular ties at every promotion imply a geometry-independent
refusal. No coordinate or signed-volume assumption is needed. -/
theorem result_of_tied {ts : List Trial} (tied : ∀ t ∈ ts, t.unique = false) (g : Geometry) :
    result g ts = some none := by
  have zero : DeclarativeCIP.ProductionOccurrenceRules456.promotionBalance
      (ts.map (Trial.outcome g)) = some 0 := by
    induction ts with
    | nil => rfl
    | cons t rest ih =>
      have ht := tied t (by simp)
      have tail := ih (fun u h => tied u (by simp [h]))
      simpa [Trial.outcome,ht,DeclarativeCIP.ProductionOccurrenceRules456.promotionBalance] using tail
  simp [result,promotionAggregate,zero]

end TetraStereo.Engine.RingChemicalPriority.Promotion
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.molecular_winner
