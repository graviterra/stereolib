import TetraStereo.OneCenter.LocalizedChemicalRingRegeneratedLifetime

set_option autoImplicit false
set_option maxHeartbeats 45000
set_option Elab.async false

namespace TetraStereo.Engine.RingReachableReferencePolicy
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRingJointPreparedSourceQueries LocalizedChemicalRingJointPreparedSourceStep
open LocalizedChemicalRingJointPreparedSourceModel LocalizedChemicalRingRegeneratedLifetime
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedGenericMarkedRecalculation (Geometry consensus caseFromMirror? mirror structuralDepth WellFormedBonds)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant)
open LocalizedChemicalRingReferencePolicy (policyFallback ReferenceLifetime)
open scoped Classical
noncomputable section

variable {i : CertifiedLocalizedCIPInput} {m : RawMolecule}
abbrev FrameFamily (i : CertifiedLocalizedCIPInput) (m : RawMolecule) :=
  (q : SourceQuery i m) → Σ c, OccurrenceData i m c q.1

structure Call (i : CertifiedLocalizedCIPInput) (m : RawMolecule) where
  query : SourceQuery i m
  geometry : Geometry
  references : List i.Atom

variable (single : i.moleculeGraph.SimpleBonded) (frame : FrameFamily i m)

private def keys (p : Profile i m) (q : SourceQuery i m) (g : Geometry) (rs : List i.Atom) :=
  sourceKeysAt i single (profileFamily i m p q) (frame q).2.target (frame q).2.frame g rs

/-- A real atom in a slot selected from the non-strict four-way ranking in
this occurrence, context and geometry. -/
def Selected (p : Profile i m) (u : Call i m) (g : Geometry) (atom : i.Atom) : Prop :=
  let k := keys single frame p u.query g u.references
  ¬ Function.Injective k ∧ ∃ slot ∈ sourceSelectedSlots k,
    frameAtom? i (frame u.query).2.frame slot = some atom

def Side (u : Call i m) (g : Geometry) := g = u.geometry ∨ g = mirror u.geometry

/-- Dependency of the replacement-policy update, evaluated on p. An ordinary
ranking reads descendants in its incoming context. Only its eligible promotions
can read a descendant map under a newly selected singleton. -/
structure Edge (p : Profile i m) (u v : Call i m) : Prop where
  below : StrictDescendant m u.query.1 v.query.1
  side : Side u v.geometry
  context : v.references = u.references ∨
    ∃ atom, v.references = [atom] ∧ Selected single frame p u v.geometry atom

abbrev Reach (p : Profile i m) := Relation.ReflTransGen (Edge single frame p)

private def finish (rank : (Fin 4 → LocalizedChemicalRingJointMarkerRanking.RefinedKey) → Option RS)
    (k : Fin 4 → LocalizedChemicalRingJointMarkerRanking.RefinedKey) (trial : Fin 4 → Option RS) :=
  if Function.Injective k then rank k else consensus ((sourceSelectedSlots k).map trial)

private theorem finish_congr {rank k l x y} (same : k = l)
    (each : ¬ Function.Injective k → ∀ slot ∈ sourceSelectedSlots k, x slot = y slot) :
    finish rank k x = finish rank l y := by
  subst l
  unfold finish
  split
  · rfl
  · rename_i tied
    exact congrArg consensus (List.map_congr_left (each tied))

private theorem keys_local (p t : Profile i m) (q : SourceQuery i m) (g : Geometry) (rs : List i.Atom)
    (agree : ∀ d : SourceQuery i m, StrictDescendant m q.val d.val → p g rs d = t g rs d) :
    keys single frame p q g rs = keys single frame t q g rs := by
  have maps := LocalizedChemicalRingJointPreparedSourceQueryMap.sourceQueryMap_local i m q _ _ agree
  unfold keys sourceKeysAt profileFamily
  rw [maps]

private def strictRead (q : SourceQuery i m) (g : Geometry)
    (k : Fin 4 → LocalizedChemicalRingJointMarkerRanking.RefinedKey) :=
  if Function.Injective k then sourceReading i g (frame q).2.frame k else none

private def trial (p : Profile i m) (u : Call i m) (g : Geometry) (slot : Fin 4) :=
  policyFallback i single .current .regenerated (profileFamily i m p u.query)
    (frame u.query).2.target (frame u.query).2.frame g u.references slot

private theorem trial_eq (p : Profile i m) (u : Call i m) (g : Geometry) (slot : Fin 4) :
    trial single frame p u g slot = (frameAtom? i (frame u.query).2.frame slot).bind
      (fun a => strictRead frame u.query g (keys single frame p u.query g [a])) := rfl

private theorem raw_eq (p : Profile i m) (u : Call i m) (g : Geometry) :
    raw i m single frame .current p u.query g u.references =
      finish (sourceReading i g (frame u.query).2.frame)
        (keys single frame p u.query g u.references) (trial single frame p u g) := rfl

private theorem raw_local (p t : Profile i m) (u : Call i m) (g : Geometry) (side : Side u g)
    (agree : ∀ v, Edge single frame p u v →
      p v.geometry v.references v.query = t v.geometry v.references v.query) :
    raw i m single frame .current p u.query g u.references =
      raw i m single frame .current t u.query g u.references := by
  rw [raw_eq single frame p u g, raw_eq single frame t u g]
  apply finish_congr (keys_local single frame p t _ _ _ (fun d below =>
    agree ⟨d,g,u.references⟩ ⟨below,side,Or.inl rfl⟩))
  intro tied slot mem
  rw [trial_eq,trial_eq]
  apply Option.bind_congr
  intro a hit
  apply congrArg (strictRead frame u.query g)
  apply keys_local
  intro d below
  exact agree ⟨d,g,[a]⟩ ⟨below,side,Or.inr ⟨a,rfl,tied,slot,mem,hit⟩⟩

private theorem local_update (p t : Profile i m) (u : Call i m)
    (agree : ∀ v, Edge single frame p u v →
      p v.geometry v.references v.query = t v.geometry v.references v.query) :
    update i m single frame .current p u.query u.geometry u.references =
      update i m single frame .current t u.query u.geometry u.references :=
  congrArg₂ caseFromMirror? (raw_local single frame p t u _ (Or.inl rfl) agree)
    (raw_local single frame p t u _ (Or.inr rfl) agree)

abbrev accumulated := solution i m single frame .accumulated
abbrev replaced := solution i m single frame .current

/-- If the profiles disagree, strict molecular descent reaches a call on the
molecular dependency cone where changing the local lifetime alone changes the
complete two-geometry descriptor. Every earlier promotion on this cone was
selected using molecular keys derived from the accumulated solution. -/
theorem disagreement_reachable (admit : m.StereochemicalAdmissible) (start : Call i m)
    (different : accumulated single frame start.geometry start.references start.query ≠
      replaced single frame start.geometry start.references start.query) :
    ∃ u, Reach single frame (accumulated single frame) start u ∧
      update i m single frame .accumulated (accumulated single frame) u.query u.geometry u.references ≠
      update i m single frame .current (accumulated single frame) u.query u.geometry u.references := by
  have wf : WellFormedBonds m := fun b hb =>
    ⟨(admit.1.1 b hb).1,(admit.1.1 b hb).2.1⟩
  induction start using (measure (fun v : Call i m => structuralDepth m v.query.1)).wf.induction with
  | h u ih =>
    by_cases stable : update i m single frame .accumulated (accumulated single frame) u.query u.geometry u.references =
        update i m single frame .current (accumulated single frame) u.query u.geometry u.references
    · have bad : ∃ v, Edge single frame (accumulated single frame) u v ∧
          accumulated single frame v.geometry v.references v.query ≠ replaced single frame v.geometry v.references v.query := by
        by_contra! all
        apply different
        exact (solution_equation i m admit single frame .accumulated ..).trans
          (stable.trans ((local_update single frame _ _ u all).trans
          (solution_equation i m admit single frame .current ..).symm))
      obtain ⟨v,edge,diff⟩ := bad
      obtain ⟨w,reach,loss⟩ := ih v
        (LocalizedChemicalRingJointPreparedStructuralProfile.structuralDepth_lt m wf u.query.2.1 edge.below) diff
      exact ⟨w,Relation.ReflTransGen.head edge reach,loss⟩
    · exact ⟨u,.refl,stable⟩

private theorem descendant_trans {u v w : RawMolecule.CanonicalBranchNode}
    (h : StrictDescendant m u v) (k : StrictDescendant m v w) : StrictDescendant m u w := by
  obtain ⟨_,hu,uv⟩ := h
  obtain ⟨_,hv,vw⟩ := k
  exact ⟨_,hu,(uv.tail hv).trans vw⟩

theorem reach_descends {p : Profile i m} {root u : Call i m}
    (path : Reach single frame p root u) :
    u.query = root.query ∨ StrictDescendant m root.query.val u.query.val := by
  induction path with
  | refl => exact Or.inl rfl
  | tail _ edge prior =>
    exact Or.inr (prior.elim (fun eqn => eqn ▸ edge.below) (fun below => descendant_trans below edge.below))

/-- Every nonempty reference on a path from an unmarked root is a singleton.
An earlier reached frame supplies the actual marked atom, the geometry of its
selection and its strict ancestry of the current query. -/
theorem origin {p : Profile i m} {root u : Call i m} (empty : root.references = [])
    (path : Reach single frame p root u) :
    u.references = [] ∨ ∃ a parent g, u.references = [a] ∧ Reach single frame p root parent ∧
      Reach single frame p parent u ∧ StrictDescendant m parent.query.1 u.query.1 ∧ Side parent g ∧ Selected single frame p parent g a := by
  induction path with
  | refl => exact Or.inl empty
  | @tail v w prior edge ih =>
    rcases edge.context with inherited | ⟨a,marked,chosen⟩
    · rcases ih with unmarked | ⟨a,parent,g,marked,reach,segment,below,side,selected⟩
      · exact Or.inl (inherited.trans unmarked)
      · exact Or.inr ⟨a,parent,g,inherited.trans marked,reach,segment.tail edge,descendant_trans below edge.below,side,selected⟩
    · exact Or.inr ⟨a,v,w.geometry,marked,prior,Relation.ReflTransGen.single edge,edge.below,edge.side,chosen⟩

def effect (life : ReferenceLifetime) (u : Call i m) :=
  update i m single frame life (accumulated single frame) u.query u.geometry u.references

/-- The same eligible molecular slot supplies the fresh atom and the
two differing promoted readings, on the same accumulated descriptor table. -/
def ChangedSelection (u : Call i m) (g : Geometry) (fresh : i.Atom) : Prop :=
  let p := accumulated single frame
  let k := keys single frame p u.query g u.references
  let attempt (life : ReferenceLifetime) := policyFallback i single life .regenerated
    (profileFamily i m p u.query) (frame u.query).2.target (frame u.query).2.frame g u.references
  ¬ Function.Injective k ∧ ∃ slot ∈ sourceSelectedSlots k,
    frameAtom? i (frame u.query).2.frame slot = some fresh ∧ attempt .accumulated slot ≠ attempt .current slot

/-- An unmarked discrepancy needs two compatible selections. The first
supplies precisely the older atom at a reached strict descendant. The second
is a real slot in that descendant's tied population on the input side or its
mirror. The local policy change survives consensus and mirror casing there. -/
theorem nested_selections (admit : m.StereochemicalAdmissible) (root : Call i m)
    (empty : root.references = [])
    (different : accumulated single frame root.geometry root.references root.query ≠
      replaced single frame root.geometry root.references root.query) :
    ∃ parent u g₁ g₂ old fresh,
      Reach single frame (accumulated single frame) root parent ∧
      Reach single frame (accumulated single frame) parent u ∧
      StrictDescendant m parent.query.1 u.query.1 ∧ Side parent g₁ ∧ Side u g₂ ∧
      Selected single frame (accumulated single frame) parent g₁ old ∧ u.references = [old] ∧
      ChangedSelection single frame u g₂ fresh ∧
      effect single frame .accumulated u ≠ effect single frame .current u := by
  obtain ⟨u,path,loss⟩ := disagreement_reachable single frame admit root different
  rcases origin single frame empty path with unmarked | ⟨old,parent,g₁,incoming,prior,segment,below,side,chosen⟩
  · exact False.elim (loss (by rw [unmarked]; rfl))
  · let p := accumulated single frame
    have changes : ∃ g₂, Side u g₂ ∧ raw i m single frame .accumulated p u.query g₂ u.references ≠
        raw i m single frame .current p u.query g₂ u.references := by
      by_contra! all
      exact loss (congrArg₂ caseFromMirror? (all _ (Or.inl rfl)) (all _ (Or.inr rfl)))
    obtain ⟨g₂,side₂,rawLoss⟩ := changes
    let k := keys single frame p u.query g₂ u.references
    let trial (life : ReferenceLifetime) := policyFallback i single life .regenerated
      (profileFamily i m p u.query) (frame u.query).2.target (frame u.query).2.frame g₂ u.references
    change (if Function.Injective k then _ else consensus ((sourceSelectedSlots k).map (trial .accumulated))) ≠
      (if Function.Injective k then _ else consensus ((sourceSelectedSlots k).map (trial .current))) at rawLoss
    by_cases sep : Function.Injective k
    · simp [sep] at rawLoss
    · rw [if_neg sep,if_neg sep] at rawLoss
      have bad : ∃ n ∈ sourceSelectedSlots k, trial .accumulated n ≠ trial .current n := by
        by_contra! agree
        exact rawLoss (congrArg consensus (List.map_congr_left agree))
      obtain ⟨slot,member,bad⟩ := bad
      cases ha : frameAtom? i (frame u.query).2.frame slot with
      | none => simp [trial,policyFallback,ha] at bad
      | some fresh => exact ⟨parent,u,g₁,g₂,old,fresh,prior,segment,below,side,side₂,chosen,incoming,
          ⟨sep,slot,member,ha,bad⟩,loss⟩


private def beforeStereo (key : LocalizedChemicalRingJointMarkerRanking.RefinedKey) :=
  (ofLex ((ofLex ((ofLex ((ofLex key).1)).1)).1)).1

/-- Molecular observation column before the stereo-unit and reference
comparisons. Erasing the descriptor table, coordinates and all marks computes
this column at the same molecular occurrence and frame. -/
def structuralColumn (q : SourceQuery i m) (slot : Fin 4) :=
  beforeStereo (keys single frame (fun _ _ _ => none) q (fun _ => none) [] slot)

theorem structuralColumn_independent (p : Profile i m) (q : SourceQuery i m) (g : Geometry)
    (refs : List i.Atom) (slot : Fin 4) :
    beforeStereo (keys single frame p q g refs slot) = structuralColumn single frame q slot := by
  simp only [beforeStereo,structuralColumn,keys,sourceKeysAt,
    LocalizedChemicalRingJointPreparedSourceKeys.sourceKeys,
    LocalizedChemicalRingJointPreparedSourceKeys.sourceCutKey,ofLex_toLex,
    DeclarativeCIP.retainedCompleteLigandRule5KeyAt_prior,DeclarativeCIP.retainedCompleteLigandPriorKeyAt_rank,
    DeclarativeCIP.retainedMolecularRankPairAt,DeclarativeCIP.observedPairKey]

private theorem selected_collision {p : Profile i m} {u : Call i m} {g atom}
    (chosen : Selected single frame p u g atom) :
    ¬ Function.Injective (structuralColumn single frame u.query) := by
  obtain ⟨_,slot,selected,_⟩ := chosen
  obtain ⟨_,other,_,ne,same⟩ := (sourceSelectedSlots_mem_iff _ _).mp selected
  have eqn := congrArg beforeStereo same
  rw [structuralColumn_independent,structuralColumn_independent] at eqn
  exact fun injective => ne (injective eqn)

/-- Different regenerated descriptors require two different actual molecular
atoms, at comparable real occurrences, each with a collision already in
its mark-free, descriptor-free column. The witness imposes no bound on the
number of other stereocenters or on the depth of the ring. -/
theorem structural_obstruction (admit : m.StereochemicalAdmissible) (root : Call i m)
    (empty : root.references = [])
    (different : accumulated single frame root.geometry root.references root.query ≠
      replaced single frame root.geometry root.references root.query) :
    ∃ parent child : SourceQuery i m, (parent = root.query ∨ StrictDescendant m root.query.val parent.val) ∧
      StrictDescendant m parent.val child.val ∧
      child.val.atom ≠ parent.val.atom ∧
      ¬ Function.Injective (structuralColumn single frame parent) ∧
      ¬ Function.Injective (structuralColumn single frame child) := by
  obtain ⟨p,u,_,g,_,a,path,_,below,_,_,first,_,second,_⟩ := nested_selections single frame admit root empty different
  have real : u.query.val.forcedLeaf = false := by
    simp [RawMolecule.CanonicalBranchNode.forcedLeaf,u.query.property.2.1]
  obtain ⟨tied,j,mem,atom,_⟩ := second
  have selected : Selected single frame (accumulated single frame) u g a := ⟨tied,j,mem,atom⟩
  exact ⟨p.query,u.query,reach_descends single frame path,below,LocalizedMarkedTerminalReferenceScope.strictDescendant_atom_ne
    p.query.property.1 below real,selected_collision single frame first,selected_collision single frame selected⟩

/-- Independent structural criterion for agreement of the complete descriptor
(including its case and refusal) at every unmarked query. Siblings can each
contain ambiguous centers: only comparable occurrences matter. -/
theorem agree_of_separated_collisions (admit : m.StereochemicalAdmissible)
    (separated : ∀ p u : SourceQuery i m, StrictDescendant m p.val u.val →
      Function.Injective (structuralColumn single frame p) ∨ Function.Injective (structuralColumn single frame u))
    (q : SourceQuery i m) (g : Geometry) :
    accumulated single frame g [] q = replaced single frame g [] q := by
  by_contra different
  obtain ⟨p,u,_,below,_,left,right⟩ := structural_obstruction single frame admit ⟨q,g,[]⟩ rfl different
  exact (separated p u below).elim left right

/-- To certify a single query, only its own descendants can obstruct
agreement. Nested collisions elsewhere in the input are unrestricted. -/
theorem agree_at_query (admit : m.StereochemicalAdmissible) (q : SourceQuery i m)
    (separated : ∀ p u : SourceQuery i m,
      (p = q ∨ StrictDescendant m q.val p.val) → StrictDescendant m p.val u.val →
      Function.Injective (structuralColumn single frame p) ∨ Function.Injective (structuralColumn single frame u))
    (g : Geometry) : accumulated single frame g [] q = replaced single frame g [] q := by
  by_contra different
  obtain ⟨p,u,within,below,_,left,right⟩ := structural_obstruction single frame admit ⟨q,g,[]⟩ rfl different
  exact (separated p u within below).elim left right

/-- Arbitrarily many detected centers are allowed if at most one molecular
atom can carry a collision in the pre-stereo column. No two real
ancestor/descendant occurrences can both represent that atom. -/
theorem agree_of_one_collision_atom (admit : m.StereochemicalAdmissible) (atom : Nat)
    (onlyAtom : ∀ q : SourceQuery i m, ¬ Function.Injective (structuralColumn single frame q) →
      q.val.atom = atom) (q : SourceQuery i m) (g : Geometry) :
    accumulated single frame g [] q = replaced single frame g [] q := by
  by_contra different
  obtain ⟨p,u,_,_,distinct,left,right⟩ := structural_obstruction single frame admit ⟨q,g,[]⟩ rfl different
  exact distinct ((onlyAtom u right).trans (onlyAtom p left).symm)

end
end TetraStereo.Engine.RingReachableReferencePolicy

assert_kernel_only TetraStereo.Engine.RingReachableReferencePolicy.disagreement_reachable
assert_kernel_only TetraStereo.Engine.RingReachableReferencePolicy.origin
assert_kernel_only TetraStereo.Engine.RingReachableReferencePolicy.nested_selections
assert_kernel_only TetraStereo.Engine.RingReachableReferencePolicy.structuralColumn_independent
assert_kernel_only TetraStereo.Engine.RingReachableReferencePolicy.structural_obstruction
assert_kernel_only TetraStereo.Engine.RingReachableReferencePolicy.agree_of_separated_collisions
assert_kernel_only TetraStereo.Engine.RingReachableReferencePolicy.agree_at_query
assert_kernel_only TetraStereo.Engine.RingReachableReferencePolicy.agree_of_one_collision_atom
