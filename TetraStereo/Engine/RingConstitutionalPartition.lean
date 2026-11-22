import TetraStereo.Engine.LocalizedChemicalRingPublic
import TetraStereo.OneCenter.AuthoritativeLocalizedRuleMajorAnalysis
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition

open OneCenter CertifiedLocalizedCIPInput CIPRuleEngine

abbrev Pair := Fin 4 × Fin 4
abbrev Context := Fin 4 → OfficialLigandRuleContext

/-- Each unordered comparison appears once, in canonical ligand-index order. -/
def pairs : List Pair := [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

theorem pairs_spec (p : Pair) : p ∈ pairs ↔ p.1 < p.2 := by
  revert p
  decide +kernel

/-- Total molecular comparison, carrying the trace of the first deciding constitutional rule. -/
def constitutional (i : Input) (c : i.certified.TetrahedralCenter) (p : Pair) :
    CIPTraceCertificate :=
  (i.certified.compareRuleMajorConstitutionAt? c p.1 p.2).get
    (i.certified.compareRuleMajorConstitutionAt?_isSome c p.1 p.2)

theorem constitutional_read (i : Input) (c : i.certified.TetrahedralCenter) (p : Pair) :
    i.certified.compareRuleMajorConstitutionAt? c p.1 p.2 = some (constitutional i c p) :=
  (Option.some_get _).symm

theorem occurrence_provenance (i : Input) (c : i.certified.TetrahedralCenter) (p : Pair) :
    i.certified.DeclarativeRuleMajorConstitutionalTrace c p.1 p.2
      (constitutional i c p).trace :=
  i.certified.compareRuleMajorConstitutionAt?_sound_declarative_trace _ _ _ _
    (constitutional_read i c p)

/-- Pairs for which a later rule must be consulted, computed solely from the molecule. -/
def residual (i : Input) (c : i.certified.TetrahedralCenter) : List Pair :=
  pairs.filter fun p => (constitutional i c p).outcome == .eq

theorem mem_residual (i : Input) (c : i.certified.TetrahedralCenter) (p : Pair) :
    p ∈ residual i c ↔ p.1 < p.2 ∧ (constitutional i c p).outcome = .eq := by
  simp [residual,pairs_spec]

theorem stable_trace (i : Input) (c : i.certified.TetrahedralCenter) (p : Pair)
    (strict : (constitutional i c p).outcome ≠ .eq) (ctx : Context) :
    (i.certified.compareRuleMajorAt? c ctx p.1 p.2).map CIPTraceCertificate.trace =
      some (constitutional i c p).trace := by
  have h : cipTraceOutcome (constitutional i c p).trace ≠ .eq := by
    rwa [(constitutional i c p).sound]
  simp [compareRuleMajorAt?,constitutional_read i c p,compareDigraphThenOfficialCertificate,
    CIPTraceCertificate.ofTrace,compareDigraphThenOfficialTrace,h]

private theorem on_tie (i : Input) (c : i.certified.TetrahedralCenter) (p : Pair)
    (tied : (constitutional i c p).outcome = .eq) (ctx : Context) :
    (i.certified.compareRuleMajorAt? c ctx p.1 p.2).map CIPTraceCertificate.outcome =
      some (cipTraceOutcome (compareOfficialContextTrace (ctx p.1) (ctx p.2))) := by
  have h := (constitutional i c p).sound.trans tied
  simp [compareRuleMajorAt?,constitutional_read i c p,
    compareDigraphThenOfficialTrace_outcome_of_digraph_eq h]

/-- Exact sensitivity at the explicit context interface. A single pair can realize every
ordering at that interface iff its entire constitutional comparison ties. The quantified
contexts are arbitrary arguments of the comparison function, not molecular publications. -/
theorem residual_iff_all_outcomes (i : Input) (c : i.certified.TetrahedralCenter) (p : Pair)
    (ordered : p.1 < p.2) :
    p ∈ residual i c ↔ ∀ o : Ordering, ∃ ctx : Context,
      (i.certified.compareRuleMajorAt? c ctx p.1 p.2).map CIPTraceCertificate.outcome = some o := by
  have different := Ne.symm (ne_of_lt ordered)
  constructor
  · intro mem o
    have tied := ((mem_residual i c p).mp mem).2
    let rs (a b : RS) : Context := fun x => OfficialLigandRuleContext.ofRS (if x = p.1 then a else b)
    cases o with
    | lt =>
      refine ⟨rs .S .R, (on_tie i c p tied _).trans ?_⟩
      simp only [rs,if_neg different]
      rfl
    | eq =>
      refine ⟨fun _ => .empty, (on_tie i c p tied _).trans ?_⟩
      rfl
    | gt =>
      refine ⟨rs .R .S, (on_tie i c p tied _).trans ?_⟩
      simp only [rs,if_neg different]
      rfl
  · intro covers
    refine (mem_residual i c p).mpr ⟨ordered,?_⟩
    by_contra strict
    obtain ⟨ctx,eqRead⟩ := covers .eq
    have h : cipTraceOutcome (constitutional i c p).trace ≠ .eq := by
      rwa [(constitutional i c p).sound]
    simp [compareRuleMajorAt?,constitutional_read i c p,
      compareDigraphThenOfficialTrace_outcome_of_digraph_ne_eq h,h] at eqRead

/-- The only occurrences whose later context can affect an unordered pair. -/
def neededLigands (i : Input) (c : i.certified.TetrahedralCenter) : List (Fin 4) :=
  (List.finRange 4).filter fun x => (residual i c).any fun p => x == p.1 || x == p.2

theorem mem_needed (i : Input) (c : i.certified.TetrahedralCenter) (x : Fin 4) :
    x ∈ neededLigands i c ↔ ∃ p ∈ residual i c, x = p.1 ∨ x = p.2 := by
  simp [neededLigands]

/-- Agreement only on the occurrences listed in the inventory preserves all six complete
rule traces, including the contextual suffix of each tied comparison. -/
theorem sufficient (i : Input) (c : i.certified.TetrahedralCenter) (f g : Context)
    (agree : ∀ x ∈ neededLigands i c, f x = g x) (p : Pair) (hp : p.1 < p.2) :
    i.certified.compareRuleMajorAt? c f p.1 p.2 =
      i.certified.compareRuleMajorAt? c g p.1 p.2 := by
  by_cases tie : (constitutional i c p).outcome = .eq
  · have mem := (mem_residual i c p).mpr ⟨hp,tie⟩
    have left := agree p.1 ((mem_needed i c _).mpr ⟨p,mem,Or.inl rfl⟩)
    have right := agree p.2 ((mem_needed i c _).mpr ⟨p,mem,Or.inr rfl⟩)
    simp [compareRuleMajorAt?,left,right]
  · have strict : cipTraceOutcome (constitutional i c p).trace ≠ .eq := by
      rwa [(constitutional i c p).sound]
    simp [compareRuleMajorAt?,constitutional_read i c p,compareDigraphThenOfficialCertificate,
      compareDigraphThenOfficialTrace,strict]

/-- Minimality at the explicit interface. For every listed occurrence, changing just that
one context can alter the outcome of at least one actual pair in the center. -/
theorem necessary (i : Input) (c : i.certified.TetrahedralCenter) (x : Fin 4)
    (hx : x ∈ neededLigands i c) :
    ∃ f g : Context, (∀ y, y ≠ x → f y = g y) ∧ ∃ p ∈ pairs,
      (i.certified.compareRuleMajorAt? c f p.1 p.2).map CIPTraceCertificate.outcome ≠
      (i.certified.compareRuleMajorAt? c g p.1 p.2).map CIPTraceCertificate.outcome := by
  obtain ⟨p,mem,side⟩ := (mem_needed i c x).mp hx
  obtain ⟨ordered,tie⟩ := (mem_residual i c p).mp mem
  let f : Context := fun _ => .ofRS .S
  let g : Context := fun y => if y = x then .ofRS .R else .ofRS .S
  refine ⟨f,g,(fun y hy => by simp [f,g,hy]),p,(pairs_spec p).mpr ordered,?_⟩
  rw [on_tie i c p tie f,on_tie i c p tie g]
  rcases side with h | h
  · subst x
    simp only [f,g,if_neg (Ne.symm (ne_of_lt ordered)),ite_true]
    decide +revert
  · subst x
    simp only [f,g,if_neg (ne_of_lt ordered),ite_true]
    decide +revert

/-- Every sufficient set of occurrences contains the computed set. The result quantifies over
all finite rings and all explicit official contexts; no guessed reference schedule is used. -/
theorem least_support (i : Input) (c : i.certified.TetrahedralCenter) (s : Fin 4 → Prop) :
    (∀ f g : Context, (∀ x, s x → f x = g x) → ∀ p ∈ pairs,
      (i.certified.compareRuleMajorAt? c f p.1 p.2).map CIPTraceCertificate.outcome =
      (i.certified.compareRuleMajorAt? c g p.1 p.2).map CIPTraceCertificate.outcome) ↔
    ∀ x ∈ neededLigands i c, s x := by
  constructor
  · intro invariant x hx
    by_contra outside
    obtain ⟨f,g,agree,p,hp,diff⟩ := necessary i c x hx
    exact diff (invariant f g (fun y hy => agree y (fun e => outside (e ▸ hy))) p hp)
  · intro covers f g agree p hp
    rw [sufficient i c f g (fun x hx => agree x (covers x hx)) p ((pairs_spec p).mp hp)]

/-- Complete center inventory in atom-index order, retaining sites even when all six pairs
are already resolved or all six have tied. -/
def inventory (i : Input) : List (i.certified.TetrahedralCenter × List Pair) :=
  i.certified.canonicalTetrahedralCenters.map fun c => (c,residual i c)

theorem inventory_exact (i : Input) (c : i.certified.TetrahedralCenter) (ps : List Pair) :
    (c,ps) ∈ inventory i ↔ ps = residual i c := by
  constructor
  · intro h
    obtain ⟨a,_,e⟩ := List.mem_map.mp h
    cases e
    rfl
  · rintro rfl
    exact List.mem_map.mpr ⟨c,(i.certified.mem_canonicalTetrahedralCenters_iff c).mpr c.2,rfl⟩

end TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition

assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.occurrence_provenance
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.stable_trace
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.residual_iff_all_outcomes
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.inventory_exact

assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.least_support
