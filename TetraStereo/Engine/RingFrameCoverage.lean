import TetraStereo.Engine.RingPromotionBalance
import TetraStereo.Engine.RingReferenceDerivation
import TetraStereo.OneCenter.LocalizedMarkedMolecularConfiguration

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.ReferenceFrame
open OneCenter LocalizedGenericMarkedRecalculation Recursive

/-- Reflection preserves equivalence of each incident pair. Strict directions may change. -/
def SharedTies (ids : List Nat) (t : Table) : Prop :=
  ∀ i ∈ ids, ∀ j ∈ ids, orderAt t false i j = some .eq ↔ orderAt t true i j = some .eq

private def weak (t : Table) (rev : Bool) (i j : Nat) : Bool :=
  (orderAt t rev i j).any (· != .lt)

private theorem pairFacts {ids t rev i j} (h : coherent ids t rev = true)
    (hi : i ∈ ids) (hj : j ∈ ids) :
    (orderAt t rev i j).isSome = true ∧ orderAt t rev j i = (orderAt t rev i j).map Ordering.swap := by
  have both := List.all_eq_true.mp (List.all_eq_true.mp h i hi) j hj
  simpa only [Bool.and_eq_true,beq_iff_eq] using (Bool.and_eq_true_iff.mp both).1

private abbrev Id (ids : List Nat) := {i : Nat // i ∈ ids}
private def weakId (ids : List Nat) (t : Table) (rev : Bool) (i j : Id ids) : Prop :=
  weak t rev i.val j.val = true
private instance (ids : List Nat) (t : Table) (rev : Bool) : DecidableRel (weakId ids t rev) :=
  fun i j => inferInstanceAs (Decidable (weak t rev i.val j.val = true))

private def sortedIds (ids : List Nat) (t : Table) (rev : Bool) :=
  (ids.attach.insertionSort (weakId ids t rev)).map Subtype.val

private theorem sortedPerm (ids : List Nat) (t : Table) (rev : Bool) : (sortedIds ids t rev).Perm ids := by
  simpa [sortedIds] using (List.perm_insertionSort (weakId ids t rev) ids.attach).map Subtype.val

private theorem strictSorted {ids t rev} (h : coherent ids t rev = true) (distinct : ids.Nodup)
    (apart : ∀ i ∈ ids, ∀ j ∈ ids, i ≠ j → orderAt t rev i j ≠ some .eq) :
    (sortedIds ids t rev).Pairwise fun i j => orderAt t rev i j = some .gt := by
  let r := weakId ids t rev
  letI : Std.Total r := ⟨fun a b => by
    obtain ⟨found,recip⟩ := pairFacts h a.property b.property
    change weak t rev a.val b.val = true ∨ weak t rev b.val a.val = true
    unfold weak
    rw [recip]
    cases sign : orderAt t rev a.val b.val with
    | none => simp [sign] at found
    | some x => cases x <;> decide⟩
  letI : IsTrans (Id ids) r := ⟨fun a b c ab bc => by
    have both := List.all_eq_true.mp (List.all_eq_true.mp h a.val a.property) b.val b.property
    have all := List.all_eq_true.mp (Bool.and_eq_true_iff.mp both).2 c.val c.property
    change (!(weak t rev a.val b.val && weak t rev b.val c.val) || weak t rev a.val c.val) = true at all
    change weak t rev a.val b.val = true at ab
    change weak t rev b.val c.val = true at bc
    simpa only [ab,bc,Bool.true_and,Bool.not_true,Bool.false_or] using all⟩
  have sorted : (sortedIds ids t rev).Pairwise (fun a b => weak t rev a b = true) :=
    List.pairwise_map.mpr (List.pairwise_insertionSort r ids.attach)
  have perm := sortedPerm ids t rev
  have unique : (sortedIds ids t rev).Nodup := perm.nodup_iff.mpr distinct
  have joined := List.Pairwise.and_mem.mp (sorted.and unique)
  apply joined.imp
  intro i j data
  obtain ⟨hi,hj,yes,diff⟩ := data
  have ne := apart i (perm.mem_iff.mp hi) j (perm.mem_iff.mp hj) diff
  cases v : orderAt t rev i j with
  | none => simp [weak,v] at yes
  | some s => cases s <;> simp_all [weak]

private theorem uniqueOrder {ids t rev} (h : coherent ids t rev = true) (distinct : ids.Nodup)
    (apart : ∀ i ∈ ids, ∀ j ∈ ids, i ≠ j → orderAt t rev i j ≠ some .eq) :
    orders ids t rev = [sortedIds ids t rev] := by
  have perm := sortedPerm ids t rev
  have sorted := strictSorted h distinct apart
  have nd : (orders ids t rev).Nodup := ((List.permutations_perm_permutations' ids).nodup_iff.mp
    (List.nodup_permutations ids distinct)).filter _
  have member : sortedIds ids t rev ∈ orders ids t rev :=
    List.mem_filter.mpr ⟨List.mem_permutations'.mpr perm,decide_eq_true sorted⟩
  have only (q) (hq : q ∈ orders ids t rev) : q = sortedIds ids t rev := by
    obtain ⟨inPerm,ok⟩ := List.mem_filter.mp hq
    have qp := List.mem_permutations'.mp inPerm
    apply (qp.trans perm.symm).eq_of_pairwise _ (of_decide_eq_true ok) sorted
    intro a b ha hb ab ba
    have recip := (pairFacts h (qp.mem_iff.mp ha) (perm.mem_iff.mp hb)).2
    simp [ab,ba] at recip
  cases e : orders ids t rev with
  | nil => simp [e] at member
  | cons x xs =>
    have head := only x (by simp [e])
    subst x
    cases xs with
    | nil => rfl
    | cons y ys =>
      have hy := only y (by simp [e])
      subst y
      simp [e] at nd

private theorem tiedOrders {ids t rev i j} (h : coherent ids t rev = true) (hi : i ∈ ids)
    (hj : j ∈ ids) (diff : i ≠ j) (tie : orderAt t rev i j = some .eq) :
    orders ids t rev = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro q hq
  obtain ⟨inPerm,ok⟩ := List.mem_filter.mp hq
  have qp := List.mem_permutations'.mp inPerm
  have ai := qp.mem_iff.mpr hi
  have aj := qp.mem_iff.mpr hj
  have ii := List.idxOf_lt_length_of_mem ai
  have jj := List.idxOf_lt_length_of_mem aj
  have distinct : q.idxOf i ≠ q.idxOf j := fun eqn => diff ((List.idxOf_inj ai).mp eqn)
  have strict := List.pairwise_iff_getElem.mp (of_decide_eq_true ok)
  rcases lt_or_gt_of_ne distinct with before | after
  · have win := strict _ _ ii jj before
    simp [tie] at win
  · have other : orderAt t rev j i = some .eq := by rw [(pairFacts h hi hj).2,tie]; rfl
    have win := strict _ _ jj ii after
    simp [other] at win

private def tiedPair (t : Table) (pair : Nat × Nat) :=
  pair.1 != pair.2 && orderAt t false pair.1 pair.2 == some .eq

/-- Construct the two-geometry outcome from coherent comparisons and nonzero
coordinate readings on permutations of the incident ligands. The order of
the original list has no effect on the existence of a strict ranking. -/
def Outcome.ofCoherence {ids : List Nat} {t : Table} {g : Geometry} (distinct : ids.Nodup)
    (consistent : ∀ rev, coherent ids t rev = true) (shared : SharedTies ids t)
    (physical : ∀ q : List Nat, q.Perm ids → (readback? g q).isSome = true) :
    Outcome g ids t := by
  cases found : (ids.product ids).find? (tiedPair t) with
  | some pair =>
    have inside := List.mem_product.mp (List.mem_of_find?_eq_some found)
    have selected : tiedPair t pair = true := List.find?_some (p := tiedPair t) found
    have ok := Bool.and_eq_true_iff.mp selected
    have diff := bne_iff_ne.mp ok.1
    have initial := eq_of_beq ok.2
    have both (rev : Bool) : orderAt t rev pair.1 pair.2 = some .eq := by
      cases rev
      · exact initial
      · exact (shared _ inside.1 _ inside.2).mp initial
    exact .tied _ _ diff inside (fun rev => ⟨both rev,by rw [(pairFacts (consistent rev) inside.1 inside.2).2,both]; rfl⟩)
      (fun rev => tiedOrders (consistent rev) inside.1 inside.2 diff (both rev))
  | none =>
    have apart (rev : Bool) (i) (hi : i ∈ ids) (j) (hj : j ∈ ids) (diff : i ≠ j) :
        orderAt t rev i j ≠ some .eq := by
      have absent := List.find?_eq_none.mp found (i,j) (List.mem_product.mpr ⟨hi,hj⟩)
      have initial : orderAt t false i j ≠ some .eq := by simpa [tiedPair,diff] using absent
      cases rev
      · exact initial
      · exact fun tie => initial ((shared i hi j hj).mpr tie)
    let a := sortedIds ids t false
    let b := sortedIds ids t true
    have ra := physical a (sortedPerm ids t false)
    have rb := physical b (sortedPerm ids t true)
    have calibrated : (geometric g a b).isSome = true := by
      simp only [geometric,readback_mirror]
      cases ea : readback? g a <;> cases eb : readback? g b <;> simp_all
    exact .assigned a b (uniqueOrder (consistent false) distinct (apart false))
      (uniqueOrder (consistent true) distinct (apart true)) _ (Option.some_get calibrated).symm

private def sameEquality (s : Signs) : Prop := s.1 = .eq ↔ s.2 = .eq

private theorem fromSigns {ids : List Nat} {t : Table}
    (rows : ∀ e ∈ t, sameEquality e.2) : SharedTies ids t := by
  intro i _ j _
  by_cases same : i = j
  · simp [orderAt,same]
  cases w : t.lookup (i,j) with
  | none => simp [orderAt,same,w]
  | some s =>
    obtain ⟨l,r,formed,_⟩ := List.lookup_eq_some_iff.mp w
    have valid := rows ((i,j),s) (by simp [formed])
    simpa [orderAt,same,w,sameEquality] using valid

private theorem initialSigns {m g p i j} (b : Basis m g p i j) : sameEquality b.initial := by
  cases b with
  | atomic _ _ _ _ _ w _ | fourth _ w _ | stereo _ w _ _ => cases w <;> simp [sameEquality,Basis.initial]
  | constitution | tied => exact Iff.rfl

private theorem markedSigns {m g p i j k s} (b : Basis m g p i j)
    (given : b.promoted? k = some s) : sameEquality s := by
  cases b <;> simp only [Basis.promoted?] at given
  all_goals first | (obtain rfl := Option.some.inj given; apply initialSigns) | skip
  rename_i pair fixed
  cases h : pair.atMark? k with
  | none => simp [h] at given
  | some result => simp [h] at given; subst s; exact Iff.rfl

private theorem ordinaryTies {m g p} (rows : List (Row m g p)) (ids : List Nat) :
    SharedTies ids (entries rows) := by
  apply fromSigns
  intro e he
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp he
  exact initialSigns x.basis

private theorem markedTies {m g p k t} (rows : List (Row m g p)) (given : promoted? rows k = some t)
    (ids : List Nat) : SharedTies ids t := by
  apply fromSigns
  induction rows generalizing t with
  | nil => simp [promoted?] at given; simp [given]
  | cons x xs ih =>
    cases hx : x.basis.promoted? k with
    | none => simp [promoted?,List.mapM_cons,hx] at given
    | some s =>
      cases hy : promoted? xs k with
      | none => simp [promoted?,List.mapM_cons,hx,Option.bind_eq_bind] at given hy; simp_all
      | some rest =>
        have eqn : t = ((x.i,x.j),s) :: rest := by
          unfold promoted? at given
          simp only [List.mapM_cons,Option.bind_eq_bind,hx,Option.bind_some] at given
          change ((promoted? xs k).bind (fun ts => some (((x.i,x.j),s) :: ts))) = some t at given
          simpa [hy] using given.symm
        subst t
        intro e he
        rcases List.mem_cons.mp he with rfl | tail
        · exact markedSigns x.basis hx
        · exact ih hy e tail

/-- A single nonzero readback in incident order supplies all physical
readings required by the coherent-order theorem. -/
theorem readback_all_permutations {g : Geometry} {ids : List Nat} (distinct : ids.Nodup)
    (four : ids.length = 4) (calibrated : (readback? g ids).isSome = true)
    (q : List Nat) (perm : q.Perm ids) : (readback? g q).isSome = true := by
  have blank (xs : List Nat) : readback? (fun _ => none) xs = none := by cases xs <;> rfl
  cases found : readback? g q with
  | some _ => rfl
  | none =>
    have bad := LocalizedMarkedMolecularConfiguration.readback_perm_congr
      (second := fun _ => none) q ids (perm.nodup_iff.mpr distinct) (perm.length_eq.trans four)
      perm.symm (found.trans (blank q).symm)
    rw [blank] at bad
    simp [bad] at calibrated

/-- A complete unmarked frame below the promotion threshold has a structural
or geometric verdict. Coherence is already a molecular-frame field. -/
def Ordinary.ofComplete {m g p} (f : MolecularFrame m g p)
    (few : (marks f.ids (entries f.rows)).length < 3)
    (physical : (readback? g f.ids).isSome = true) : Ordinary f :=
  ⟨few,.ofCoherence f.distinct f.ordinary (ordinaryTies _ _) (readback_all_permutations f.distinct f.four physical)⟩

/-- Each eligible mark needs molecular comparison results, coherence and
calibrated coordinates. Produces all trials in the exact eligible order. -/
def Population.ofComplete {m g p} (f : Frame m g p)
    (covered : ∀ k ∈ marks f.ids (entries f.rows), (promoted? f.rows k).isSome = true)
    (consistent : ∀ k ∈ marks f.ids (entries f.rows), ∀ t, promoted? f.rows k = some t →
      ∀ rev, coherent f.ids t rev = true)
    (physical : (readback? g f.ids).isSome = true) : Population m g p := by
  let ids := marks f.ids (entries f.rows)
  let atMark (k : {n // n ∈ ids}) : Trial f := by
    let t := (promoted? f.rows k.val).get (covered _ k.property)
    have found : promoted? f.rows k.val = some t := (Option.some_get _).symm
    have agrees := consistent _ k.property t found
    exact ⟨k.val,t,found,agrees,.ofCoherence f.distinct agrees (markedTies f.rows found _) (readback_all_permutations f.distinct f.four physical)⟩
  exact ⟨f,ids.attach.map atMark,by simp [List.map_map,Function.comp_def,atMark,ids]⟩

/-- Every complete four-ligand frame produces either its ordinary outcome
or an exhaustive population over precisely this same molecular frame.
Marked tables are required only above the promotion threshold. -/
def MolecularFrame.resolve {m g p} (f : MolecularFrame m g p)
    (physical : (readback? g f.ids).isSome = true)
    (covered : 3 ≤ (marks f.ids (entries f.rows)).length →
      ∀ k ∈ marks f.ids (entries f.rows), (promoted? f.rows k).isSome = true)
    (consistent : 3 ≤ (marks f.ids (entries f.rows)).length →
      ∀ k ∈ marks f.ids (entries f.rows), ∀ t, promoted? f.rows k = some t →
      ∀ rev, coherent f.ids t rev = true) :
    Ordinary f ⊕ {s : Population m g p // s.frame.toMolecularFrame = f} := by
  if few : (marks f.ids (entries f.rows)).length < 3 then
    exact .inl (Ordinary.ofComplete f few physical)
  else
    have threshold := Nat.le_of_not_gt few
    have bound : (marks f.ids (entries f.rows)).length ≤ 4 :=
      (List.length_filter_le _ _).trans (Nat.le_of_eq f.four)
    have eligible : (marks f.ids (entries f.rows)).length ∈ [3,4] := by simp; omega
    let frame : Frame m g p := ⟨f,eligible⟩
    exact .inr ⟨Population.ofComplete frame (covered threshold) (consistent threshold) physical,rfl⟩

/-- Check every marked molecular comparison and both coherence conditions. -/
private def markedCoverage {m g p} (f : MolecularFrame m g p) :=
  (marks f.ids (entries f.rows)).all fun k =>
    (promoted? f.rows k).any fun t => coherent f.ids t false && coherent f.ids t true

private theorem markedCoverage_iff {m g p} (f : MolecularFrame m g p) :
    markedCoverage f = true ↔ ∀ k ∈ marks f.ids (entries f.rows),
      ∃ t, promoted? f.rows k = some t ∧ ∀ rev, coherent f.ids t rev = true := by
  unfold markedCoverage
  rw [List.all_eq_true]
  constructor
  · intro checked k hk
    have hit := checked k hk
    cases result : promoted? f.rows k with
    | none => simp [result] at hit
    | some t =>
      have both := Bool.and_eq_true_iff.mp (show (coherent f.ids t false && coherent f.ids t true) = true by
        simpa [result] using hit)
      exact ⟨t,rfl,fun rev => by cases rev <;> first | exact both.1 | exact both.2⟩
  · intro checked k hk
    obtain ⟨t,found,cons⟩ := checked k hk
    simp [found,cons]

/-- Executable decision after the unmarked molecular frame has been assembled. -/
def MolecularFrame.resolve? {m g p} (f : MolecularFrame m g p) :
    Option (Ordinary f ⊕ {s : Population m g p // s.frame.toMolecularFrame = f}) := do
  if cal : (readback? g f.ids).isSome = true then
    if few : (marks f.ids (entries f.rows)).length < 3 then
      return .inl (Ordinary.ofComplete f few cal)
    if ready : markedCoverage f = true then
      have hit := (markedCoverage_iff f).mp ready
      return f.resolve cal (fun _ k hk => by obtain ⟨t,s,_⟩ := hit k hk; simp [s])
        (fun _ k hk t found => by obtain ⟨_,s,cons⟩ := hit k hk; cases s.symm.trans found; exact cons)
  none

/-- All remaining frame-level failure conditions are exposed as molecular
comparison, coherence and coordinate tests, prior to signed aggregation. -/
theorem MolecularFrame.resolve?_isSome_iff {m g p} (f : MolecularFrame m g p) :
    f.resolve?.isSome = true ↔
      (readback? g f.ids).isSome = true ∧ ((marks f.ids (entries f.rows)).length < 3 ∨
      ∀ k ∈ marks f.ids (entries f.rows), ∃ t, promoted? f.rows k = some t ∧
        ∀ rev, coherent f.ids t rev = true) := by
  rw [← markedCoverage_iff]
  by_cases cal : (readback? g f.ids).isSome = true <;>
    by_cases few : (marks f.ids (entries f.rows)).length < 3 <;>
    by_cases ready : markedCoverage f = true <;> simp_all [MolecularFrame.resolve?]
  split <;> rfl

/-- The outer option records comparison and coordinate coverage. A completed
ordinary tie or a zero signed promotion balance gives an empty inner label. -/
def MolecularFrame.signedOutcome? {m g p} (f : MolecularFrame m g p) :=
  f.resolve?.map fun result => match result with
    | .inl ordinary => ordinary.outcome.reading?.bind Reading.label
    | .inr population => population.val.signedDescriptor

theorem MolecularFrame.signedOutcome?_isSome_iff {m g p} (f : MolecularFrame m g p) :
    f.signedOutcome?.isSome = true ↔
      (readback? g f.ids).isSome = true ∧ ((marks f.ids (entries f.rows)).length < 3 ∨
      ∀ k ∈ marks f.ids (entries f.rows), ∃ t, promoted? f.rows k = some t ∧
        ∀ rev, coherent f.ids t rev = true) := by
  simpa [MolecularFrame.signedOutcome?] using f.resolve?_isSome_iff

/-- Exact promoted outcome without any assumption of consensus among trials. -/
theorem MolecularFrame.signedOutcome?_of_population {m g p} (f : MolecularFrame m g p) {s}
    (selected : f.resolve? = some (.inr s)) :
    f.signedOutcome? = some ((survivingHand
      (LocalizedChemicalRingPromotionAggregation.readingBalance (s.val.hands false))).map fun hand =>
        if f.reversals % 2 = 0 then .chiral hand else .pseudoasymmetric (pseudoRSOfRS hand)) := by
  simp only [MolecularFrame.signedOutcome?,selected,Option.map_some,s.val.signedDescriptor_eq]
  rw [show s.val.frame.reversals = f.reversals from congrArg MolecularFrame.reversals s.property]

end TetraStereo.Engine.RingChemicalPriority.ReferenceFrame

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Outcome.ofCoherence

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Ordinary.ofComplete
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Population.ofComplete
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.MolecularFrame.resolve
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.MolecularFrame.resolve?_isSome_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.MolecularFrame.signedOutcome?_isSome_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.MolecularFrame.signedOutcome?_of_population

namespace TetraStereo.Engine.RingChemicalPriority.ReferenceFrame
open OneCenter LocalizedGenericMarkedRecalculation Recursive
open ReferenceDerivation (Certificate Derives)
open InventoryPriority (Entries)

/-- One signed publication table for the complete incident frame. Each
address has at most one signed value, every value is derived against this
same table, and every input consumed by the frame has an exact lookup. -/
structure DescendantFrame (m : RawMolecule) (g : Geometry) (p : List Nat) (depth : Nat) where
  published : Entries
  unique : (published.map Prod.fst).Nodup
  proper : ∀ x ∈ published, p <+: x.1 ∧ p.length < x.1.length
  issued : ∀ x ∈ published, Derives m g published x.1 x.2
  frame : MolecularFrame m g p
  constructed : molecularFrame? m g p depth (ReferenceDerivation.armFrom published) = some frame
  bound : ∀ x ∈ frame.inputs, published.lookup x.1 = some x.2

theorem DescendantFrame.input_derived {m g p depth} (f : DescendantFrame m g p depth) {x}
    (used : x ∈ f.frame.inputs) : f.published.lookup x.1 = some x.2 ∧ p <+: x.1 ∧
      p.length < x.1.length ∧ Derives m g f.published x.1 x.2 := by
  have hit := f.bound _ used
  obtain ⟨l,r,formed,_⟩ := List.lookup_eq_some_iff.mp hit
  have member : x ∈ f.published := by rw [formed]; simp
  exact ⟨hit,(f.proper _ member).1,(f.proper _ member).2,f.issued _ member⟩

theorem DescendantFrame.row_input {m g p depth} (f : DescendantFrame m g p depth) {row : Row m g p} {x}
    (inside : row ∈ f.frame.rows) (used : x ∈ row.basis.inputs) :
    f.published.lookup x.1 = some x.2 ∧ Derives m g f.published x.1 x.2 := by
  have facts := f.input_derived (List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨row,inside,used⟩))
  exact ⟨facts.1,facts.2.2.2⟩

private abbrev Child (m : RawMolecule) (g : Geometry) := (q : List Nat) × Certificate m g q

private def childEntries {m g} (r : Child m g) : Entries :=
  (r.1,r.2.verdict) :: r.2.published

private def promotedDescendants (m : RawMolecule) (p : List Nat) (focus : RawMolecule.CanonicalBranchNode) :=
  (RingAuxiliaryInventory.promotionPaths m focus).eraseDups.filter fun q => decide (p <+: q ∧ p.length < q.length)

private def DescendantFrame.assemble? {m g depth} (p : List Nat) (paths : List (List Nat))
    (readChild : (q : List Nat) → Option (Certificate m g q)) : Option (DescendantFrame m g p depth) := do
  let children := paths.filterMap fun q => (readChild q).map fun c => (⟨q,c⟩ : Child m g)
  let env := (children.flatMap childEntries).dedup
  if unique : (env.map Prod.fst).Nodup then
    if proper : ∀ x ∈ env, p <+: x.1 ∧ p.length < x.1.length then
      let ⟨frame,built⟩ ← (molecularFrame? m g p depth (ReferenceDerivation.armFrom env)).attach
      if bound : ∀ x ∈ frame.inputs, env.lookup x.1 = some x.2 then
        have issued : ∀ x ∈ env, Derives m g env x.1 x.2 := by
          intro x hx
          obtain ⟨child,inside,used⟩ := List.mem_flatMap.mp (List.mem_dedup.mp hx)
          have sub : child.2.published ⊆ env := fun y hy =>
            List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨child,inside,List.mem_cons_of_mem _ hy⟩)
          rcases List.mem_cons.mp used with rfl | deep
          · exact child.2.derived.weaken sub
          · exact (child.2.issued x deep).weaken sub
        return ⟨env,unique,proper,issued,frame,built,bound⟩
  none

/-- Assemble a new parent from cached or independently derived children.
Reads only proper promotion paths and never requires a verdict for the focus. -/
def DescendantFrame.fromCache? {m g depth} (cache : ReferenceDerivation.Cache m g depth)
    (p : List Nat) : Option (DescendantFrame m g p depth) := do
  let focus ← occurrence? m p
  DescendantFrame.assemble? p (promotedDescendants m p focus) fun q => cache.read q

/-- Build the descendant cache once in bottom-up order before it is used
to assemble the parent frame. Certified child refusals remain signed inputs. -/
def DescendantFrame.fromMolecule? (m : RawMolecule) (g : Geometry) (p : List Nat) (depth : Nat) :
    Option (DescendantFrame m g p depth) := do
  let focus ← occurrence? m p
  let paths := promotedDescendants m p focus
  let cache := ReferenceDerivation.cache m g depth paths
  DescendantFrame.assemble? p paths fun q => cache.read q

/-- The cache is an optimization only: even a pre-populated cache gives
exactly the same dependent frame as a fresh bottom-up calculation. -/
theorem DescendantFrame.fromCache?_eq_fromMolecule? {m g depth} (cache : ReferenceDerivation.Cache m g depth)
    (p : List Nat) : DescendantFrame.fromCache? cache p = DescendantFrame.fromMolecule? m g p depth := by
  unfold DescendantFrame.fromCache? DescendantFrame.fromMolecule?
  cases h : occurrence? m p with
  | none => rfl
  | some focus =>
    let paths := promotedDescendants m p focus
    apply congrArg (DescendantFrame.assemble? (depth := depth) p paths)
    funext q
    exact (ReferenceDerivation.Cache.read_exact q cache).trans (ReferenceDerivation.Cache.read_exact q _).symm

/-- End-to-end signed outcome using child certificates and the raw molecule.
The outer option retains a failure to cover comparisons or coordinates. -/
def signedAt? (m : RawMolecule) (g : Geometry) (p : List Nat) (depth : Nat) :=
  (DescendantFrame.fromMolecule? m g p depth).bind fun f => f.frame.signedOutcome?

theorem signedAt?_iff {m g p depth v} :
    signedAt? m g p depth = some v ↔ ∃ f : DescendantFrame m g p depth,
      DescendantFrame.fromMolecule? m g p depth = some f ∧ f.frame.signedOutcome? = some v :=
  Option.bind_eq_some_iff

/-- Every completed signed molecular outcome has an exact occurrence table
that justifies all signed inputs to every one of its molecular comparisons. -/
theorem signedAt?_inputs {m g p depth v} (result : signedAt? m g p depth = some v) :
    ∃ f : DescendantFrame m g p depth, f.frame.signedOutcome? = some v ∧
      ∀ row ∈ f.frame.rows, ∀ x ∈ row.basis.inputs, f.published.lookup x.1 = some x.2 ∧
        Derives m g f.published x.1 x.2 := by
  obtain ⟨f,_,actual⟩ := signedAt?_iff.mp result
  exact ⟨f,actual,fun _ hr _ hx => f.row_input hr hx⟩

end TetraStereo.Engine.RingChemicalPriority.ReferenceFrame

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.DescendantFrame.input_derived
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.DescendantFrame.fromMolecule?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.signedAt?_inputs
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.DescendantFrame.fromCache?_eq_fromMolecule?
