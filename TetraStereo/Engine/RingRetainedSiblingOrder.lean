import TetraStereo.Engine.RingActivePairSoundness

set_option autoImplicit false

namespace TetraStereo.Engine.RingRetainedSiblingOrder

open OneCenter CertifiedLocalizedCIPInput RingRetainedConstitution
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm AtomicOrder)

private abbrev Layers := List (List (OfficialSparseEntry DeclarativeCIP.ExactAtomicNumber))

private def compareLayers := OfficialRuleMajorKey.compareSparseLayers
  ExactOfficialRuleMajorKey.compareExactAtomicNumber

private instance : Std.TransCmp compareLayers := by
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  letI := ExactOfficialRuleMajorKey.compareExactAtomicNumber_transCmp
  unfold compareLayers OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareSparseEntry
  infer_instance

private def layers (i : Input) (a : Arm i) : Layers :=
  ExactOfficialRuleMajorKey.observedRule1aLayers
    i.certified.certified.input.molecule.semanticExactOfficialRule1aObservation
    (key i.certified a).sourceNodes

/-- Only the first of the addressed constitutional comparisons orders siblings. -/
def compare1a (i : Input) (a b : Arm i) := compareLayers (layers i a) (layers i b)

theorem trace_head (i : Input) (a b : Arm i) :
    (trace i.certified a b).head? = some ⟨.atomicNumber,compare1a i a b⟩ := rfl

/-- Exchanging these occurrences in a queue can only exchange two terminal visits of the
same atomic number. The retained reader checks both publications for absence at the leaves. -/
def SameLeaves (i : Input) (a b : Arm i) : Prop :=
  i.certified.executableLocalizedRerootChildren a = [] ∧
  i.certified.executableLocalizedRerootChildren b = [] ∧ RingActivePairs.z? i a = RingActivePairs.z? i b

instance {i a b} : Decidable (SameLeaves i a b) := by unfold SameLeaves; infer_instance

/-- A strict order compares the actual children of this directed occurrence.
The incoming edge has already been removed by the retained carrier. -/
inductive Order (i : Input) (q : Arm i) (children : List (Arm i)) : Prop where
  | atomic (order : AtomicOrder i q children)
  | retained (allChildren : children.Perm (i.certified.executableLocalizedRerootChildren q))
      (higher : children.Pairwise fun a b => compare1a i a b = .gt)

  | molecular (allChildren : children.Perm (i.certified.executableLocalizedRerootChildren q))
      (higher : children.Pairwise fun a b => ∃ ka kb,
        RingRetainedChemicalTrace.key? i a = some ka ∧ RingRetainedChemicalTrace.key? i b = some kb ∧
          (RingRetainedChemicalTrace.compareKeys ka kb = .gt ∨
            (RingRetainedChemicalTrace.compareKeys ka kb = .eq ∧ SameLeaves i a b)))

theorem Order.complete {i q xs} (h : Order i q xs) :
    xs.Perm (i.certified.executableLocalizedRerootChildren q) := by
  cases h with
  | atomic w => exact w.complete
  | retained p _ | molecular p _ => exact p

/-- Each admitted branch is entered from the actual parent and has a complete
addressed constitutional expansion even when the parent's own direction is inward. -/
theorem Order.branch {i q xs} (h : Order i q xs) {a} (ha : a ∈ xs) :
    a.previous? = some q.occurrence ∧ i.certified.LocalizedRerootCursorValid a ∧
      Expansion i.certified a (key i.certified a) ∧ (key i.certified a).complete = true := by
  have frame := i.certified.executableLocalizedRerootChildren_declarative q
  have mem := h.complete.mem_iff.mp ha
  have valid := i.certified.localizedRerootChild_valid q a _ frame mem
  exact ⟨frame.2 a mem,valid,key_source i.certified a valid⟩

/-- Project the retained comparison onto the original molecular source nodes.
Both expansions carry their original-ring duplicate distances and incoming direction. -/
theorem Order.addressed {i q xs} (h : Order i q xs) {a b} (ha : a ∈ xs) (hb : b ∈ xs) :
    ∃ ka kb : Key i.certified, Expansion i.certified a ka ∧ Expansion i.certified b kb ∧
      ka.complete = true ∧ kb.complete = true ∧ trace i.certified a b =
        ExactOfficialRuleMajorKey.compareAddressedSourceTrace i.certified.moleculeGraph ka.sourceNodes kb.sourceNodes ∧
      cipTraceOutcome (trace i.certified a b) = ExactOfficialRuleMajorKey.compare i.certified.moleculeGraph ka kb :=
  trace_source i.certified a b (h.branch ha).2.1 (h.branch hb).2.1

private abbrev Row (i : Input) := Arm i × Layers

private def rows (i : Input) (q : Arm i) :=
  ((i.certified.executableLocalizedRerootChildren q).map
    (fun a => (a,layers i a))).mergeSort (fun a b => (compareLayers a.2 b.2).isGE)

private theorem rows_perm (i : Input) (q : Arm i) :
    (rows i q).Perm ((i.certified.executableLocalizedRerootChildren q).map
      (fun a => (a,layers i a))) := List.mergeSort_perm ..

private theorem row_eq (i : Input) (q : Arm i) (a : Row i) (mem : a ∈ rows i q) :
    layers i a.1 = a.2 := by
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp ((rows_perm i q).mem_iff.mp mem)
  rfl

private def Strict (i : Input) (rs : List (Row i)) := rs.Pairwise fun a b => compareLayers a.2 b.2 = .gt

private instance {i rs} : Decidable (Strict i rs) := by unfold Strict; infer_instance

private theorem of_strict {i q} (strict : Strict i (rows i q)) :
    Order i q ((rows i q).map Prod.fst) := by
  apply Order.retained
  · simpa [List.map_map,Function.comp_def] using (rows_perm i q).map Prod.fst
  · rw [List.pairwise_map]
    apply strict.imp_of_mem
    intro a b ha hb h
    simpa only [compare1a,row_eq i q a ha,row_eq i q b hb] using h

/-- Preserve the inexpensive atomic order when it succeeds. Otherwise carry one
materialized Rule 1a projection per child through sorting and the strictness check. -/
def children? (i : Input) (q : Arm i) : Option {xs : List (Arm i) // Order i q xs} :=
  match h : RingActivePairs.children? i q with
  | some es => some ⟨es.map Prod.fst,.atomic (RingActivePairs.children_source h)⟩
  | none =>
    let rs := rows i q
    if strict : Strict i rs then some ⟨rs.map Prod.fst,of_strict strict⟩ else none

/-- Every pair differs under Rule 1a in the original, unsorted molecular frame. -/
def Separated (i : Input) (q : Arm i) :=
  (i.certified.executableLocalizedRerootChildren q).Pairwise fun a b => compare1a i a b ≠ .eq

private theorem strict_iff (i : Input) (q : Arm i) : Strict i (rows i q) ↔ Separated i q := by
  have oriented {a b : Row i} (ne : compareLayers a.2 b.2 ≠ .eq) : compareLayers b.2 a.2 ≠ .eq :=
    fun e => ne (Std.OrientedCmp.eq_symm e)
  have perm := (rows_perm i q).pairwise_iff (R := fun (a b : Row i) => compareLayers a.2 b.2 ≠ .eq) (fun h => oriented h)
  have raw : Separated i q ↔ (rows i q).Pairwise (fun a b => compareLayers a.2 b.2 ≠ .eq) := by
    rw [perm,List.pairwise_map]
    rfl
  have trans (a b c : Row i) : (compareLayers a.2 b.2).isGE → (compareLayers b.2 c.2).isGE →
      (compareLayers a.2 c.2).isGE := Std.TransCmp.isGE_trans
  have total (a b : Row i) : ((compareLayers a.2 b.2).isGE || (compareLayers b.2 a.2).isGE) = true := by
    rw [Std.OrientedCmp.eq_swap (cmp := compareLayers) (a := a.2) (b := b.2)]
    cases compareLayers b.2 a.2 <;> rfl
  have descending : (rows i q).Pairwise (fun a b => (compareLayers a.2 b.2).isGE = true) :=
    List.pairwise_mergeSort trans total _
  rw [raw]
  constructor
  · exact fun h => h.imp fun win => by rw [win]; decide
  · intro untied
    apply (List.pairwise_and_iff.mpr ⟨descending,untied⟩).imp
    intro a b h
    cases eqn : compareLayers a.2 b.2 <;> simp_all

/-- A strict Rule 1a sibling sequence is uniquely determined among all permutations
that obey the molecular Rule 1a precedence relation. -/
theorem unique {i : Input} {xs ys : List (Arm i)} (perm : xs.Perm ys)
    (strict : xs.Pairwise fun a b => compare1a i a b = .gt)
    (legal : ys.Pairwise fun a b => compare1a i b a ≠ .gt) : xs = ys := by
  have flip (a b : Arm i) : compare1a i a b = (compare1a i b a).swap :=
    Std.OrientedCmp.eq_swap (cmp := compareLayers)
  have untied : ys.Pairwise (fun a b => compare1a i a b ≠ .eq) := by
    apply (perm.pairwise_iff (R := fun a b => compare1a i a b ≠ .eq) (fun {a b} ne h =>
      ne (by rw [flip a b,h]; rfl))).mp
    exact strict.imp fun h => by rw [h]; decide
  have ysStrict : ys.Pairwise (fun a b => compare1a i a b = .gt) := by
    apply (List.pairwise_and_iff.mpr ⟨legal,untied⟩).imp
    intro a b h
    rw [flip a b] at h ⊢
    cases e : compare1a i b a with
    | lt => rfl
    | eq => exact False.elim (h.2 (by rw [e]; rfl))
    | gt => exact False.elim (h.1 e)
  exact List.Perm.eq_of_pairwise (fun a b _ _ ab ba => by rw [flip a b,ba] at ab; contradiction)
    strict ysStrict perm

/-- A failure of both tests localizes an actual Rule 1a equality in the
original frame. Every Rule 1a-separated sibling frame is covered. -/
theorem missing_iff (i : Input) (q : Arm i) :
    (children? i q).isNone = true ↔ (RingActivePairs.children? i q).isNone = true ∧ ¬Separated i q := by
  unfold children?
  split
  · rename_i es h
    simp [h]
  · rename_i h
    dsimp only
    split
    · rename_i yes
      have sep := (strict_iff i q).mp yes
      simp [h,sep]
    · rename_i no
      have tied := mt (strict_iff i q).mpr no
      simp [h,tied]

private abbrev ChemicalRow (i : Input) := (a : Arm i) ×
  {k : RingRetainedChemicalTrace.Key // RingRetainedChemicalTrace.key? i a = some k}

private def readRow (i : Input) (a : Arm i) : Option (ChemicalRow i) :=
  (RingRetainedChemicalTrace.key? i a).attach.map (Sigma.mk a)

private theorem row_origins {i : Input} {xs : List (Arm i)} {rs : List (ChemicalRow i)}
    (hit : xs.mapM (readRow i) = some rs) : rs.map Sigma.fst = xs := by
  induction xs generalizing rs with
  | nil => obtain rfl := Option.some.inj hit; rfl
  | cons a xs ih =>
    rw [List.mapM_cons] at hit
    obtain ⟨r,hr,k⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨tail,ht,out⟩ := Option.bind_eq_some_iff.mp k
    obtain rfl := Option.some.inj out
    obtain ⟨v,_,rfl⟩ := Option.map_eq_some_iff.mp hr
    simpa using ih ht

/-- Resolve a tied atomic number using complete molecular comparisons of the actual
retained branches. Equal real nodes never separate solely because one points inward. -/
def chemicalChildren? (i : Input) (q : Arm i) : Option {xs : List (Arm i) // Order i q xs} := do
  if let some ⟨es,h⟩ := (RingActivePairs.children? i q).attach then
    return ⟨es.map Prod.fst,.atomic (RingActivePairs.children_source h)⟩
  let ⟨rs,hr⟩ ← ((i.certified.executableLocalizedRerootChildren q).mapM (readRow i)).attach
  let cmp (a b : ChemicalRow i) := RingRetainedChemicalTrace.compareKeys a.2.val b.2.val
  let sorted := rs.mergeSort fun a b => (cmp a b).isGE
  if strict : sorted.Pairwise (fun a b => cmp a b = .gt ∨ (cmp a b = .eq ∧ SameLeaves i a.1 b.1)) then
    have perm : sorted.Perm rs := List.mergeSort_perm ..
    have allChildren := (row_origins hr) ▸ perm.map Sigma.fst
    return ⟨sorted.map Sigma.fst,.molecular allChildren (List.pairwise_map.mpr
      (strict.imp fun {a b} h => ⟨a.2.val,b.2.val,a.2.property,b.2.property,h⟩))⟩
  none

end TetraStereo.Engine.RingRetainedSiblingOrder

assert_kernel_only TetraStereo.Engine.RingRetainedSiblingOrder.trace_head
assert_kernel_only TetraStereo.Engine.RingRetainedSiblingOrder.unique
assert_kernel_only TetraStereo.Engine.RingRetainedSiblingOrder.Order.branch
assert_kernel_only TetraStereo.Engine.RingRetainedSiblingOrder.Order.addressed
assert_kernel_only TetraStereo.Engine.RingRetainedSiblingOrder.children?
assert_kernel_only TetraStereo.Engine.RingRetainedSiblingOrder.missing_iff

assert_kernel_only TetraStereo.Engine.RingRetainedSiblingOrder.chemicalChildren?
