import TetraStereo.Engine.LocalizedChemicalRingPublic
import TetraStereo.OneCenter.AuthoritativeLocalizedRuleMajorAnalysis
import TetraStereo.OneCenter.LocalizedAllRootUniversalDepth
import TetraStereo.OneCenter.LocalizedConstitutionalExecutable
import TetraStereo.OneCenter.LocalizedChemicalRingRootSliceCache
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.Engine.RingRetainedConstitution
open OneCenter CertifiedLocalizedCIPInput

abbrev Key (i : CertifiedLocalizedCIPInput) := ExactOfficialRuleMajorKey i.Atom
abbrev Cursor (i : CertifiedLocalizedCIPInput) (d : Nat) := i.LocalizedRerootCursor d

/-- Recursive molecular specification. Every original carrier neighbor other than the incoming
edge occurs once in its declared frame. Duplicate nodes remain terminal. Source coordinates
are assembled by a descending permutation of all child expansions. The underlying atoms,
provenance and Rule 1b distances come from the original-root node at each retained address. -/
inductive Expansion (i : CertifiedLocalizedCIPInput) {d : Nat} : Cursor i d → Key i → Prop where
  | node (q : Cursor i d) (children : List (Cursor i d)) (sub : Cursor i d → Key i)
      (ordered : List (Key i))
      (frame : i.DeclarativeLocalizedRerootChildren q children)
      (branches : ∀ child ∈ children, Expansion i child (sub child))
      (perm : ordered.Perm (children.map sub)) (descending : ExactOfficialRuleMajorKey.Descending i.moleculeGraph ordered) :
      Expansion i q (ExactOfficialRuleMajorKey.assemble
        (MoleculeGraph.exactOfficialRuleMajorRootKey q.occurrence.val.node true) ordered)

private def observed (i : CertifiedLocalizedCIPInput) (a b : Key i) :=
  ExactOfficialRuleMajorKey.compareObserved i.moleculeGraph i.certified.input.molecule.semanticExactOfficialRule1aObservation a b

private theorem observed_eq (i : CertifiedLocalizedCIPInput) (a b : Key i) :
    observed i a b = ExactOfficialRuleMajorKey.compare i.moleculeGraph a b :=
  ExactOfficialRuleMajorKey.compareObserved_eq_exact _ _ i.executableExactOfficialRule1aObservation_correct a b

private def rank (i : CertifiedLocalizedCIPInput) (xs : List (Key i)) :=
  xs.mergeSort fun a b => (observed i a b).isGE

private theorem rank_descending (i : CertifiedLocalizedCIPInput) (xs : List (Key i)) :
    ExactOfficialRuleMajorKey.Descending i.moleculeGraph (rank i xs) := by
  let cmp := ExactOfficialRuleMajorKey.compare i.moleculeGraph
  letI : Std.TransCmp cmp := ExactOfficialRuleMajorKey.compare_transCmp _
  have trans (a b c : Key i) : (cmp a b).isGE → (cmp b c).isGE → (cmp a c).isGE :=
    Std.TransCmp.isGE_trans
  have total (a b : Key i) : ((cmp a b).isGE || (cmp b a).isGE) = true := by
    rw [Std.OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b)]
    cases cmp b a <;> rfl
  unfold rank ExactOfficialRuleMajorKey.Descending
  simp only [observed_eq]
  apply (List.pairwise_mergeSort trans total xs).imp
  intro a b ge lower
  change cmp a b = .lt at lower
  simp [lower] at ge

/-- The zero-budget value is an incomplete prefix. Only ranks exceeding the cursor budget
are exported as complete keys. -/
private def build (i : CertifiedLocalizedCIPInput) {d : Nat} : Nat → Cursor i d → Key i
  | 0,q => MoleculeGraph.exactOfficialRuleMajorRootKey q.occurrence.val.node false
  | n+1,q =>
    let children := i.executableLocalizedRerootChildren q
    ExactOfficialRuleMajorKey.assemble (MoleculeGraph.exactOfficialRuleMajorRootKey q.occurrence.val.node true)
      (rank i (children.map (build i n)))

private theorem build_source (i : CertifiedLocalizedCIPInput) {d : Nat} :
    ∀ n (q : Cursor i d), i.LocalizedRerootCursorValid q → i.localizedRerootCursorBudget q < n →
      Expansion i q (build i n q) ∧ (build i n q).complete = true
  | 0,_,_,bounded => by omega
  | n+1,q,valid,bounded => by
    let children := i.executableLocalizedRerootChildren q
    have frame := i.executableLocalizedRerootChildren_declarative q
    have child (x : Cursor i d) (mem : x ∈ children) :=
      build_source i n x (i.localizedRerootChild_valid q x children frame mem)
        (by have h := i.localizedRerootChild_budget_lt q x children valid frame mem; omega)
    have perm : (rank i (children.map (build i n))).Perm (children.map (build i n)) := List.mergeSort_perm ..
    refine ⟨Expansion.node q children (build i n) _ frame (fun x hx => (child x hx).1) perm (rank_descending i _),?_⟩
    apply List.all_eq_true.mpr
    intro k present
    obtain ⟨x,mem,rfl⟩ := List.mem_map.mp (perm.mem_iff.mp present)
    exact (child x mem).2

/-- Retained key at the uniform structural traversal bound. -/
def key (i : CertifiedLocalizedCIPInput) {d : Nat} (q : Cursor i d) : Key i := build i (2*(d+1)+1) q

/-- Construct a full retained key with one materialized occurrence carrier for every
expansion in this arm. The order of the parent-facing and outward edges is preserved. -/
private def buildCached (i : CertifiedLocalizedCIPInput) {d : Nat} (reader : i.LocalizedRerootChildReader d) :
    Nat → Cursor i d → Key i
  | 0,q => MoleculeGraph.exactOfficialRuleMajorRootKey q.occurrence.val.node false
  | n+1,q =>
    let children := (reader.readChildren q).getD []
    ExactOfficialRuleMajorKey.assemble (MoleculeGraph.exactOfficialRuleMajorRootKey q.occurrence.val.node true)
      (rank i (children.map (buildCached i reader n)))

private theorem cached_exact (i : CertifiedLocalizedCIPInput) {d : Nat} (reader : i.LocalizedRerootChildReader d) (n : Nat) :
    buildCached i reader n = build i n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext q
    simp only [buildCached,reader.readChildren_eq,executableLocalizedRerootChildren?,Option.getD_some,ih,build]

def cachedKey (i : CertifiedLocalizedCIPInput) {d : Nat} (q : Cursor i d) : Key i :=
  let slice := localizedRerootRootSliceCache (i.localizedRerootCarrierCache d) q.occurrence.val.root
  buildCached i slice.reader (2*(d+1)+1) q

@[csimp] theorem key_cached : @key = @cachedKey := by
  funext i d q
  exact congrFun (cached_exact i (localizedRerootRootSliceCache (i.localizedRerootCarrierCache d) q.occurrence.val.root).reader (2*(d+1)+1)).symm q

theorem key_source (i : CertifiedLocalizedCIPInput) {d : Nat} (q : Cursor i d) (valid : i.LocalizedRerootCursorValid q) :
    Expansion i q (key i q) ∧ (key i q).complete = true :=
  build_source i _ q valid (Nat.lt_succ_of_le (i.localizedRerootCursorBudget_le_twice q))

private theorem build_stable (i : CertifiedLocalizedCIPInput) {d : Nat} :
    ∀ n m (q : Cursor i d), i.LocalizedRerootCursorValid q → i.localizedRerootCursorBudget q < n →
      i.localizedRerootCursorBudget q < m → build i n q = build i m q
  | 0,_,_,_,hn,_ => by omega
  | _+1,0,_,_,_,hm => by omega
  | n+1,m+1,q,valid,hn,hm => by
      have frame := i.executableLocalizedRerootChildren_declarative q
      have children : (i.executableLocalizedRerootChildren q).map (build i n) =
          (i.executableLocalizedRerootChildren q).map (build i m) := by
        apply List.map_congr_left
        intro x hx
        have smaller := i.localizedRerootChild_budget_lt q x _ valid frame hx
        exact build_stable i n m x (i.localizedRerootChild_valid q x _ frame hx) (by omega) (by omega)
      simp only [build, children]

/-- A request that does not cover the cursor budget leaves its result open. -/
def keyAt? (i : CertifiedLocalizedCIPInput) {d : Nat} (n : Nat) (q : Cursor i d) : Option (Key i) :=
  if i.localizedRerootCursorBudget q < n then some (build i n q) else none

/-- Every sufficient bound returns the same addressed key, including the ordering of tied siblings. -/
theorem key_stable (i : CertifiedLocalizedCIPInput) {d : Nat} (n : Nat) (q : Cursor i d)
    (valid : i.LocalizedRerootCursorValid q) (covered : i.localizedRerootCursorBudget q < n) :
    keyAt? i n q = some (key i q) := by
  rw [keyAt?,if_pos covered]
  exact congrArg some (build_stable i _ _ q valid covered (Nat.lt_succ_of_le (i.localizedRerootCursorBudget_le_twice q)))

/-- Exact constitutional trace on the two retained occurrences. -/
def trace (i : CertifiedLocalizedCIPInput) {d : Nat} (a b : Cursor i d) :=
  ExactOfficialRuleMajorKey.compareTraceObserved i.moleculeGraph i.certified.input.molecule.semanticExactOfficialRule1aObservation
    (key i a) (key i b)

theorem trace_source (i : CertifiedLocalizedCIPInput) {d : Nat} (a b : Cursor i d)
    (av : i.LocalizedRerootCursorValid a) (bv : i.LocalizedRerootCursorValid b) :
    ∃ l r : Key i, Expansion i a l ∧ Expansion i b r ∧ l.complete = true ∧ r.complete = true ∧
      trace i a b = ExactOfficialRuleMajorKey.compareAddressedSourceTrace i.moleculeGraph l.sourceNodes r.sourceNodes ∧
      cipTraceOutcome (trace i a b) = ExactOfficialRuleMajorKey.compare i.moleculeGraph l r := by
  obtain ⟨la,lc⟩ := key_source i a av
  obtain ⟨rb,rc⟩ := key_source i b bv
  refine ⟨key i a,key i b,la,rb,lc,rc,?_,?_⟩ <;>
    rw [trace, ExactOfficialRuleMajorKey.compareTraceObserved_eq_exact _ _ i.executableExactOfficialRule1aObservation_correct]
  · rfl
  · exact ExactOfficialRuleMajorKey.compareTrace_outcome ..

/-- Lift an unbounded descendant of an arbitrary original atom root to its canonical full
carrier occurrence. The address and the precise original source node are unchanged. -/
def occurrence (i : CertifiedLocalizedCIPInput) (root : i.Atom) {address : List Nat} {node : OfficialCIPNode i.Atom}
    (source : i.UnboundedOfficialSubtree (OfficialCIPNode.root root) address node) :
    i.LocalizedCIPOccurrence (i.certified.input.molecule.atomCount+1) :=
  ⟨_,i.localizedOccurrenceUniversalDepth_covers_atom_moleculeWide root source⟩

/-- For any two incident retained directions, either may be the old parent. Both are cut at
this same focus, in its same original root. Address adjacency is the only routing premise. -/
theorem compare_incident (i : CertifiedLocalizedCIPInput) {d : Nat} (focus a b : i.LocalizedCIPOccurrence d)
    (left : i.LocalizedCarrierTreeAdjacent a.val focus.val) (right : i.LocalizedCarrierTreeAdjacent b.val focus.val) :
    let l : Cursor i d := ⟨a,some focus⟩
    let r : Cursor i d := ⟨b,some focus⟩
    ∃ ka kb : Key i, Expansion i l ka ∧ Expansion i r kb ∧ ka.complete = true ∧ kb.complete = true ∧
      trace i l r = ExactOfficialRuleMajorKey.compareAddressedSourceTrace i.moleculeGraph ka.sourceNodes kb.sourceNodes ∧
      cipTraceOutcome (trace i l r) = ExactOfficialRuleMajorKey.compare i.moleculeGraph ka kb :=
  trace_source i _ _ ((i.mem_localizedRerootNeighborFrames_iff focus.val a.val).mpr ⟨a.property,left⟩)
    ((i.mem_localizedRerootNeighborFrames_iff focus.val b.val).mpr ⟨b.property,right⟩)

private instance (i : CertifiedLocalizedCIPInput) (a b : i.LocalizedCIPOccurrenceFrame) :
    Decidable (i.LocalizedCarrierTreeAdjacent a b) := by unfold LocalizedCarrierTreeAdjacent; infer_instance

/-- These are two distinct incident directions of one nonduplicate occurrence. -/
def Incident (i : CertifiedLocalizedCIPInput) {d : Nat} (focus a b : i.LocalizedCIPOccurrence d) : Prop :=
  focus.val.node.isDuplicateLeaf = false ∧ a.val.address ≠ b.val.address ∧
    i.LocalizedCarrierTreeAdjacent a.val focus.val ∧ i.LocalizedCarrierTreeAdjacent b.val focus.val

instance {i d} {focus a b : i.LocalizedCIPOccurrence d} : Decidable (Incident i focus a b) := by
  unfold Incident
  infer_instance

/-- Executable comparison at a single retained occurrence. The entry verifies both directions
at the given focus before emitting the exact constitutional trace. -/
def compareAt? (i : CertifiedLocalizedCIPInput) {d : Nat} (focus a b : i.LocalizedCIPOccurrence d) :
    Option (List CIPRuleDecision) :=
  if Incident i focus a b then some (trace i ⟨a,some focus⟩ ⟨b,some focus⟩) else none

theorem compareAt?_exact (i : CertifiedLocalizedCIPInput) {d : Nat} (focus a b : i.LocalizedCIPOccurrence d)
    (t : List CIPRuleDecision) :
    compareAt? i focus a b = some t ↔ Incident i focus a b ∧
      t = trace i ⟨a,some focus⟩ ⟨b,some focus⟩ := by
  by_cases h : Incident i focus a b
  · simp only [compareAt?,h,if_true,Option.some.injEq,true_and]
    exact eq_comm
  · simp [compareAt?,h]

/-- On every admitted ring, take any three successive addresses in one unbounded original
atom-rooted expansion. The inward arm at the middle address retains its historical source,
and the outward arm retains its own. Both directed edge roots use the full molecular carrier. -/
theorem old_parent_vs_child (input : LocalizedChemicalRing.Input) (root : input.certified.Atom)
    (path : List Nat) (j k : Nat) (p f s : OfficialCIPNode input.certified.Atom)
    (hp : input.certified.UnboundedOfficialSubtree (OfficialCIPNode.root root) path p)
    (hf : input.certified.UnboundedOfficialSubtree (OfficialCIPNode.root root) (path ++ [j]) f)
    (hs : input.certified.UnboundedOfficialSubtree (OfficialCIPNode.root root) ((path ++ [j]) ++ [k]) s) :
    let i := input.certified
    let focus := occurrence i root hf
    let left : Cursor i _ := ⟨occurrence i root hp,some focus⟩
    let right : Cursor i _ := ⟨occurrence i root hs,some focus⟩
    ∃ ka kb : Key i, Expansion i left ka ∧ Expansion i right kb ∧ ka.complete = true ∧ kb.complete = true ∧
      trace i left right = ExactOfficialRuleMajorKey.compareAddressedSourceTrace i.moleculeGraph ka.sourceNodes kb.sourceNodes ∧
      cipTraceOutcome (trace i left right) = ExactOfficialRuleMajorKey.compare i.moleculeGraph ka kb := by
  apply compare_incident
  · exact ⟨rfl,Or.inl ⟨by simp [occurrence],by simp [occurrence]⟩⟩
  · exact ⟨rfl,Or.inr ⟨by simp [occurrence],by simp [occurrence]⟩⟩

end TetraStereo.Engine.RingRetainedConstitution

assert_kernel_only TetraStereo.Engine.RingRetainedConstitution.key_source
assert_kernel_only TetraStereo.Engine.RingRetainedConstitution.trace_source
assert_kernel_only TetraStereo.Engine.RingRetainedConstitution.compare_incident

assert_kernel_only TetraStereo.Engine.RingRetainedConstitution.key_stable
assert_kernel_only TetraStereo.Engine.RingRetainedConstitution.old_parent_vs_child
assert_kernel_only TetraStereo.Engine.RingRetainedConstitution.compareAt?_exact

assert_kernel_only TetraStereo.Engine.RingRetainedConstitution.key_cached
