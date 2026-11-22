import TetraStereo.Engine.RingComparisonAgreement

set_option autoImplicit false

namespace TetraStereo.Engine.CentresRing.ConfiguredPriority
open OneCenter LocalizedGenericMarkedRecalculation
open RingChemicalPriority Recursive ComparisonAgreement

/-- A scoped reading distinguishes a carbon with no supplied configuration
from a configured carbon at which a molecular ranking yields no descriptor. -/
inductive Fact (m : RawMolecule) (g : Geometry) (configured : List Nat) :
    List Nat → Option Reading → Prop where
  | unspecified {p} (node : RawMolecule.CanonicalBranchNode) (located : occurrence? m p = some node)
      (carbon : (m.atoms[node.atom]?).any (fun a => a.element == .C) = true)
      (outside : node.atom ∉ configured) : Fact m g configured p none
  | ordinary {p v} (frame : ReferenceFrame.MolecularFrame m g p) (enabled : frame.focus.atom ∈ configured)
      (decision : ReferenceFrame.Ordinary frame)
      (below : ∀ x ∈ frame.inputs, p <+: x.1 ∧ p.length < x.1.length)
      (children : ∀ x ∈ frame.inputs, Fact m g configured x.1 x.2)
      (outcome : decision.outcome.reading? = v) : Fact m g configured p v
  | promoted {p v} (population : ReferenceFrame.Population m g p) (enabled : population.frame.focus.atom ∈ configured)
      (below : ∀ x ∈ population.inputs, p <+: x.1 ∧ p.length < x.1.length)
      (children : ∀ x ∈ population.inputs, Fact m g configured x.1 x.2)
      (unanimous : population.consensus? = some v) : Fact m g configured p v

/-- Every positive reading has an explicitly configured carbon, a
geometric order and a casing determined by the frame's reversal count. -/
theorem Fact.chemical_letter {m g cs p r} (d : Fact m g cs p (some r)) :
    ∃ (f : ReferenceFrame.MolecularFrame m g p) (order : List Nat),
      f.focus.atom ∈ cs ∧ readback? g order = some r.actual ∧
      r.label = some (if f.reversals % 2 = 0 then .chiral r.actual else .pseudoasymmetric (pseudoRSOfRS r.actual)) := by
  cases d with
  | ordinary f enabled s _ _ observed =>
    cases eqn : s.outcome with
    | tied => simp [eqn,ReferenceFrame.Outcome.reading?] at observed
    | assigned a b ha hb v hv =>
      obtain rfl : v = r := by simpa [eqn,ReferenceFrame.Outcome.reading?] using observed
      exact ⟨f,a,enabled,f.chemical_letter ha hb hv⟩
  | promoted pop enabled _ _ agreed =>
    have nonempty : ReferenceFrame.marks pop.frame.ids (ReferenceFrame.entries pop.frame.rows) ≠ [] := by
      intro h
      have eligible := pop.frame.eligible
      simp [h] at eligible
    obtain ⟨k,hk⟩ := List.exists_mem_of_ne_nil _ nonempty
    obtain ⟨_,a,_,_,_,_,_,raw,label⟩ := pop.chemical_letter agreed k hk
    exact ⟨pop.frame.toMolecularFrame,a,enabled,raw,label⟩

/-- Finite molecular subderivations can be read in one publication list.
This lemma makes no claim of uniqueness for that list. -/
private theorem gather {m g} (needed : InventoryPriority.Entries)
    (known : ∀ x ∈ needed, ∃ es, ReferenceDerivation.Derives m g es x.1 x.2) :
    ∃ es, needed ⊆ es ∧ ∀ x ∈ needed, ReferenceDerivation.Derives m g es x.1 x.2 := by
  induction needed with
  | nil => exact ⟨[],by simp,by simp⟩
  | cons x xs ih =>
    obtain ⟨left,hx⟩ := known x List.mem_cons_self
    obtain ⟨right,sub,rest⟩ := ih (fun y hy => known y (List.mem_cons_of_mem x hy))
    let es := x :: (left ++ right)
    have fromLeft : left ⊆ es := fun _ h => List.mem_cons_of_mem _ (List.mem_append_left _ h)
    have fromRight : right ⊆ es := fun _ h => List.mem_cons_of_mem _ (List.mem_append_right _ h)
    refine ⟨es,?_,?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | h
      · exact List.mem_cons_self
      · exact fromRight (sub h)
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | h
      · exact hx.weaken fromLeft
      · exact (rest y h).weaken fromRight

/-- Lift a configured-inventory derivation to a full molecular derivation.
Only omitted configurations below this root need independent absence
proofs. Positive auxiliaries and their priority decisions are transferred
recursively from the scoped proof. -/
theorem Fact.to_molecular {m g cs p v} (d : Fact m g cs p v)
    (omissions : ∀ q, p <+: q → ∀ n, occurrence? m q = some n →
      (m.atoms[n.atom]?).any (fun a => a.element == .C) = true → n.atom ∉ cs →
      ∃ es, ReferenceDerivation.Derives m g es q none) :
    ∃ es, ReferenceDerivation.Derives m g es p v := by
  induction d with
  | unspecified n located carbon excluded => exact omissions _ (List.prefix_refl _) n located carbon excluded
  | ordinary f _ decision below _ observed ih =>
    obtain ⟨es,bound,children⟩ := gather f.inputs (fun x h =>
      ih x h (fun q ext => omissions q ((below x h).1.trans ext)))
    exact ⟨es,.ordinary f decision bound children observed⟩
  | promoted pop _ below _ agree ih =>
    obtain ⟨es,bound,children⟩ := gather pop.inputs (fun x h =>
      ih x h (fun q ext => omissions q ((below x h).1.trans ext)))
    exact ⟨es,.promotion pop bound children agree⟩

/-- With every carbon below the root configured, all scoped readings
(including ties) already have full molecular derivations. -/
theorem Fact.to_molecular_of_all_carbons {m g cs p v} (d : Fact m g cs p v)
    (all : ∀ q, p <+: q → ∀ n, occurrence? m q = some n →
      (m.atoms[n.atom]?).any (fun a => a.element == .C) = true → n.atom ∈ cs) :
    ∃ es, ReferenceDerivation.Derives m g es p v :=
  d.to_molecular fun q sub n reached carbon excluded => (excluded (all q sub n reached carbon)).elim

structure Ranked (m : RawMolecule) (g : Geometry) (configured p : List Nat) where
  frame : ReferenceFrame.MolecularFrame m g p
  enabled : frame.focus.atom ∈ configured
  inputs : ∀ x ∈ frame.inputs, p <+: x.1 ∧ p.length < x.1.length ∧ Fact m g configured x.1 x.2
  verdict : Option Reading
  derived : Fact m g configured p verdict

private structure Entry (m : RawMolecule) (g : Geometry) (cs p : List Nat) where
  value : List Nat × Option Reading
  below : p <+: value.1 ∧ p.length < value.1.length
  proof : Fact m g cs value.1 value.2

private def atPath? (m : RawMolecule) (g : Geometry) (cs : List Nat) (depth : Nat)
    (p : List Nat) (childRank : (q : List Nat) → p <+: q ∧ p.length < q.length → Option (Ranked m g cs q)) :
    Option (Ranked m g cs p) :=
  if saturatedWithHalogens m then do
    let node ← occurrence? m p
    guard (cs.contains node.atom)
    let entry (q : List Nat) : Option (Entry m g cs p) := do
      if below : p <+: q ∧ p.length < q.length then
        let ⟨child,located⟩ ← (occurrence? m q).attach
        if enabled : child.atom ∈ cs then
          let r ← childRank q below
          return ⟨(q,r.verdict),below,r.derived⟩
        else if carbon : (m.atoms[child.atom]?).any (fun a => a.element == .C) = true then
          return ⟨(q,none),below,.unspecified child located carbon enabled⟩
      none
    let rows := (RingAuxiliaryInventory.promotionPaths m node).eraseDups.filterMap entry
    let table := rows.map Entry.value
    let frame ← ReferenceFrame.molecularFrame? m g p depth (ReferenceDerivation.armFrom table)
    if active : frame.focus.atom ∈ cs then
      if complete : ∀ x ∈ frame.inputs, x ∈ table then
        have subs : ∀ x ∈ frame.inputs, p <+: x.1 ∧ p.length < x.1.length ∧ Fact m g cs x.1 x.2 := by
          intro x hx
          obtain ⟨e,_,rfl⟩ := List.mem_map.mp (complete x hx)
          exact ⟨e.below.1,e.below.2,e.proof⟩
        if let some d := frame.ordinary? then return ⟨frame,active,subs,_,.ordinary frame active d (fun x h => ⟨(subs x h).1,(subs x h).2.1⟩) (fun x h => (subs x h).2.2) rfl⟩
        if eligible : (ReferenceFrame.marks frame.ids (ReferenceFrame.entries frame.rows)).length ∈ [3,4] then
          let f : ReferenceFrame.Frame m g p := ⟨frame,eligible⟩
          let trials ← ReferenceFrame.trials? f
          if allMarks : trials.map ReferenceFrame.Trial.mark = ReferenceFrame.marks frame.ids (ReferenceFrame.entries frame.rows) then
            let pop : ReferenceFrame.Population m g p := ⟨f,trials,allMarks⟩
            let ⟨v,h⟩ ← pop.consensus?.attach
            return ⟨frame,active,subs,v,.promoted pop active (fun x hx => ⟨(subs x hx).1,(subs x hx).2.1⟩) (fun x hx => (subs x hx).2.2) h⟩
    none
  else none

/-- Rank from the graph, coordinates and configured atoms. The callback can
read only proper descendants in this rooted molecular digraph. -/
def rank? (m : RawMolecule) (g : Geometry) (cs : List Nat) (depth : Nat) : Nat →
    (p : List Nat) → Option (Ranked m g cs p)
  | 0,_ => none
  | fuel+1,p => atPath? m g cs depth p fun q _ => rank? m g cs depth fuel q

theorem rank?_of_outside {m : RawMolecule} (outside : saturatedWithHalogens m = false)
    (g : Geometry) (cs : List Nat) (depth fuel : Nat) (p : List Nat) :
    rank? m g cs depth fuel p = none := by
  cases fuel <;> simp [rank?,atPath?,outside]

/-- Once the budget covers the remaining simple path, more fuel leaves the
entire dependent result unchanged, including an unresolved result. -/
theorem rank_stable (m : RawMolecule) (g : Geometry) (cs : List Nat) (depth fuel extra : Nat) (p : List Nat)
    (enough : m.atomCount < p.length + fuel) :
    rank? m g cs depth fuel p = rank? m g cs depth (fuel+extra) p := by
  induction fuel generalizing p with
  | zero =>
    cases extra with
    | zero => rfl
    | succ extra =>
      by_cases domain : saturatedWithHalogens m = true
      · have missing : occurrence? m p = none := by
          cases reached : occurrence? m p with
          | none => rfl
          | some node =>
            have length := OccurrenceTable.reached_length (OccurrenceTable.endpoints_of_saturated domain) reached
            omega
        simp [rank?,atPath?,domain,missing]
      · simp [rank?,atPath?,domain]
  | succ fuel ih =>
    simp only [Nat.succ_add,rank?]
    congr 1
    funext q below
    exact ih q (by have := below.2; omega)

/-- A witnessed comparison retains the effective configuration inventory
and every recursively justified premise for its exact operands. -/
inductive Ground (m : RawMolecule) (g : Geometry) (cs : List Nat) (c : Molecular.Call) : Answer → Type where
  | constitution (rank : IsotopePriority.IncidentComparison m c.frame.focus c.comparison.left c.comparison.right)
      (applies : c.frame.constitutional = true ∨ rank.ordering ≠ .eq) : Ground m g cs c (constitutionalAnswer rank)
  | stereo (basis : ReferenceFrame.Basis m g c.frame.focus c.comparison.left c.comparison.right)
      (full : c.frame.constitutional = false) (visible : Snapshot basis c.frame.visible)
      (support : ∀ x ∈ basis.inputs, c.frame.focus <+: x.1 ∧ c.frame.focus.length < x.1.length ∧ Fact m g cs x.1 x.2)
      {a : Answer} (answer : answer? basis c.frame.mark = some a) : Ground m g cs c a

structure CheckedCall (m : RawMolecule) (g : Geometry) (cs : List Nat) (root : Nat) (c : Molecular.Call) where
  molecule : c.frame.molecule = m
  root_eq : c.frame.focus.head? = some root
  exactAnswer : Ground m g cs c ⟨c.winner,c.comparison.value⟩

private def checkCall {m g cs} (root : Nat) (lookup : (p : List Nat) → Option (Ranked m g cs p))
    (c : Molecular.Call) : Option (CheckedCall m g cs root c) := do
  if bound : c.frame.molecule = m ∧ c.frame.focus.head? = some root then
    if let some r := IsotopePriority.compareIncident? m c.frame.focus c.comparison.left c.comparison.right then
      if applies : c.frame.constitutional = true ∨ r.ordering ≠ .eq then
        if eqn : constitutionalAnswer r = ⟨c.winner,c.comparison.value⟩ then
          return ⟨bound.1,bound.2,eqn ▸ Ground.constitution r applies⟩
        else none
    if full : c.frame.constitutional = false then
      let r ← lookup c.frame.focus
      let row ← r.frame.rows.find? (fun x => x.i == c.comparison.left && x.j == c.comparison.right)
      if ri : row.i = c.comparison.left then
        if rj : row.j = c.comparison.right then
          let b : ReferenceFrame.Basis m g c.frame.focus c.comparison.left c.comparison.right := ri ▸ rj ▸ row.basis
          let ⟨visible⟩ ← snapshot? b c.frame.visible
          if used : ∀ x ∈ b.inputs, x ∈ r.frame.inputs then
            if exactAnswer : answer? b c.frame.mark = some ⟨c.winner,c.comparison.value⟩ then
              return ⟨bound.1,bound.2,.stereo b full visible (fun x h => r.inputs x (used x h)) exactAnswer⟩
  none

structure CheckedUpdate (m : RawMolecule) (g : Geometry) (cs : List Nat) (t : CenterTrace) (u : Update) where
  path : List Nat
  located : t.discovered[u.index]? = some path.reverse
  rank : Ranked m g cs path
  label : labelCode (rank.verdict.bind Reading.label) = u.label

structure CheckedCenter (m : RawMolecule) (g : Geometry) (cs : List Nat) (t : CenterTrace) where
  source : Molecular.Evidence m g t
  calls : Each (CheckedCall m g cs t.atom) source.derived.calls
  updates : Each (CheckedUpdate m g cs t) t.updates
  root : Ranked m g cs [t.atom]
  letter : labelCode (root.verdict.bind Reading.label) = t.label

theorem CheckedCenter.at_index {m g cs t} (audit : CheckedCenter m g cs t) {i : Nat} {cmp : Comparison}
    (atIndex : (Molecular.chronological t)[i]? = some cmp) :
    ∃ c, audit.source.derived.calls[i]? = some c ∧ c.comparison = cmp ∧ Nonempty (CheckedCall m g cs t.atom c) := by
  rw [← audit.source.coverage,List.getElem?_map] at atIndex
  obtain ⟨c,found,eqn⟩ := Option.map_eq_some_iff.mp atIndex
  exact ⟨c,found,eqn,audit.calls.member (List.mem_of_getElem? found)⟩

theorem CheckedCenter.auxiliary_at {m g cs t} (audit : CheckedCenter m g cs t) {u} (member : u ∈ t.updates) :
    ∃ p v, t.discovered[u.index]? = some p.reverse ∧ Fact m g cs p v ∧ labelCode (v.bind Reading.label) = u.label := by
  obtain ⟨w⟩ := audit.updates.member member
  exact ⟨w.path,w.rank.verdict,w.located,w.rank.derived,w.label⟩

/-- Compare the configured root with the same molecule at the supplied
full coordinates. The two outcomes retain the complete molecular
certificate and an equality or inequality with the verified source label. -/
inductive CoordinateComparison (m : RawMolecule) (g : Geometry) (t : CenterTrace) where
  | agrees (full : ReferenceDerivation.Certificate m g [t.atom])
      (same : labelCode (full.verdict.bind Reading.label) = t.label)
  | differs (full : ReferenceDerivation.Certificate m g [t.atom])
      (different : labelCode (full.verdict.bind Reading.label) ≠ t.label)

def CheckedCenter.compareCoordinates? {m g cs t} (audit : CheckedCenter m g cs t) (depth : Nat) :
    Option (CoordinateComparison m g t) := do
  let full ← ReferenceDerivation.derive? m g depth (m.atomCount+1) [t.atom]
  if h : labelCode (full.verdict.bind Reading.label) = labelCode (audit.root.verdict.bind Reading.label) then
    return .agrees full (h.trans audit.letter)
  else return .differs full (fun eqn => h (eqn.trans audit.letter.symm))

/-- Each materialized occurrence stores exactly its saturated-budget result.
The configuration inventory, geometry and molecular observation depth are
part of the type of the cache. -/
structure CacheRow (m : RawMolecule) (g : Geometry) (cs : List Nat) (depth : Nat) where
  path : List Nat
  result : Option (Ranked m g cs path)
  exactResult : result = rank? m g cs depth (m.atomCount+1) path

abbrev Cache (m : RawMolecule) (g : Geometry) (cs : List Nat) (depth : Nat) := List (CacheRow m g cs depth)

def Cache.read {m g cs depth} (p : List Nat) : Cache m g cs depth → Option (Ranked m g cs p)
  | [] => rank? m g cs depth (m.atomCount+1) p
  | row :: rest => if same : row.path = p then same ▸ row.result else Cache.read p rest

theorem Cache.read_exact {m g cs depth} (p : List Nat) (rows : Cache m g cs depth) :
    rows.read p = rank? m g cs depth (m.atomCount+1) p := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    by_cases same : row.path = p
    · subst p
      simpa [Cache.read] using row.exactResult
    · simpa [Cache.read,same] using ih

private def cacheRow {m g cs depth} (rows : Cache m g cs depth) (p : List Nat) : CacheRow m g cs depth :=
  let result := atPath? m g cs depth p (fun q _ => rows.read q)
  ⟨p,result,by
    unfold result
    rw [rank?]
    congr 1
    funext q below
    rw [Cache.read_exact]
    exact (rank_stable m g cs depth m.atomCount 1 q (by have := below.2; omega)).symm⟩

/-- Compute configured descendants once, longest paths first. Only enabled
carbon sites need a recursive ranking; every excluded site is read directly
from its inventory membership at the parent. Extra paths can come from an
arbitrary discovery order and do not affect the value of a lookup. -/
def cacheAtRoot (m : RawMolecule) (g : Geometry) (cs : List Nat) (depth root : Nat)
    (extra : List (List Nat)) : Cache m g cs depth :=
  let paths := ((occurrence? m [root]).map (RingAuxiliaryInventory.promotionPaths m)).getD []
  let configured := paths.filter (fun p => p.getLast?.any cs.contains)
  let ordered := ([root] :: (configured ++ extra)).eraseDups.mergeSort (fun p q => decide (q.length ≤ p.length))
  ordered.foldl (fun rows p => cacheRow rows p :: rows) []

def checkCenter? {m g t} (source : Molecular.Evidence m g t) (cs : List Nat) (depth : Nat) :
    Option (CheckedCenter m g cs t) := do
  let discovered := t.discovered.map List.reverse
  let rows := cacheAtRoot m g cs depth t.atom discovered
  let lookup := fun p => if p = [t.atom] ∨ p ∈ discovered then rows.read p else none
  let root ← lookup [t.atom]
  if exactRoot : labelCode (root.verdict.bind Reading.label) = t.label then
    let calls ← ComparisonAgreement.traverse (checkCall t.atom lookup) source.derived.calls
    let updates ← ComparisonAgreement.traverse (fun u => do
      let ⟨p,found⟩ ← (t.discovered[u.index]?).attach
      let rank ← lookup p.reverse
      if same : labelCode (rank.verdict.bind Reading.label) = u.label then
        return (⟨p.reverse,by simpa using found,rank,same⟩ : CheckedUpdate m g cs t u)
      none) t.updates
    return ⟨source,calls,updates,root,exactRoot⟩
  none

structure Report (input : LocalizedChemicalRing.Input) (cs : List Nat) where
  source : Molecular.SourceChecked input cs
  checked : Each (CheckedCenter input.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified) cs)
    source.molecular.replay.traces

private def checkAll {m g} (cs : List Nat) (depth : Nat) :
    (rows : List (Sigma (Molecular.Evidence m g))) → Option (Each (CheckedCenter m g cs) (rows.map Sigma.fst))
  | [] => some .nil
  | ⟨_,e⟩ :: rest => do return .cons (← checkCenter? e cs depth) (← checkAll cs depth rest)

/-- Verify the release's explicitly configured inventory. Unspecified sites
have no published stereochemistry in this report. Full-coordinate chemical
conformance is available separately through ComparisonAgreement. -/
def checkSource (input : LocalizedChemicalRing.Input) (packet : Molecular.SourceReceipt) (cs : List Nat)
    (depth : Nat) : Except String (Report input cs) := do
  let s ← Molecular.checkSourceReceipt input packet cs
  let some checked := checkAll cs depth s.molecular.derivations
    | throw "the configured molecular comparisons, publications or report do not agree"
  return ⟨s,s.molecular.inventory_eq ▸ checked⟩

end TetraStereo.Engine.CentresRing.ConfiguredPriority

assert_kernel_only TetraStereo.Engine.CentresRing.ConfiguredPriority.Fact.to_molecular
assert_kernel_only TetraStereo.Engine.CentresRing.ConfiguredPriority.Fact.to_molecular_of_all_carbons
assert_kernel_only TetraStereo.Engine.CentresRing.ConfiguredPriority.Fact.chemical_letter
assert_kernel_only TetraStereo.Engine.CentresRing.ConfiguredPriority.CheckedCenter.at_index
assert_kernel_only TetraStereo.Engine.CentresRing.ConfiguredPriority.CheckedCenter.auxiliary_at
assert_kernel_only TetraStereo.Engine.CentresRing.ConfiguredPriority.CheckedCenter.compareCoordinates?
assert_kernel_only TetraStereo.Engine.CentresRing.ConfiguredPriority.checkSource

assert_kernel_only TetraStereo.Engine.CentresRing.ConfiguredPriority.rank_stable
assert_kernel_only TetraStereo.Engine.CentresRing.ConfiguredPriority.Cache.read_exact
