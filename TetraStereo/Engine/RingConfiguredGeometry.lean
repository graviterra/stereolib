import TetraStereo.Engine.RingConfiguredPriorities
import TetraStereo.OneCenter.LocalizedMarkedMolecularConfiguration
import TetraStereo.OneCenter.LocalizedMarkedCertifiedTerminalRefusal

set_option autoImplicit false

namespace TetraStereo.Engine.CentresRing.ConfiguredPriority
open OneCenter LocalizedGenericMarkedRecalculation LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors LocalizedMarkedMolecularConfiguration
open RingChemicalPriority Recursive ReferenceFrame

/-- Only one physical hand per configured carbon is read, in molecular
neighbor order, independently of the number of ring paths to that carbon. -/
def SameConfiguredHands (m : RawMolecule) (cs : List Nat) (g h : Geometry) : Prop :=
  ∀ a ∈ cs, (m.canonicalIncidentNeighbors a).length = 4 →
    readback? g (m.canonicalIncidentNeighbors a) = readback? h (m.canonicalIncidentNeighbors a)

private def next (m : RawMolecule) (n : Node) (i : Nat) :=
  (m.canonicalChildren n).find? fun c => c.atom == i && !c.forcedLeaf

private theorem walk {m : RawMolecule} (steps : List Nat) {n r : Node}
    (reached : Reached m n) (real : n.forcedLeaf = false)
    (done_ : steps.foldlM (next m) n = some r) : Reached m r ∧ r.forcedLeaf = false := by
  induction steps generalizing n with
  | nil =>
    obtain rfl : n = r := by simpa using done_
    exact ⟨reached,real⟩
  | cons i steps ih =>
    cases hx : next m n i with
    | none => simp [List.foldlM_cons,hx] at done_
    | some child =>
      have picked : (m.canonicalChildren n).find? (fun c => c.atom == i && !c.forcedLeaf) = some child := hx
      apply ih (reached_child _ _ _ reached (List.mem_of_find?_eq_some picked))
      · simpa using (Bool.and_eq_true_iff.mp (List.find?_some (p := fun c : Node => c.atom == i && !c.forcedLeaf) (a := child) picked)).2
      · simpa [List.foldlM_cons,hx] using done_

private theorem located {m : RawMolecule} {p n} (atPath : occurrence? m p = some n) :
    Reached m n ∧ n.forcedLeaf = false := by
  cases p with
  | nil => simp [occurrence?] at atPath
  | cons a steps =>
    by_cases valid : a < m.atomCount
    · apply walk steps (reached_root m a valid) rfl
      simpa [occurrence?,guard,valid,next] using atPath
    · simp [occurrence?,guard,valid] at atPath

private theorem read_order {m cs p g h t rev order}
    (wf : m.WellFormed) (single : SingleBonded m)
    (same : SameConfiguredHands m cs g h) (f : MolecularFrame m g p) (enabled : f.focus.atom ∈ cs)
    (strict : orders f.ids t rev = [order]) : readback? g order = readback? h order := by
  have seen := located f.reached
  have frame := occurrence_atoms_perm_neighbors m wf single f.focus seen.1 seen.2
  have ids : f.ids.Perm (m.canonicalIncidentNeighbors f.focus.atom) := f.incident ▸ frame
  have member : order ∈ orders f.ids t rev := by simp [strict]
  have orderPerm := List.mem_permutations'.mp (List.mem_filter.mp member).1
  have four := ids.length_eq.symm.trans f.four
  exact readback_perm_congr _ _ (ids.nodup_iff.mp f.distinct) four (orderPerm.trans ids) (same _ enabled four)

private def rebase {m g p i j} (h : Geometry) : Basis m g p i j → Basis m h p i j
  | .atomic d l r hl hr w s => .atomic d l r hl hr w s
  | .constitution c s => .constitution c s
  | .fourth arms w why => .fourth arms w why
  | .stereo pair w a b => .stereo pair w a b
  | .tied pair fixed => .tied pair fixed

@[simp] private theorem rebase_initial {m g p i j h} (b : Basis m g p i j) :
    (rebase h b).initial = b.initial := by cases b <;> rfl
@[simp] private theorem rebase_mark {m g p i j h} (b : Basis m g p i j) (k : Nat) :
    (rebase h b).promoted? k = b.promoted? k := by cases b <;> rfl
@[simp] private theorem rebase_inputs {m g p i j h} (b : Basis m g p i j) :
    (rebase h b).inputs = b.inputs := by cases b <;> rfl

private def rowAt {m g p} (h : Geometry) (r : Row m g p) : Row m h p :=
  ⟨r.i,r.j,rebase h r.basis⟩

@[simp] private theorem entries_at {m g p h} (rs : List (Row m g p)) :
    entries (rs.map (rowAt h)) = entries rs := by simp [entries,List.map_map,rowAt,Function.comp_def]

@[simp] private theorem promoted_at {m g p h} (rs : List (Row m g p)) (k : Nat) :
    promoted? (rs.map (rowAt h)) k = promoted? rs k := by
  simp [promoted?,List.mapM_map,Function.comp_def,rowAt]

private def frameAt {m g p} (h : Geometry) (f : MolecularFrame m g p) : MolecularFrame m h p :=
  ⟨f.focus,f.reached,f.carbon,f.ids,f.incident,f.four,f.distinct,f.rows.map (rowAt h),
   by simpa [List.map_map,rowAt,Function.comp_def] using f.allPairs,by simpa using f.ordinary⟩

@[simp] private theorem inputs_at {m g p h} (f : MolecularFrame m g p) :
    (frameAt h f).inputs = f.inputs := by simp [MolecularFrame.inputs,frameAt,List.flatMap_map,rowAt]

private def outcomeAt {m cs p g h t} (wf : m.WellFormed) (single : SingleBonded m)
    (same : SameConfiguredHands m cs g h) (f : MolecularFrame m g p) (enabled : f.focus.atom ∈ cs) :
    Outcome g f.ids t → Outcome h f.ids t
  | .assigned a b ha hb v hv => .assigned a b ha hb v (by
      simpa only [geometric,← read_order wf single same f enabled ha,readback_mirror,
        ← read_order wf single same f enabled hb] using hv)
  | .tied i j ne inside ties strict => .tied i j ne inside ties strict

@[simp] private theorem outcomeAt_reading {m cs p g h t} (wf : m.WellFormed) (single : SingleBonded m)
    (same : SameConfiguredHands m cs g h) (f : MolecularFrame m g p) (en : f.focus.atom ∈ cs)
    (x : Outcome g f.ids t) : (outcomeAt wf single same f en x).reading? = x.reading? := by cases x <;> rfl


private def withTable {g ids t u} (eqn : t = u) (x : Outcome g ids t) : Outcome g ids u := eqn ▸ x

@[simp] private theorem withTable_reading {g ids t u} (eqn : t = u) (x : Outcome g ids t) :
    (withTable eqn x).reading? = x.reading? := by subst u; rfl

private def ordinaryAt {m cs p g h} (wf : m.WellFormed) (single : SingleBonded m)
    (same : SameConfiguredHands m cs g h) (f : MolecularFrame m g p) (en : f.focus.atom ∈ cs)
    (d : Ordinary f) : Ordinary (frameAt h f) where
  ineligible := by simpa [frameAt] using d.ineligible
  outcome := withTable (entries_at f.rows).symm (outcomeAt wf single same f en d.outcome)

private def promotionAt {m g p} (h : Geometry) (f : Frame m g p) : Frame m h p :=
  ⟨frameAt h f.toMolecularFrame,by simpa [frameAt] using f.eligible⟩

private def trialAt {m cs p g h} (wf : m.WellFormed) (single : SingleBonded m)
    (same : SameConfiguredHands m cs g h) (f : Frame m g p) (en : f.focus.atom ∈ cs)
    (t : ReferenceFrame.Trial f) : ReferenceFrame.Trial (promotionAt h f) where
  mark := t.mark
  table := t.table
  derived := by simpa [promotionAt,frameAt] using t.derived
  consistent := t.consistent
  outcome := outcomeAt wf single same f.toMolecularFrame en t.outcome

private def populationAt {m cs p g h} (wf : m.WellFormed) (single : SingleBonded m)
    (same : SameConfiguredHands m cs g h) (s : Population m g p) (en : s.frame.focus.atom ∈ cs) :
    Population m h p where
  frame := promotionAt h s.frame
  trials := s.trials.map (trialAt wf single same s.frame en)
  complete := by simpa [List.map_map,trialAt,Function.comp_def,promotionAt,frameAt] using s.complete

private theorem consensus_at {m cs p g h} (wf : m.WellFormed) (single : SingleBonded m)
    (same : SameConfiguredHands m cs g h) (s : Population m g p) (en : s.frame.focus.atom ∈ cs) :
    (populationAt wf single same s en).consensus? = s.consensus? := by
  cases ht : s.trials with
  | nil => simp [Population.consensus?,populationAt,ht]
  | cons t ts => simp [Population.consensus?,populationAt,ht,trialAt,List.all_map,Function.comp_def]

/-- A recursively derived verdict can be transported using the hand of
just one canonical order at each configured carbon. Every occurrence,
auxiliary premise and trial mark keeps its identity in the new derivation. -/
theorem Fact.transport {m cs p g h v} (wf : m.WellFormed) (single : SingleBonded m)
    (same : SameConfiguredHands m cs g h) (d : Fact m g cs p v) : Fact m h cs p v := by
  induction d with
  | unspecified n atPath carbon outside => exact .unspecified n atPath carbon outside
  | ordinary f enabled s below _ observed ih =>
    refine .ordinary (frameAt h f) enabled (ordinaryAt wf single same f enabled s)
      (by simpa using below) (by simpa using ih) ?_
    simpa [ordinaryAt] using observed
  | promoted pop enabled below _ agree ih =>
    refine .promoted (populationAt wf single same pop enabled) enabled ?_ ?_ ?_
    · simpa [Population.inputs,populationAt,promotionAt] using below
    · simpa [Population.inputs,populationAt,promotionAt] using ih
    · exact (consensus_at wf single same pop enabled).trans agree

theorem fact_iff_of_configured_hands {m cs p g h v} (wf : m.WellFormed) (single : SingleBonded m)
    (same : SameConfiguredHands m cs g h) : Fact m g cs p v ↔ Fact m h cs p v :=
  ⟨Fact.transport wf single same,Fact.transport wf single (fun a ha four => (same a ha four).symm)⟩

def Ranked.transport {m cs p g h} (wf : m.WellFormed) (single : SingleBonded m)
    (same : SameConfiguredHands m cs g h) (r : Ranked m g cs p) : Ranked m h cs p where
  frame := frameAt h r.frame
  enabled := r.enabled
  inputs := by
    intro x hx
    obtain ⟨below,longer,fact⟩ := r.inputs x (by simpa using hx)
    exact ⟨below,longer,fact.transport wf single same⟩
  verdict := r.verdict
  derived := r.derived.transport wf single same

private theorem rebase_snapshot {m g p i j h visible} (b : Basis m g p i j)
    (snap : ComparisonAgreement.Snapshot b visible) : ComparisonAgreement.Snapshot (rebase h b) visible := by
  cases b <;> exact ⟨snap.read,snap.covered⟩

private theorem rebase_answer {m g p i j h} (b : Basis m g p i j) (mark : Option Nat) :
    ComparisonAgreement.answer? (rebase h b) mark = ComparisonAgreement.answer? b mark := by
  cases b <;> rfl

/-- A specific comparison at the same path, mark and publication state
has the same proof of its deciding rule and signed integer. -/
def CheckedCall.transport {m g h cs root call} (wf : m.WellFormed) (single : SingleBonded m)
    (same : SameConfiguredHands m cs g h) (d : CheckedCall m g cs root call) : CheckedCall m h cs root call := by
  refine ⟨d.molecule,d.root_eq,?_⟩
  generalize eqn : (⟨call.winner,call.comparison.value⟩ : ComparisonAgreement.Answer) = ans
  have original : Ground m g cs call ans := eqn ▸ d.exactAnswer
  cases original with
  | constitution rank applies => exact .constitution rank applies
  | stereo b full snap support answer =>
    refine .stereo (rebase h b) full (rebase_snapshot _ snap) ?_ ((rebase_answer b _).trans answer)
    intro x hx
    obtain ⟨below,longer,fact⟩ := support x (by simpa using hx)
    exact ⟨below,longer,fact.transport wf single same⟩

/-- A published auxiliary retains its exact discovery address and case. -/
def CheckedUpdate.transport {m g h cs t u} (wf : m.WellFormed) (single : SingleBonded m)
    (same : SameConfiguredHands m cs g h) (d : CheckedUpdate m g cs t u) : CheckedUpdate m h cs t u :=
  ⟨d.path,d.located,d.rank.transport wf single same,d.label⟩

/-- For every geometry realizing the supplied configurations, the original
center receipt retains its scoped root reading, all signed comparisons by
chronological index, and every published auxiliary at its discovery address. -/
theorem CheckedCenter.under_configured_geometry {m cs t g h}
    (audit : CheckedCenter m g cs t) (wf : m.WellFormed) (single : SingleBonded m)
    (same : SameConfiguredHands m cs g h) :
    Fact m h cs [t.atom] audit.root.verdict ∧ labelCode (audit.root.verdict.bind Reading.label) = t.label ∧
    (∀ (i : Nat) (cmp : Comparison), (Molecular.chronological t)[i]? = some cmp →
      ∃ c, audit.source.derived.calls[i]? = some c ∧ c.comparison = cmp ∧ Nonempty (CheckedCall m h cs t.atom c)) ∧
    (∀ u ∈ t.updates, Nonempty (CheckedUpdate m h cs t u)) := by
  refine ⟨audit.root.derived.transport wf single same,audit.letter,?_,?_⟩
  · intro i cmp found
    obtain ⟨c,hc,eqn,⟨call⟩⟩ := audit.at_index found
    exact ⟨c,hc,eqn,⟨call.transport wf single same⟩⟩
  · intro u member
    obtain ⟨update⟩ := audit.updates.member member
    exact ⟨update.transport wf single same⟩

/-- Every row of an admitted public receipt is valid under every completion
of its configured stereochemistry. The input itself supplies graph
well-formedness and single bonding; no new source run is required. -/
theorem Report.for_all_completions {input cs} (report : Report input cs) (h : Geometry)
    (same : SameConfiguredHands input.molecule cs (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified) h)
    {t} (member : t ∈ report.source.molecular.replay.traces) :
    ∃ audit : CheckedCenter input.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified) cs t,
      Fact input.molecule h cs [t.atom] audit.root.verdict ∧ labelCode (audit.root.verdict.bind Reading.label) = t.label ∧
      (∀ (i : Nat) (cmp : Comparison), (Molecular.chronological t)[i]? = some cmp →
        ∃ c, audit.source.derived.calls[i]? = some c ∧ c.comparison = cmp ∧ Nonempty (CheckedCall input.molecule h cs t.atom c)) ∧
      (∀ u ∈ t.updates, Nonempty (CheckedUpdate input.molecule h cs t u)) := by
  obtain ⟨audit⟩ := report.checked.member member
  have single := LocalizedMarkedCertifiedTerminalRefusal.raw_single input.molecule input.certified input.agreement
    input.admissible.1.1 input.admissible.1.2 input.supported input.single
  exact ⟨audit,audit.under_configured_geometry input.admissible.1.1 single same⟩

end TetraStereo.Engine.CentresRing.ConfiguredPriority

assert_kernel_only TetraStereo.Engine.CentresRing.ConfiguredPriority.Fact.transport
assert_kernel_only TetraStereo.Engine.CentresRing.ConfiguredPriority.fact_iff_of_configured_hands
assert_kernel_only TetraStereo.Engine.CentresRing.ConfiguredPriority.CheckedCall.transport
assert_kernel_only TetraStereo.Engine.CentresRing.ConfiguredPriority.CheckedUpdate.transport
assert_kernel_only TetraStereo.Engine.CentresRing.ConfiguredPriority.CheckedCenter.under_configured_geometry

assert_kernel_only TetraStereo.Engine.CentresRing.ConfiguredPriority.Report.for_all_completions
