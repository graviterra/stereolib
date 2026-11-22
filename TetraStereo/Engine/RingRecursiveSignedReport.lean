import TetraStereo.Engine.RingFrozenSigned
import TetraStereo.Engine.RingOccurrencePublication
import TetraStereo.Engine.RingSilentPair

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.RecursiveSigned
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation Recursive
open InventoryPriority (Entries)

theorem Certificate.replay {m g p} (c : Certificate m g p) {rows : Entries}
    (same : rows.Perm c.published) (order : Publication.ChildrenFirst rows) :
    Derives m g rows p c.verdict ∧ ∀ before x after, rows = before ++ x :: after →
      Derives m g before x.1 x.2 :=
  Publication.replay (fun {_ _ _} d {_} keep => d.localize keep) c.derived c.issued same order

/-- All occurrences in one distance batch may read the same frozen table.
Each recursively mixed signed decision can be derived before its peers publish. -/
theorem Certificate.frozen_batch {m g p} (c : Certificate m g p) {x} (issued : x ∈ c.published) :
    Derives m g (c.published.filter fun y => x.1.length < y.1.length) x.1 x.2 :=
  (c.issued _ issued).localize (fun _ hy lower => List.mem_filter.mpr ⟨hy,decide_eq_true lower.2⟩)

theorem Certificate.byDistance_replays {m g p} (c : Certificate m g p) {es : Entries}
    (same : es.Perm c.published) :
    let rows := ReferenceDerivation.byDistance es
    Derives m g rows p c.verdict ∧ ∀ before x after, rows = before ++ x :: after →
      Derives m g before x.1 x.2 :=
  c.replay ((List.mergeSort_perm ..).trans same) (Publication.childrenFirst_byDistance es)

/-- A row records a terminal-pair refusal, a direct constitutional decision,
or a recursively signed stereochemical decision. -/
inductive CarbonVerdict (m : RawMolecule) (g : Geometry) (depth i : Nat) where
  | direct (proof : LocalIsotopeCarbonReport.Verdict m g depth i)
  | terminal (pair : RingTerminalPair.Certificate m i)
  | silent (pair : RingSilentPair.Certificate m depth i)
  | recursive (certificate : Certificate m g [i])
  | frozen (certificate : FrozenSigned.Certificate (cacheAtRoot m g depth i) [i])

def CarbonVerdict.label {m g depth i} : CarbonVerdict m g depth i → Option LocalizedAuxiliaryLabel
  | .direct v => v.label
  | .terminal _ | .silent _ => none
  | .recursive c => c.verdict.bind Reading.label
  | .frozen c => c.frame.step.reading?.bind Reading.label

def carbon? (m : RawMolecule) (g : Geometry) (depth i : Nat) : Option (CarbonVerdict m g depth i) :=
  match RingTerminalPair.check? m i with
  | some pair => some (.terminal pair)
  | none => match LocalIsotopeCarbonReport.at? m g depth i with
    | some v => some (.direct v)
    | none =>
      let base := cacheAtRoot m g depth i
      match base.read [i] with
      | some cert => some (.recursive cert)
      | none => match FrozenSigned.checkWith? base i with
        | some c => some (.frozen c)
        | none => (RingSilentPair.check? m depth i).map .silent

structure Report (input : LocalizedChemicalRing.Input) (depth : Nat) where
  rows : List ((i : Nat) × CarbonVerdict input.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified) depth i)
  inventory : rows.map Sigma.fst = RingCarbonReport.carbons input.molecule

def Report.labels {input depth} (r : Report input depth) := r.rows.map fun row => (row.1,row.2.label)

private def collect (m : RawMolecule) (g : Geometry) (depth : Nat) :
    (ids : List Nat) → Option {rows : List ((i : Nat) × CarbonVerdict m g depth i) // rows.map Sigma.fst = ids}
  | [] => some ⟨[],rfl⟩
  | i :: ids => do
    let head ← carbon? m g depth i
    let tail ← collect m g depth ids
    return ⟨⟨i,head⟩ :: tail.val,by simp [tail.property]⟩

private theorem collect_isSome (m g depth ids) : (collect m g depth ids).isSome = true ↔
    ∀ i ∈ ids, (LocalIsotopeCarbonReport.at? m g depth i).isSome = true ∨
      (RingTerminalPair.check? m i).isSome = true ∨
      (derive? m g depth m.atomCount [i]).isSome = true ∨ (FrozenSigned.check? m g depth i).isSome = true ∨
      (RingSilentPair.check? m depth i).isSome = true := by
  have row (i : Nat) : (carbon? m g depth i).isSome = true ↔
      (LocalIsotopeCarbonReport.at? m g depth i).isSome = true ∨
      (RingTerminalPair.check? m i).isSome = true ∨
      (derive? m g depth m.atomCount [i]).isSome = true ∨ (FrozenSigned.check? m g depth i).isSome = true ∨
      (RingSilentPair.check? m depth i).isSome = true := by
    cases h : LocalIsotopeCarbonReport.at? m g depth i <;> cases t : RingTerminalPair.check? m i <;>
      cases result : derive? m g depth m.atomCount [i] <;>
      cases frozen : FrozenSigned.checkWith? (cacheAtRoot m g depth i) i <;>
      simp [carbon?,h,t,cacheAtRoot_exact,result,FrozenSigned.check?,frozen]
  simp_rw [← row]
  induction ids with
  | nil => simp [collect]
  | cons i ids ih =>
    cases h : carbon? m g depth i <;> cases t : collect m g depth ids <;>
      simp [collect,h,t] at ih ⊢ <;> tauto

def report? (input : LocalizedChemicalRing.Input) (depth : Nat) : Option (Report input depth) := do
  let rows ← collect input.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified)
    depth (RingCarbonReport.carbons input.molecule)
  return ⟨rows.val,rows.property⟩

/-- Public projection computes precisely the labels of the individual checked
carbon rows, in their original molecular order. Failure at one site propagates. -/
theorem report_labels (input : LocalizedChemicalRing.Input) (depth : Nat) :
    (report? input depth).map Report.labels =
      (RingCarbonReport.carbons input.molecule).mapM (m := Option) (fun i =>
        (carbon? input.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified) depth i).map
          fun v => (i,v.label)) := by
  let m := input.molecule
  let g := LocalizedChemicalRingPhysicalSense.inputGeometry input.certified
  have projection (ids : List Nat) :
      (collect m g depth ids).map (fun rs => rs.val.map fun x => (x.1,x.2.label)) =
        ids.mapM (m := Option) (fun i => (carbon? m g depth i).map fun v => (i,v.label)) := by
    induction ids with
    | nil => rfl
    | cons i ids ih =>
      cases h : carbon? m g depth i <;> cases t : collect m g depth ids <;>
        simp [collect,h,t,List.mapM_cons,← ih]
  have result := projection (RingCarbonReport.carbons m)
  unfold report? Report.labels
  change ((collect m g depth (RingCarbonReport.carbons m)).bind _).map _ = _
  cases t : collect m g depth (RingCarbonReport.carbons m) <;> simpa [t] using result

/-- Direct and recursively signed proofs may be used at different carbons
of the same report. The inventory is exactly the carbon atoms of the input. -/
theorem report?_isSome_iff (input : LocalizedChemicalRing.Input) (depth : Nat) :
    (report? input depth).isSome = true ↔
      ∀ i ∈ RingCarbonReport.carbons input.molecule,
        let g := LocalizedChemicalRingPhysicalSense.inputGeometry input.certified
        (LocalIsotopeCarbonReport.at? input.molecule g depth i).isSome = true ∨
          (RingTerminalPair.check? input.molecule i).isSome = true ∨
          (derive? input.molecule g depth input.molecule.atomCount [i]).isSome = true ∨
          (FrozenSigned.check? input.molecule g depth i).isSome = true ∨
          (RingSilentPair.check? input.molecule depth i).isSome = true := by
  rw [← collect_isSome]
  unfold report?
  cases collect input.molecule _ depth _ <;> rfl

/-- For any ring topology or observation depth, if every carbon has an
identical pair of singly attached terminal atoms, the public procedure returns
an exact all-refusal report. The hypotheses concern atom records and bonds. -/
theorem terminal_carbon_report (input : LocalizedChemicalRing.Input) (depth : Nat)
    (covered : ∀ i ∈ RingCarbonReport.carbons input.molecule,
      ∃ h : i < input.molecule.atomCount, RingTerminalPair.Focus input.molecule i ∧
        ∃ a b, RingTerminalPair.Equivalent input.molecule ⟨i,h⟩ a b) :
    ∃ r : Report input depth, report? input depth = some r ∧
      r.labels = (RingCarbonReport.carbons input.molecule).map (fun i => (i,none)) := by
  have terminal := fun i hi => (RingTerminalPair.check?_isSome_iff _ i).mpr (covered i hi)
  have complete := (report?_isSome_iff input depth).mpr fun i hi => Or.inr (Or.inl (terminal i hi))
  let r := (report? input depth).get complete
  have got : report? input depth = some r := (Option.some_get _).symm
  refine ⟨r,got,?_⟩
  let m := input.molecule
  let g := LocalizedChemicalRingPhysicalSense.inputGeometry input.certified
  have rows (ids : List Nat) (selected : ∀ i ∈ ids, (RingTerminalPair.check? m i).isSome = true)
      (rs : {rows : List ((i : Nat) × CarbonVerdict m g depth i) // rows.map Sigma.fst = ids})
      (found : collect m g depth ids = some rs) :
      rs.val.map (fun x => (x.1,x.2.label)) = ids.map (fun i => (i,none)) := by
    induction ids with
    | nil => simpa [collect] using congrArg (fun q => q.map (fun xs => xs.val.map (fun x => (x.1,x.2.label)))) found.symm
    | cons i ids ih =>
      obtain ⟨c,eqn⟩ := Option.isSome_iff_exists.mp (selected i List.mem_cons_self)
      cases rem : collect m g depth ids with
      | none => simp [collect,carbon?,eqn,rem] at found
      | some tail =>
        have rest := ih (fun j hj => selected j (List.mem_cons_of_mem _ hj)) tail rem
        simp [collect,carbon?,eqn,rem] at found
        subst rs
        exact congrArg (List.cons (i,none)) rest
  cases h : collect m g depth (RingCarbonReport.carbons m) with
  | none => simp [report?,m,g,h] at got
  | some rs =>
    have data := rows _ terminal rs h
    change (do let xs ← collect m g depth (RingCarbonReport.carbons m)
               pure (⟨xs.val,xs.property⟩ : Report input depth)) = some r at got
    simp [h] at got
    rw [← got]
    exact data

/-- The independent priority evidence for a listed hand. For a recursive
decision the complete molecular step and its signed premises are retained. -/
inductive PriorityOrder (m : RawMolecule) (g : Geometry) (depth i : Nat) : List Nat → Nat → Prop where
  | atomic {a} (ranked : atomicOrder? m [i] depth = some a) : PriorityOrder m g depth i a 0
  | terminal (r : LocalIsotopeCarbonReport.Ranking m i) : PriorityOrder m g depth i r.order 0
  | frozen (c : FrozenSigned.Certificate (cacheAtRoot m g depth i) [i]) {a n}
      (order : c.frame.step.orders a n) : PriorityOrder m g depth i a n
  | signed (c : Certificate m g [i]) {a n} (order : c.step.orders a n) : PriorityOrder m g depth i a n

theorem CarbonVerdict.assignment {m g depth i} (row : CarbonVerdict m g depth i) {letter}
    (assigned : row.label = some letter) :
    ∃ a n hand, PriorityOrder m g depth i a n ∧ readback? g a = some hand ∧
      letter = (if n % 2 = 0 then .chiral hand else .pseudoasymmetric (pseudoRSOfRS hand)) := by
  cases row with
  | direct v =>
    cases v with
    | hydrogenTie => contradiction
    | atomic v =>
      cases v with
      | hydrogens => contradiction
      | strict a ranked r observed =>
        obtain ⟨letter,raw,_⟩ := AtomicCarbonReport.Verdict.strict_letter ranked observed
        exact ⟨a,0,r.actual,.atomic ranked,raw,Option.some.inj (assigned.symm.trans letter)⟩
    | isotope ranking r observed =>
      obtain ⟨letter,raw,_⟩ := LocalIsotopeCarbonReport.isotope_letter (depth := depth) ranking observed
      exact ⟨_,0,r.actual,.terminal ranking,raw,Option.some.inj (assigned.symm.trans letter)⟩
  | terminal | silent => contradiction
  | frozen c =>
    change c.frame.step.reading?.bind Reading.label = some letter at assigned
    obtain ⟨r,actual,label⟩ := Option.bind_eq_some_iff.mp assigned
    obtain ⟨a,n,basis,raw,correct⟩ := c.assignment actual
    exact ⟨a,n,r.actual,.frozen c basis,raw,Option.some.inj (label.symm.trans correct)⟩
  | recursive c =>
    change c.step.reading?.bind Reading.label = some letter at assigned
    obtain ⟨r,actual,label⟩ := Option.bind_eq_some_iff.mp assigned
    obtain ⟨a,n,basis,raw,correct⟩ := c.step.chemical_letter actual
    exact ⟨a,n,r.actual,.signed c basis,raw,Option.some.inj (label.symm.trans correct)⟩

/-- Each assigned report entry gives a molecular order, spatial hand and
reversal count that determine both its letter and its case. -/
theorem Report.assignment {input depth} (r : Report input depth) {i letter}
    (member : (i,some letter) ∈ r.labels) :
    let g := LocalizedChemicalRingPhysicalSense.inputGeometry input.certified
    ∃ a n hand, PriorityOrder input.molecule g depth i a n ∧ readback? g a = some hand ∧
      letter = (if n % 2 = 0 then .chiral hand else .pseudoasymmetric (pseudoRSOfRS hand)) := by
  obtain ⟨⟨j,row⟩,_,same⟩ := List.mem_map.mp member
  obtain rfl : j = i := congrArg Prod.fst same
  exact row.assignment (congrArg Prod.snd same)

/-- An omitted letter has an equivalent pair of terminal ligands or a
recursive molecular refusal whose publications replay in frozen batches. -/
theorem Report.refusal {input depth} (r : Report input depth) {i}
    (member : (i,none) ∈ r.labels) :
    let m := input.molecule
    let g := LocalizedChemicalRingPhysicalSense.inputGeometry input.certified
    (∃ h : RingCarbonReport.HydrogenPair m i, ⟨i,.direct (.atomic (.hydrogens h))⟩ ∈ r.rows) ∨
    (∃ h : LocalIsotopeCarbonReport.HydrogenTie m i, ⟨i,.direct (.hydrogenTie h)⟩ ∈ r.rows) ∨
    (∃ pair : RingTerminalPair.Certificate m i, ⟨i,.terminal pair⟩ ∈ r.rows) ∨
    (∃ c : Certificate m g [i], ⟨i,.recursive c⟩ ∈ r.rows ∧ c.step.refuses ∧
      ∀ x ∈ c.published, Derives m g (c.published.filter (fun y => x.1.length < y.1.length)) x.1 x.2) ∨
    (∃ pair : RingSilentPair.Certificate m depth i, ⟨i,.silent pair⟩ ∈ r.rows) ∨
    (∃ c : FrozenSigned.Certificate (cacheAtRoot m g depth i) [i], ⟨i,.frozen c⟩ ∈ r.rows ∧
      c.frame.step.refuses ∧ ∀ x ∈ c.frame.step.inputs,
        c.table.entries.lookup x.1 = some x.2 ∧ FrozenSigned.Published (cacheAtRoot m g depth i)
          c.table.entries x.1 x.2) := by
  obtain ⟨⟨j,row⟩,listed,same⟩ := List.mem_map.mp member
  obtain rfl : j = i := congrArg Prod.fst same
  have label : row.label = none := congrArg Prod.snd same
  cases row with
  | direct v =>
    cases v with
    | hydrogenTie pair => exact Or.inr (Or.inl ⟨pair,listed⟩)
    | isotope order reading seen =>
      have letter := (LocalIsotopeCarbonReport.isotope_letter (depth := depth) order seen).1
      cases label.symm.trans letter
    | atomic v =>
      cases v with
      | hydrogens pair => exact Or.inl ⟨pair,listed⟩
      | strict order ranked reading seen =>
        have letter := (AtomicCarbonReport.Verdict.strict_letter ranked seen).1
        cases label.symm.trans letter
  | terminal pair => exact Or.inr (Or.inr (Or.inl ⟨pair,listed⟩))
  | silent pair => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨pair,listed⟩))))
  | recursive c =>
    change c.step.reading?.bind Reading.label = none at label
    cases h : c.step.reading? with
    | none => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c,listed,c.step.reading?_eq_none_iff.mp h,fun _ hx => c.frozen_batch hx⟩)))
    | some reading => simp [h,Reading.label,caseFromMirror?] at label
  | frozen c =>
    change c.frame.step.reading?.bind Reading.label = none at label
    cases h : c.frame.step.reading? with
    | some reading => simp [h,Reading.label,caseFromMirror?] at label
    | none =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨c,listed,c.refusal.mp h,fun _ hx =>
        ⟨(c.input_published hx).1,(c.input_published hx).2.2.2⟩⟩))))


end TetraStereo.Engine.RingChemicalPriority.RecursiveSigned

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.Certificate.byDistance_replays
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.Certificate.frozen_batch
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.report?_isSome_iff

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.Report.assignment

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.Report.refusal

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.terminal_carbon_report

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RecursiveSigned.report_labels
