import TetraStereo.Engine.RingReferenceSchedule
import TetraStereo.Engine.CentresRingDerived

set_option autoImplicit false

namespace TetraStereo.Engine.CentresRing.ComparisonAgreement
open OneCenter LocalizedGenericMarkedRecalculation
open RingChemicalPriority RingChemicalPriority.Recursive
open Molecular (Rule Call)
open InventoryPriority (Entries)

structure Answer where
  rule : Option Rule
  value : Int
  deriving DecidableEq, Repr

private def signed (o : Ordering) (size : Int) :=
  match o with | .eq => 0 | .gt => size | .lt => -size

def constitutionalAnswer {m p i j} (c : IsotopePriority.IncidentComparison m p i j) : Answer :=
  ⟨c.rule?.map (fun | .atomicNumber => .atomicNumber | .duplicateOrigin _ => .duplicate
                       | .isotopeMass _ => .isotope),signed c.ordering 1⟩

/-- Predict the first active rule and signed magnitude from independent
two-geometry molecular evidence. Reference priority is consulted only
when the earlier unmarked rules give an exact tie. -/
def answer? {m g p i j} (b : ReferenceFrame.Basis m g p i j) (mark : Option Nat) : Option Answer := do
  match b with
  | .atomic _ _ _ _ _ w _ => return ⟨some .atomicNumber,if w then 1 else -1⟩
  | .constitution c _ => return constitutionalAnswer c
  | .fourth _ w d =>
    let rule := match d with
      | .classes _ => Rule.stereoClass
      | .stereo stage .. => if stage == .fourB then Rule.likePair else Rule.lower
    return ⟨some rule,if w then 1 else -1⟩
  | .stereo _ w .. => return ⟨some .handedPair,if w then 2 else -2⟩
  | .tied pair _ =>
    let some k := mark | return ⟨none,0⟩
    let v := (← pair.atMark? k).verdict.ordering
    return ⟨if v = .eq then none else some .reference,signed v 1⟩

private def usesStereo {m g p i j} : ReferenceFrame.Basis m g p i j → Bool
  | .atomic .. | .constitution .. => false
  | _ => true

def codeAt (visible : List PairList.Publication) (p : List Nat) :=
  (visible.find? (fun f => f.path == p)).map (·.code)

private def inputCode (x : Option Reading) := labelCode (x.bind Reading.label)

/-- The release reads an unpublished path as "-". It can match a missing
row only when the molecular certificate independently derives absence. -/
abbrev ReadAgrees (observed : Option String) (verdict : Option Reading) : Prop :=
  observed = some (inputCode verdict) ∨ observed = none ∧ verdict = none

theorem ReadAgrees.source_value {observed verdict} (h : ReadAgrees observed verdict) :
    observed.getD "-" = labelCode (verdict.bind Reading.label) := by
  rcases h with rfl | ⟨rfl,rfl⟩ <;> rfl

theorem ReadAgrees.positive {observed r} (h : ReadAgrees observed (some r)) :
    observed = some (labelCode r.label) := by
  rcases h with h | ⟨_,h⟩
  · exact h
  · cases h

/-- Each molecular reading matches the value consulted by the source.
Every nonempty source label on a consulted arm occurs in the molecular inventory. -/
structure Snapshot {m g p i j} (b : ReferenceFrame.Basis m g p i j) (visible : List PairList.Publication) : Prop where
  read : ∀ x ∈ b.inputs, ReadAgrees (codeAt visible x.1) x.2
  covered : usesStereo b = true → ∀ f ∈ visible, f.code ≠ "-" →
    (p ++ [i] <+: f.path ∨ p ++ [j] <+: f.path) → ∃ x ∈ b.inputs, x.1 = f.path ∧ inputCode x.2 = f.code

def snapshot? {m g p i j} (b : ReferenceFrame.Basis m g p i j) (visible : List PairList.Publication) :
    Option (PLift (Snapshot b visible)) := do
  if h : ∀ x ∈ b.inputs, ReadAgrees (codeAt visible x.1) x.2 then
    if total : usesStereo b = true → ∀ f ∈ visible, f.code ≠ "-" →
        (p ++ [i] <+: f.path ∨ p ++ [j] <+: f.path) → ∃ x ∈ b.inputs, x.1 = f.path ∧ inputCode x.2 = f.code then
      return ⟨⟨h,total⟩⟩
  none

inductive Ground (m : RawMolecule) (g : Geometry) (c : Call) : Answer → Type where
  | constitution (rank : IsotopePriority.IncidentComparison m c.frame.focus c.comparison.left c.comparison.right)
      (applies : c.frame.constitutional = true ∨ rank.ordering ≠ .eq) : Ground m g c (constitutionalAnswer rank)
  | molecular (cert : ReferenceDerivation.Certificate m g c.frame.focus)
      (b : ReferenceFrame.Basis m g c.frame.focus c.comparison.left c.comparison.right)
      (full : c.frame.constitutional = false) (snapshot : Snapshot b c.frame.visible)
      (used : ∀ x ∈ b.inputs, cert.published.lookup x.1 = some x.2)
      {a : Answer} (result : answer? b c.frame.mark = some a) : Ground m g c a

structure Agreement (m : RawMolecule) (g : Geometry) (root : Nat) (c : Call) where
  sameMolecule : c.frame.molecule = m
  atRoot : c.frame.focus.head? = some root
  ground : Ground m g c ⟨c.winner,c.comparison.value⟩

private def ground? (m : RawMolecule) (g : Geometry) (c : Call) (depth : Nat)
    (rows : ReferenceDerivation.Cache m g depth) :
    Option ((a : Answer) × Ground m g c a) := do
  let i := c.comparison.left
  let j := c.comparison.right
  if let some r := IsotopePriority.compareIncident? m c.frame.focus i j then
    if ok : c.frame.constitutional = true ∨ r.ordering ≠ .eq then return ⟨_,.constitution r ok⟩
  if full : c.frame.constitutional = false then
    let cert ← rows.read c.frame.focus
    let frame ← cert.frame? depth
    let row ← frame.rows.find? (fun row => row.i == i && row.j == j)
    if ri : row.i = i then
      if rj : row.j = j then
        let b : ReferenceFrame.Basis m g c.frame.focus i j := ri ▸ rj ▸ row.basis
        let ⟨snap⟩ ← snapshot? b c.frame.visible
        if used : ∀ x ∈ b.inputs, cert.published.lookup x.1 = some x.2 then
          let ⟨a,ha⟩ ← (answer? b c.frame.mark).attach
          return ⟨a,.molecular cert b full snap used ha⟩
  none

private def checkCallWith? (m : RawMolecule) (g : Geometry) (root depth : Nat)
    (rows : ReferenceDerivation.Cache m g depth) (c : Call) : Option (Agreement m g root c) := do
  if binding : c.frame.molecule = m ∧ c.frame.focus.head? = some root then
    let ⟨a,evidence⟩ ← ground? m g c depth rows
    if exactValue : a = ⟨c.winner,c.comparison.value⟩ then
      return ⟨binding.1,binding.2,exactValue ▸ evidence⟩
  none

def checkCall? (m : RawMolecule) (g : Geometry) (root depth : Nat) (c : Call) :=
  checkCallWith? m g root depth [] c

inductive Each {α : Type} (W : α → Type) : List α → Type where
  | nil : Each W []
  | cons {x xs} (head : W x) (tail : Each W xs) : Each W (x :: xs)

def traverse {α : Type} {W : α → Type} (f : (a : α) → Option (W a)) :
    (xs : List α) → Option (Each W xs)
  | [] => some .nil
  | x :: xs => do return .cons (← f x) (← traverse f xs)

theorem Each.member {α W xs} (d : @Each α W xs) {x} (hx : x ∈ xs) : Nonempty (W x) := by
  induction d with
  | nil => contradiction
  | cons head _ ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · exact ⟨head⟩
    · exact ih h

structure Trace (m : RawMolecule) (g : Geometry) (t : CenterTrace) where
  replay : Molecular.Evidence m g t
  comparisons : Each (Agreement m g t.atom) replay.derived.calls

def checkTrace? (m : RawMolecule) (g : Geometry) (t : CenterTrace) (depth : Nat) : Option (Trace m g t) := do
  let e ← (Molecular.certify m g t).toOption
  let rows := ReferenceDerivation.cacheAtRoot m g depth t.atom (t.discovered.map List.reverse)
  return ⟨e,← traverse (checkCallWith? m g t.atom depth rows) e.derived.calls⟩

/-- Preserve the chronological index even when several calls share their
operands and integer. The call's frame retains its visible store and mark. -/
theorem Trace.at_index {m g t} (s : Trace m g t) {n : Nat} {cmp : Comparison} (logged : (Molecular.chronological t)[n]? = some cmp) :
    ∃ c, s.replay.derived.calls[n]? = some c ∧ c.comparison = cmp ∧ Nonempty (Agreement m g t.atom c) := by
  rw [← s.replay.coverage,List.getElem?_map] at logged
  obtain ⟨c,found,eqn⟩ := Option.map_eq_some_iff.mp logged
  exact ⟨c,found,eqn,s.comparisons.member (List.mem_of_getElem? found)⟩

structure Auxiliary (m : RawMolecule) (g : Geometry) (t : CenterTrace) (u : Update) where
  path : List Nat
  located : t.discovered[u.index]? = some path.reverse
  certificate : ReferenceDerivation.Certificate m g path
  exactLabel : inputCode certificate.verdict = u.label

private def checkAuxiliaryWith? (m : RawMolecule) (g : Geometry) (t : CenterTrace) (depth : Nat)
    (rows : ReferenceDerivation.Cache m g depth) (u : Update) :
    Option (Auxiliary m g t u) := do
  let ⟨rev,found⟩ ← (t.discovered[u.index]?).attach
  let cert ← rows.read rev.reverse
  if exactLabel : inputCode cert.verdict = u.label then
    return ⟨rev.reverse,by simpa using found,cert,exactLabel⟩
  none

def checkAuxiliary? (m : RawMolecule) (g : Geometry) (t : CenterTrace) (depth : Nat) (u : Update) :=
  checkAuxiliaryWith? m g t depth [] u

/-- All chronological comparisons and every auxiliary update match. The
root verdict is computed independently, so a casing discrepancy remains
observable even after every signed integer in the trace is justified. -/
structure Diagnosis (m : RawMolecule) (g : Geometry) (t : CenterTrace) extends Trace m g t where
  updates : Each (Auxiliary m g t) t.updates
  root : ReferenceDerivation.Certificate m g [t.atom]

private def diagnoseEvidence {m g t} (e : Molecular.Evidence m g t) (depth : Nat) :
    Option (Diagnosis m g t) := do
  let rows := ReferenceDerivation.cacheAtRoot m g depth t.atom (t.discovered.map List.reverse)
  let calls ← traverse (checkCallWith? m g t.atom depth rows) e.derived.calls
  return ⟨⟨e,calls⟩,← traverse (checkAuxiliaryWith? m g t depth rows) t.updates,← rows.read [t.atom]⟩

def diagnose? (m : RawMolecule) (g : Geometry) (t : CenterTrace) (depth : Nat) :
    Option (Diagnosis m g t) := do
  diagnoseEvidence (← (Molecular.certify m g t).toOption) depth

def Diagnosis.chemicalCode {m g t} (d : Diagnosis m g t) := inputCode d.root.verdict
def Diagnosis.agrees {m g t} (d : Diagnosis m g t) := d.chemicalCode == t.label

theorem Diagnosis.auxiliary_at {m g t} (d : Diagnosis m g t) {u} (member : u ∈ t.updates) :
    ∃ p, ∃ c : ReferenceDerivation.Certificate m g p, t.discovered[u.index]? = some p.reverse ∧
      labelCode (c.verdict.bind Reading.label) = u.label := by
  obtain ⟨e⟩ := d.updates.member member
  exact ⟨e.path,e.certificate,e.located,e.exactLabel⟩

/-- Check the bound molecular input and source trace inventory before
auditing every requested center at the supplied geometry. -/
structure DiagnosedReceipt (input : LocalizedChemicalRing.Input) (cs : List Nat) where
  replay : Result input cs
  centers : Each (Diagnosis input.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified)) replay.traces

def diagnoseReceipt (input : LocalizedChemicalRing.Input) (packet : Receipt) (depth : Nat)
    (cs : List Nat := inventory input) : Except String (DiagnosedReceipt input cs) := do
  let r ← checkReceipt input packet cs
  let some centers := traverse (fun t => diagnose? input.molecule
    (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified) t depth) r.traces
    | throw "a comparison, auxiliary publication or molecular root could not be certified"
  return ⟨r,centers⟩

/-- The same trace inventory must pass both the release rule-prefix check
and the independent molecular checks. -/
structure DiagnosedSource (input : LocalizedChemicalRing.Input) (cs : List Nat) where
  source : Molecular.SourceChecked input cs
  centers : Each (Diagnosis input.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified))
    source.molecular.replay.traces

private def diagnoseAll {m g} (depth : Nat) :
    (es : List (Sigma (Molecular.Evidence m g))) → Option (Each (Diagnosis m g) (es.map Sigma.fst))
  | [] => some .nil
  | ⟨_,e⟩ :: rest => do return .cons (← diagnoseEvidence e depth) (← diagnoseAll depth rest)

def diagnoseSource (input : LocalizedChemicalRing.Input) (packet : Molecular.SourceReceipt) (depth : Nat)
    (cs : List Nat := inventory input) : Except String (DiagnosedSource input cs) := do
  let source ← Molecular.checkSourceReceipt input packet cs
  let some centers := diagnoseAll depth source.molecular.derivations
    | throw "a source comparison, auxiliary publication or molecular root could not be certified"
  return ⟨source,source.molecular.inventory_eq ▸ centers⟩

/-- A caller requiring exact chemical and release agreement can obtain it
only when both independently computed root labels agree on every row. -/
structure Conforming (m : RawMolecule) (g : Geometry) (t : CenterTrace) extends Diagnosis m g t where
  exactRoot : toDiagnosis.chemicalCode = t.label

def requireAgreement {m g} {ts : List CenterTrace} :
    Each (Diagnosis m g) ts → Option (Each (Conforming m g) ts)
  | .nil => some .nil
  | .cons (x := t) d tail => do
    if h : d.chemicalCode = t.label then return .cons ⟨d,h⟩ (← requireAgreement tail)
    none

private theorem same_code_iff (source molecular : RS) (count reversals : Nat) :
    labelCode (some (if reversals % 2 = 0 then .chiral molecular else .pseudoasymmetric (pseudoRSOfRS molecular))) =
      labelCode (some (classifyTetrahedralRSPseudo source count)) ↔
      source = molecular ∧ (count = 1 ↔ reversals % 2 ≠ 0) := by
  cases source <;> cases molecular <;> by_cases one : count = 1 <;> by_cases even : reversals % 2 = 0 <;>
    simp [classifyTetrahedralRSPseudo,labelCode,pseudoRSOfRS,one,even]

/-- At every success in an audited public report, agreement is completely
determined by the two spatial hands and the relation between the release's
actual sort count and the molecular reversal parity. -/
theorem DiagnosedSource.assigned_agreement_iff {input cs} (result : DiagnosedSource input cs)
    {a label} (member : (a,some label) ∈ result.source.molecular.replay.report) :
    ∃ t ∈ result.source.molecular.replay.traces, t.atom = a ∧ ∃ rank sourceHand,
      finalRanking input cs t = .ok (some rank) ∧
      readback? (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified) rank.order = some sourceHand ∧
      ∃ d : Diagnosis input.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified) t,
        ∀ r, d.root.verdict = some r → ∃ order n,
          ReferenceDerivation.LetterBasis input.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified)
            d.root.published [t.atom] order n ∧
          readback? (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified) order = some r.actual ∧
          (d.chemicalCode = t.label ↔ sourceHand = r.actual ∧ (rank.pseudoCount = 1 ↔ n % 2 ≠ 0)) := by
  obtain ⟨t,ht,root,rank,hand,ranked,read,letter,code⟩ := success_evidence result.source.molecular.replay.checked member
  obtain ⟨d⟩ := result.centers.member ht
  refine ⟨t,ht,root,rank,hand,ranked,read,d,?_⟩
  intro r chosen
  have derived := d.root.derived
  rw [chosen] at derived
  obtain ⟨order,n,basis,physical,casing⟩ := derived.chemical_letter
  refine ⟨order,n,basis,physical,?_⟩
  simpa only [Diagnosis.chemicalCode,inputCode,chosen,Option.bind_some,casing,← code,← letter] using
    same_code_iff hand r.actual rank.pseudoCount n

end TetraStereo.Engine.CentresRing.ComparisonAgreement

assert_kernel_only TetraStereo.Engine.CentresRing.ComparisonAgreement.ReadAgrees.source_value
assert_kernel_only TetraStereo.Engine.CentresRing.ComparisonAgreement.ReadAgrees.positive
assert_kernel_only TetraStereo.Engine.CentresRing.ComparisonAgreement.Trace.at_index
assert_kernel_only TetraStereo.Engine.CentresRing.ComparisonAgreement.checkTrace?
assert_kernel_only TetraStereo.Engine.CentresRing.ComparisonAgreement.Diagnosis.auxiliary_at
assert_kernel_only TetraStereo.Engine.CentresRing.ComparisonAgreement.diagnoseReceipt
assert_kernel_only TetraStereo.Engine.CentresRing.ComparisonAgreement.diagnoseSource
assert_kernel_only TetraStereo.Engine.CentresRing.ComparisonAgreement.requireAgreement

assert_kernel_only TetraStereo.Engine.CentresRing.ComparisonAgreement.DiagnosedSource.assigned_agreement_iff
