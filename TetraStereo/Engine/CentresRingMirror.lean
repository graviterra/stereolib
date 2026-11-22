import TetraStereo.Engine.CentresRingDerived

set_option autoImplicit false

namespace TetraStereo.Engine.CentresRing.MirrorCasing
open OneCenter CertifiedLocalizedCIPInput
open LocalizedGenericMarkedRecalculation (caseFromMirror?)
open LocalizedChemicalRing (Input Report)

/-- Handedness of the reported priority order, independent of the sort's case bit. -/
def hand : LocalizedAuxiliaryLabel → RS
  | .chiral h => h
  | .pseudoasymmetric .r => .R
  | .pseudoasymmetric .s => .S

/-- Chemical reflection exchanges the uppercase enantiomers and fixes a
lowercase descriptor. This acts on the descriptor as a whole. -/
def reflectLabel : LocalizedAuxiliaryLabel → LocalizedAuxiliaryLabel
  | .chiral h => .chiral h.swap
  | .pseudoasymmetric h => .pseudoasymmetric h

/-- Exactly one cased label realizes the two absolute readings and the mirror law. -/
theorem unique_case (a b : RS) :
    ∃! d : LocalizedAuxiliaryLabel, hand d = a ∧ hand (reflectLabel d) = b := by
  cases a <;> cases b
  all_goals first
    | refine ⟨.chiral .R, by decide, ?_⟩
    | refine ⟨.chiral .S, by decide, ?_⟩
    | refine ⟨.pseudoasymmetric .r, by decide, ?_⟩
    | refine ⟨.pseudoasymmetric .s, by decide, ?_⟩
  all_goals rintro (h | h) eq <;> cases h <;> first | rfl | simp [hand, reflectLabel, RS.swap] at eq

theorem case_exact (a b : RS) (d : LocalizedAuxiliaryLabel) :
    caseFromMirror? (some a) (some b) = some d ↔
      hand d = a ∧ hand (reflectLabel d) = b := by
  cases a <;> cases b <;> rcases d with h | h <;> cases h <;> decide

/-- Exchanging the two spatial readings implements the chemical mirror
convention for all successful assignments and all missing readings. -/
theorem case_reversed (a b : Option RS) :
    caseFromMirror? b a = (caseFromMirror? a b).map reflectLabel := by
  rcases a with _ | a <;> rcases b with _ | b <;> try rfl
  cases a <;> cases b <;> rfl

section LinkedPairs
open LocalizedGenericMarkedRecalculation (Geometry readback? mirror readback_mirror)
open LocalizedMarkedTerminalGaugeSwap (readback_swap12 readback_swap34 readback_swap13 readback_swap24)

/-- Ligands a and c share one ring, b and d the other. Selecting a senior
ligand also selects its partner in the junior pair. -/
def linkedOrder (second : Bool) (a b c d : Nat) : List Nat :=
  if second then [b,a,d,c] else [a,b,c,d]

private theorem linked_read (g : Geometry) (k : Bool) (a b c d : Nat) :
    readback? g (linkedOrder k a b c d) = readback? g [a,b,c,d] := by
  cases k with
  | false => rfl
  | true =>
    change readback? g [b,a,d,c] = _
    rw [readback_swap34 g b a c d,readback_swap12 g a b c d]
    cases readback? g [a,b,c,d] with
    | none => rfl
    | some h => cases h <;> rfl

private theorem exchange_pairs (g : Geometry) (a b c d : Nat) :
    readback? g [c,d,a,b] = readback? g [a,b,c,d] := by
  rw [readback_swap24 g c b a d,readback_swap13 g a b c d]
  cases readback? g [a,b,c,d] with
  | none => rfl
  | some h => cases h <;> rfl

/-- When reflection exchanges senior and junior pairs, with the same two ring
partnerships, both independent choices of senior ligand give uppercase for
every nondegenerate reading. Missing or coplanar coordinates give none. -/
theorem linked_pairs_uppercase (g : Geometry) (x y : Bool) (a b c d : Nat) :
    caseFromMirror? (readback? g (linkedOrder x a b c d))
      (readback? (mirror g) (linkedOrder y c d a b)) =
        (readback? g [a,b,c,d]).map (.chiral ·) := by
  rw [linked_read,linked_read,readback_mirror,exchange_pairs g a b c d]
  cases readback? g [a,b,c,d] with
  | none => rfl
  | some h => cases h <;> rfl
end LinkedPairs

structure Entry where
  atom : Nat
  original : Option LocalizedAuxiliaryLabel
  reflected : Option LocalizedAuxiliaryLabel

def Entry.descriptor (e : Entry) : Option LocalizedAuxiliaryLabel :=
  caseFromMirror? (e.original.map hand) (e.reflected.map hand)

/-- Each row retains both source decisions for auditing. An assignment available
on just one geometry is a verification error. A shared refusal stays a refusal. -/
inductive Aligned : List Entry → Report → Report → Prop where
  | nil : Aligned [] [] []
  | cons {es a b} (e : Entry) : e.original.isSome = e.reflected.isSome → Aligned es a b →
    Aligned (e :: es) ((e.atom,e.original) :: a) ((e.atom,e.reflected) :: b)

theorem Aligned.member {es a b} (h : Aligned es a b) {e : Entry} (mem : e ∈ es) :
    (e.atom,e.original) ∈ a ∧ (e.atom,e.reflected) ∈ b := by
  induction h with
  | nil => simp at mem
  | cons row _ _ ih =>
    rcases List.mem_cons.mp mem with rfl | tail
    · exact ⟨List.mem_cons_self,List.mem_cons_self⟩
    · exact ⟨List.mem_cons_of_mem _ (ih tail).1,List.mem_cons_of_mem _ (ih tail).2⟩

theorem hand_classify (r : RS) (n : Nat) : hand (classifyTetrahedralRSPseudo r n) = r := by
  cases r <;> by_cases h : n = 1 <;> simp [classifyTetrahedralRSPseudo,h,hand,pseudoRSOfRS]

private def align : (a b : Report) → Except String {es : List Entry // Aligned es a b}
  | [], [] => .ok ⟨[],.nil⟩
  | (i,u)::a, (j,v)::b => do
    if eq : i = j then
      if same : u.isSome = v.isSome then
        let tail ← align a b
        let e : Entry := ⟨i,u,v⟩
        return ⟨e :: tail.val,by subst j; exact Aligned.cons e same tail.property⟩
      else throw s!"assignment availability changed under reflection at atom {i}"
    else throw "center order changed under reflection"
  | _, _ => .error "center inventories differ"

def reflectGeometry (g : SpatialConfiguration) : SpatialConfiguration :=
  ⟨g.positions.map CartesianPoint3.reflectX⟩

structure Checked (input : Input) (cs : List Nat) where
  reflectedInput : Input
  admission : LocalizedChemicalRing.admitRawSpatial? input.molecule (reflectGeometry input.spatial) =
    some reflectedInput
  original : Molecular.SourceChecked input cs
  reflected : Molecular.SourceChecked reflectedInput cs
  entries : List Entry
  aligned : Aligned entries original.molecular.replay.report reflected.molecular.replay.report

def Checked.report {input cs} (c : Checked input cs) : Report :=
  c.entries.map fun e => (e.atom,e.descriptor)

/-- A corrected success comes with two priority orders read on the actual
molecule and its admitted reflection. These readings uniquely determine its case. -/
theorem Checked.readings {input cs} (c : Checked input cs) {atom d}
    (mem : (atom,some d) ∈ c.report) :
    ∃ t ∈ c.original.molecular.replay.traces, t.atom = atom ∧ ∃ r : Ranking,
      finalRanking input cs t = .ok (some r) ∧
      LocalizedGenericMarkedRecalculation.readback?
        (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified) r.order = some (hand d) ∧
      ∃ u ∈ c.reflected.molecular.replay.traces, u.atom = atom ∧ ∃ s : Ranking,
        finalRanking c.reflectedInput cs u = .ok (some s) ∧
        LocalizedGenericMarkedRecalculation.readback?
          (LocalizedChemicalRingPhysicalSense.inputGeometry c.reflectedInput.certified) s.order =
            some (hand (reflectLabel d)) := by
  obtain ⟨e,hm,eq⟩ := List.mem_map.mp mem
  change (e.atom,e.descriptor) = (atom,some d) at eq
  have found := (Prod.mk.inj eq).2
  obtain ⟨left,right⟩ := c.aligned.member hm
  cases l : e.original with
  | none => simp [Entry.descriptor,l,caseFromMirror?] at found
  | some x =>
    cases h : e.reflected with
    | none => simp [Entry.descriptor,h,l,caseFromMirror?] at found
    | some y =>
      have casesEq := (case_exact (hand x) (hand y) d).mp (by simpa [Entry.descriptor,l,h] using found)
      rw [l] at left
      rw [h] at right
      obtain ⟨t,ht,ti,r,a,hr,ha,hx,_⟩ := success_evidence c.original.molecular.replay.checked left
      obtain ⟨u,hu,ui,s,b,hs,hb,hy,_⟩ := success_evidence c.reflected.molecular.replay.checked right
      exact ⟨t,ht,ti.trans (Prod.mk.inj eq).1,r,hr,by simpa [casesEq.1,← hx,hand_classify] using ha,
        u,hu,ui.trans (Prod.mk.inj eq).1,s,hs,by simpa [casesEq.2,← hy,hand_classify] using hb⟩

/-- A two-geometry projection of independently verified molecular priority
readings. Both source reports remain available, including their original case. -/
def check (input : Input) (forward backward : Molecular.SourceReceipt)
    (cs : List Nat := inventory input) : Except String (Checked input cs) := do
  let a ← Molecular.checkSourceReceipt input forward cs
  match hm : LocalizedChemicalRing.admitRawSpatial? input.molecule (reflectGeometry input.spatial) with
  | none => throw "reflected spatial input failed admission"
  | some other =>
    let b ← Molecular.checkSourceReceipt other backward cs
    let es ← align a.molecular.replay.report b.molecular.replay.report
    return ⟨other,hm,a,b,es.val,es.property⟩

/-- Live counterpart of the offline two-geometry check. The two calls use
the same configured source adapter and center inventory. -/
def analyze (input : Input) (cs : List Nat := inventory input)
    (classpath : String := ".cache/centres10/classes:.cache/centres10/guava.jar") :
    IO (Except String (Checked input cs)) := do
  match h : LocalizedChemicalRing.admitRawSpatial? input.molecule (reflectGeometry input.spatial) with
  | none => return .error "reflected spatial input failed admission"
  | some other =>
    match ← Molecular.analyze input cs classpath with
    | .error msg => return .error msg
    | .ok a =>
      let second ← Molecular.analyze other cs classpath
      return do
        let b ← second
        let es ← align a.molecular.replay.report b.molecular.replay.report
        return ⟨other,h,a,b,es.val,es.property⟩

end TetraStereo.Engine.CentresRing.MirrorCasing
assert_kernel_only TetraStereo.Engine.CentresRing.MirrorCasing.unique_case
assert_kernel_only TetraStereo.Engine.CentresRing.MirrorCasing.case_exact
assert_kernel_only TetraStereo.Engine.CentresRing.MirrorCasing.check
assert_kernel_only TetraStereo.Engine.CentresRing.MirrorCasing.Checked.readings
assert_kernel_only TetraStereo.Engine.CentresRing.MirrorCasing.linked_pairs_uppercase
assert_kernel_only TetraStereo.Engine.CentresRing.MirrorCasing.case_reversed
