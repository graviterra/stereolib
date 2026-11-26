import TetraStereo.Engine.RingSphereStore

/-! Finite physical signatures modulo independent terminal-twin exchanges.
Coordinates remain arbitrary rational tables; no reference evaluations are assumed. -/
set_option autoImplicit false
noncomputable section
namespace TetraStereo.Engine.RingPhysicalSignatures
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingHydrogenSpelling RingSpatialTransport RingNumberedHydrogenGeometry
open RingWrittenPHReadings RingPyramidalChoices
open RingActiveDistanceSchedule (height)

/-- Centers whose determinant cannot be repaired by one of the selected pair actions. -/
abbrev TetraIndex (i : Input) (ps : List (TwinPair i)) :=
  {c : i.certified.TetrahedralCenter // c ∉ ps.map TwinPair.c}
abbrev PIndex (i : Input) := {a : i.certified.Atom // RingPyramidalPublication.phosphorus i a = true}
abbrev Index (i : Input) (ps : List (TwinPair i)) := TetraIndex i ps ⊕ PIndex i

instance indexFinite (i : Input) (ps : List (TwinPair i)) : Finite (Index i ps) := by
  unfold Index TetraIndex PIndex
  infer_instance

/-- Missing or zero determinant, R, and S are three distinct physical readings. -/
def signCode : Option RS → Fin 3
  | none => 0
  | some .R => 1
  | some .S => 2

theorem signCode_injective : Function.Injective signCode := by
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases b <;> cases h
  | some a => cases a <;> cases b with
    | none => cases h
    | some b => cases b <;> first | rfl | cases h

abbrev Signature (i : Input) (ps : List (TwinPair i)) := Index i ps → Fin 3

/-- One determinant for each unpaired tetra center and each eligible P.
For P the one reading controls every slot order and both reflections. -/
def signature (i : Input) (ps : List (TwinPair i)) (x : SpatialConfiguration) : Signature i ps
  | .inl c => signCode (readback? (geometry x)
      (order (fun k => ((tetraEnumeration i c.val) k).val.val) 1))
  | .inr a => signCode (readback? (geometry x)
      (order (phosphorusFrameIds (phosphorusEnumeration i a.val a.property)) 1))

theorem signature_eq_iff (i : Input) (ps : List (TwinPair i)) (x w : SpatialConfiguration) :
    signature i ps x = signature i ps w ↔ OtherFramesAgree ps x w := by
  constructor
  · intro same
    refine ⟨?_,?_⟩
    · intro c outside
      have free : c ∉ ps.map TwinPair.c := by
        intro found
        obtain ⟨p,member,equal⟩ := List.mem_map.mp found
        exact outside p member equal
      exact signCode_injective (congrFun same (.inl ⟨c,free⟩))
    · intro a hp
      exact signCode_injective (congrFun same (.inr ⟨a,hp⟩))
  · intro off
    funext s
    cases s with
    | inl c =>
      apply congrArg signCode
      exact off.1 c.val (fun p member equal => c.property (List.mem_map.mpr ⟨p,member,equal⟩))
    | inr a => exact congrArg signCode (off.2 a.val a.property)

/-- A single molecular pair action transports the full materialized row list,
simultaneously at every root and every bounded prefix. -/
theorem signature_rows (i : Input) (ps : List (TwinPair i))
    (separate : (ps.map TwinPair.c).Nodup) (w x : SpatialConfiguration)
    (hw : w.positions.length = size i) (hx : x.positions.length = size i)
    (gw : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) = true)
    (gx : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) = true)
    (same : signature i ps x = signature i ps w) :
    ∃ g : GraphMap i i, PairActions ps g ∧ ∀ root k,
      k ≤ height (atGeometry i w hw) + 1 →
      ((RingSphereStore.rows (atGeometry i w hw) root k).map
        (fun row => (RingSphereStore.siteMap (g.atTables w x hw hx) row.1,row.2))).Perm
        (RingSphereStore.rows (atGeometry i x hx) (g.atoms root) k) := by
  obtain ⟨g,actions,full,hands⟩ := (many_twin_frames_iff ps separate w x hw hx gw gx).mpr
    ((signature_eq_iff i ps x w).mp same)
  exact ⟨g,actions,RingSphereStore.spelling_rows (g.atTables w x hw hx) gw hands⟩

/-- Closed raw reports retain their original Nat IDs, request order, duplicates,
refusals and invalid-ID rejection across equal physical signatures. -/
theorem signature_reports (i : Input) (ps : List (TwinPair i))
    (separate : (ps.map TwinPair.c).Nodup) (w x : SpatialConfiguration)
    (hw : w.positions.length = size i) (hx : x.positions.length = size i)
    (gw : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) = true)
    (gx : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) = true)
    (closed : RingHydrogenCompletion.plan i.molecule = [])
    (same : signature i ps x = signature i ps w) (ids : List Nat) :
    RingHydrogenReport.fromRaw? i.molecule x ids = RingHydrogenReport.fromRaw? i.molecule w ids :=
  many_twin_report ps separate w x hw hx closed (gw.trans gx.symm)
    (fun _ => (signature_eq_iff i ps x w).mp same) ids

instance signatureFinite (i : Input) (ps : List (TwinPair i)) : Finite (Signature i ps) := by
  unfold Signature
  infer_instance

theorem signature_card (i : Input) (ps : List (TwinPair i)) :
    Nat.card (Signature i ps) = 3 ^ Nat.card (Index i ps) := by
  letI : Fintype (Index i ps) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  simp [Signature,Nat.card_eq_fintype_card]

/-- Only realized admitted signatures need representatives. This is a finite
index type even though rational coordinate tables form an infinite family. -/
def Realized (i : Input) (ps : List (TwinPair i)) :=
  {s : Signature i ps // ∃ x : SpatialConfiguration, ∃ hx : x.positions.length = size i,
    LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) = true ∧ signature i ps x = s}

instance realizedFinite (i : Input) (ps : List (TwinPair i)) : Finite (Realized i ps) := by
  unfold Realized
  infer_instance

def representative {i : Input} {ps : List (TwinPair i)} (s : Realized i ps) : SpatialConfiguration :=
  Classical.choose s.property

theorem representative_valid {i : Input} {ps : List (TwinPair i)} (s : Realized i ps) :
    ∃ hx : (representative s).positions.length = size i,
      LocalizedChemicalRing.coordinatesAdmitted (atGeometry i (representative s) hx) = true ∧
        signature i ps (representative s) = s.val := Classical.choose_spec s.property

private theorem admitted_tetra_some (i : Input) (x : SpatialConfiguration)
    (hx : x.positions.length = size i)
    (gx : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) = true)
    (c : i.certified.TetrahedralCenter) :
    (readback? (geometry x) (order (fun k => ((tetraEnumeration i c) k).val.val) 1)).isSome = true := by
  let j := atGeometry i x hx
  obtain ⟨points,observed,nonzero,_⟩ :=
    LocalizedChemicalRingPhysicalAdmission.canonical_all_calibrated j.certified gx c
  have point (k : Fin 4) : geometry x (i.certified.canonicalLigandAtom c k).val = some (points k) := by
    change geometry j.spatial (i.certified.canonicalLigandAtom c k).val = _
    rw [← inputGeometry_eq j]
    exact (LocalizedChemicalRingPhysicalSense.inputGeometry_val j.certified _).trans (observed k)
  change (readback? (geometry x)
    [(i.certified.canonicalLigandAtom c 0).val,(i.certified.canonicalLigandAtom c 1).val,
      (i.certified.canonicalLigandAtom c 2).val,(i.certified.canonicalLigandAtom c 3).val]).isSome = true
  rcases lt_or_gt_of_ne nonzero with neg | pos
  · simp [readback?,point,descriptorOfPriorityOrderedPoints?,descriptorOfOrientedVolume?,neg]
  · simp [readback?,point,descriptorOfPriorityOrderedPoints?,descriptorOfOrientedVolume?,pos,not_lt.mpr pos.le]

/-- Every retained tetrahedral coordinate of an admitted realized signature
has one of the two nonzero codes. P readings can still be absent. -/
theorem realized_tetra_nonzero {i : Input} {ps : List (TwinPair i)}
    (s : Realized i ps) (c : TetraIndex i ps) : s.val (.inl c) ≠ 0 := by
  obtain ⟨x,hx,gx,same⟩ := s.property
  have present := admitted_tetra_some i x hx gx c.val
  rw [← same]
  change signCode _ ≠ 0
  obtain ⟨h,found⟩ := Option.isSome_iff_exists.mp present
  rw [found]
  cases h <;> decide

/-- Binary tetrahedral readings and ternary P readings encode all admitted
realized signatures injectively. -/
def admittedCode {i : Input} {ps : List (TwinPair i)} (s : Realized i ps) :
    (TetraIndex i ps → Fin 2) × (PIndex i → Fin 3) :=
  (fun c => ⟨(s.val (.inl c)).val - 1,by
      have nz := realized_tetra_nonzero s c
      have bound := (s.val (.inl c)).isLt
      have positive : (s.val (.inl c)).val ≠ 0 := fun eqn => nz (Fin.ext eqn)
      omega⟩,
    fun a => s.val (.inr a))

theorem admittedCode_injective (i : Input) (ps : List (TwinPair i)) :
    Function.Injective (@admittedCode i ps) := by
  intro s t equal
  apply Subtype.ext
  funext idx
  cases idx with
  | inl c =>
    have eqn := congrArg (fun code => (code.1 c).val) equal
    have ns := realized_tetra_nonzero s c
    have nt := realized_tetra_nonzero t c
    have sv : (s.val (.inl c)).val ≠ 0 := fun h => ns (Fin.ext h)
    have tv : (t.val (.inl c)).val ≠ 0 := fun h => nt (Fin.ext h)
    apply Fin.ext
    change (s.val (.inl c)).val - 1 = (t.val (.inl c)).val - 1 at eqn
    omega
  | inr a => exact congrArg (fun code => code.2 a) equal

/-- Admission removes the zero code at every retained tetrahedral center. -/
theorem realized_card_bound (i : Input) (ps : List (TwinPair i)) :
    Nat.card (Realized i ps) ≤
      2 ^ Nat.card (TetraIndex i ps) * 3 ^ Nat.card (PIndex i) := by
  have bound := Nat.card_le_card_of_injective (@admittedCode i ps) (admittedCode_injective i ps)
  letI : Fintype (TetraIndex i ps) := Fintype.ofFinite _
  letI : Fintype (PIndex i) := Fintype.ofFinite _
  simpa [Nat.card_eq_fintype_card] using bound

/-- Every admitted coordinate table has one finite representative and one
pair action transporting its complete native row lists at all roots/prefixes. -/
theorem representative_rows (i : Input) (ps : List (TwinPair i))
    (separate : (ps.map TwinPair.c).Nodup)
    (x : SpatialConfiguration) (hx : x.positions.length = size i)
    (gx : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) = true) :
    ∃ s : Realized i ps, ∃ hw : (representative s).positions.length = size i,
    ∃ g : GraphMap i i, PairActions ps g ∧ ∀ root k,
      k ≤ height (atGeometry i x hx) + 1 →
      ((RingSphereStore.rows (atGeometry i x hx) root k).map
        (fun row => (RingSphereStore.siteMap (g.atTables x (representative s) hx hw) row.1,row.2))).Perm
        (RingSphereStore.rows (atGeometry i (representative s) hw) (g.atoms root) k) := by
  let s : Realized i ps := ⟨signature i ps x,x,hx,gx,rfl⟩
  obtain ⟨hw,gw,same⟩ := representative_valid s
  obtain ⟨g,actions,rows⟩ := signature_rows i ps separate x (representative s) hx hw gx gw same
  exact ⟨s,hw,g,actions,rows⟩

/-- A finite family of admitted representative tables suffices for all original
raw requests. The representative is selected by physical readings, not evaluations. -/
theorem representative_reports (i : Input) (ps : List (TwinPair i))
    (separate : (ps.map TwinPair.c).Nodup) (closed : RingHydrogenCompletion.plan i.molecule = [])
    (x : SpatialConfiguration) (hx : x.positions.length = size i)
    (gx : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) = true) :
    ∃ s : Realized i ps, ∀ ids : List Nat,
      RingHydrogenReport.fromRaw? i.molecule x ids =
        RingHydrogenReport.fromRaw? i.molecule (representative s) ids := by
  let s : Realized i ps := ⟨signature i ps x,x,hx,gx,rfl⟩
  obtain ⟨hw,gw,same⟩ := representative_valid s
  exact ⟨s,fun ids => signature_reports i ps separate (representative s) x hw hx gw gx closed same.symm ids⟩

end TetraStereo.Engine.RingPhysicalSignatures
assert_kernel_only TetraStereo.Engine.RingPhysicalSignatures.signature_eq_iff
assert_kernel_only TetraStereo.Engine.RingPhysicalSignatures.signature_rows
assert_kernel_only TetraStereo.Engine.RingPhysicalSignatures.signature_reports
assert_kernel_only TetraStereo.Engine.RingPhysicalSignatures.signature_card

assert_kernel_only TetraStereo.Engine.RingPhysicalSignatures.representative_valid
assert_kernel_only TetraStereo.Engine.RingPhysicalSignatures.representative_reports

assert_kernel_only TetraStereo.Engine.RingPhysicalSignatures.representative_rows

assert_kernel_only TetraStereo.Engine.RingPhysicalSignatures.realized_tetra_nonzero
assert_kernel_only TetraStereo.Engine.RingPhysicalSignatures.admittedCode_injective
assert_kernel_only TetraStereo.Engine.RingPhysicalSignatures.realized_card_bound


namespace TetraStereo.Engine.RingPhysicalSignatures
open OneCenter RingHydrogenSpelling RingSpatialTransport RingWrittenPHReadings
open LocalizedChemicalRing (Input)
open RingNestedActivePair (Labels)
open RingGroupedReport (Report)
private theorem roots_of_complete_rows {i : Input}
    (valid : LocalizedChemicalRing.coordinatesAdmitted i = true) (assign : Nat → Option Labels)
    (as : List i.certified.Atom)
    (correct : RingChemicalReport.Correct i as (as.map fun a => (a.val,assign a.val))) :
    ∀ a ∈ as, RingChemicalGraphProof.root i a = some (assign a.val) := by
  induction as with
  | nil => simp
  | cons b bs ih =>
    obtain ⟨row,rest⟩ := List.forall₂_cons.mp correct
    intro a mem
    rcases List.mem_cons.mp mem with rfl | ht
    · exact (RingChemicalGraphProof.root_iff valid _ _).mpr row.2
    · exact ih rest a ht

/-- A single full report determines every valid ordered subrequest, with repetition. -/
theorem project_full_report (i : Input) (cl : RingHydrogenCompletion.plan i.molecule = [])
    (valid : LocalizedChemicalRing.coordinatesAdmitted i = true) (assign : Nat → Option Labels)
    (full : RingHydrogenReport.fromRaw? i.molecule i.spatial (List.range i.molecule.atomCount) =
      some ((List.range i.molecule.atomCount).map fun n => (n,assign n)))
    (ids : List Nat) (bounds : ∀ n ∈ ids, n < i.molecule.atomCount) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial ids = some (ids.map fun n => (n,assign n)) := by
  let as := List.finRange (size i)
  have rangeEq : as.map Fin.val = List.range i.molecule.atomCount := by
    rw [←i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1]
    apply List.ext_getElem
    · simp [as,size]
    · intros; simp [as]
  rw [←rangeEq,fromRaw_closed_report i cl valid] at full
  simp only [List.map_map,Function.comp_def] at full
  have correct := (RingChemicalReport.report_iff i valid _ _).mp full
  exact raw_of_root_labels i assign cl valid ids bounds
    (fun a _ => roots_of_complete_rows valid assign as correct a (List.mem_finRange a))


/-- Recover a requested row by its original atom ID from an atom-indexed full report. -/
def selectRows (ids : List Nat) (rows : Report) : Report :=
  ids.map fun n => (n,rows[n]?.bind Prod.snd)

/-- One actual full public evaluation suffices for every bounded subrequest.
The selected rows can repeat, and a completed refusal is preserved. -/
theorem select_full_report (i : Input) (cl : RingHydrogenCompletion.plan i.molecule = [])
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (ids : List Nat)
    (bounds : ∀ n ∈ ids, n < i.molecule.atomCount) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial ids =
      (RingHydrogenReport.fromRaw? i.molecule i.spatial (List.range i.molecule.atomCount)).map (selectRows ids) := by
  let assign (n : Nat) : Option Labels := if h : n < size i then
    (RingChemicalGraphProof.root i ⟨n,h⟩).join else none
  have roots (a : i.certified.Atom) : RingChemicalGraphProof.root i a = some (assign a.val) := by
    obtain ⟨v,hv,_⟩ := RingChemicalGraphProof.total ok (RingGroupedReport.origin i a)
    have root : RingChemicalGraphProof.root i a = some v :=
      (RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i) a).trans hv
    unfold assign
    rw [dif_pos a.isLt]
    change RingChemicalGraphProof.root i a = some (RingChemicalGraphProof.root i a).join
    rw [root]; rfl
  have values (as : List Nat) (inside : ∀ n ∈ as, n < i.molecule.atomCount) :=
    raw_of_root_labels i assign cl ok as inside (fun a _ => roots a)
  rw [values ids bounds,values _ (fun _ => List.mem_range.mp)]
  apply congrArg some
  apply List.map_congr_left
  intro n mem
  have hn := bounds n mem
  simp [hn]

end TetraStereo.Engine.RingPhysicalSignatures
assert_kernel_only TetraStereo.Engine.RingPhysicalSignatures.select_full_report
