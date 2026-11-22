import TetraStereo.Engine.RingRetainedChemicalTrace
import TetraStereo.Engine.RingStrictConstitution

set_option autoImplicit false

namespace TetraStereo.Engine.RingRetainedAuxiliary
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingRetainedConstitution (Cursor Key)
open LocalizedChemicalRingPhysicalSense (inputGeometry inputGeometry_val)

abbrev Occurrence (i : CertifiedLocalizedCIPInput) (d : Nat) := i.LocalizedCIPOccurrence d
abbrev Branch (i : CertifiedLocalizedCIPInput) (d : Nat) := Cursor i d × Key i

def frame (i : CertifiedLocalizedCIPInput) {d : Nat} (q : Occurrence i d) :=
  i.executableLocalizedRerootChildren ⟨q,none⟩

private def compare (i : CertifiedLocalizedCIPInput) {d : Nat} (a b : Branch i d) :=
  ExactOfficialRuleMajorKey.compareObserved i.moleculeGraph i.certified.input.molecule.semanticExactOfficialRule1aObservation a.2 b.2

/-- Rank the entire occurrence frame, including the branch toward the original root. Each
retained constitutional key is computed once and remains paired with its source cursor. -/
def order (i : CertifiedLocalizedCIPInput) {d : Nat} (q : Occurrence i d) : List (Branch i d) :=
  let rows := (frame i q).map fun b => (b,RingRetainedConstitution.key i b)
  rows.mergeSort fun a b => (compare i a b).isGE

theorem order_perm (i : CertifiedLocalizedCIPInput) {d : Nat} (q : Occurrence i d) :
    (order i q).Perm ((frame i q).map fun b => (b,RingRetainedConstitution.key i b)) := List.mergeSort_perm ..

/-- A physical coordinate carrier is the current atom at the actual directed occurrence. -/
def atom? {i d} (b : Branch i d) : Option Nat := b.1.occurrence.val.node.current?.map Fin.val

def canonical (i : CertifiedLocalizedCIPInput) (c : i.TetrahedralCenter) : List Nat :=
  (List.finRange 4).map fun k => (i.canonicalLigandAtom c k).val

def Strict (i : CertifiedLocalizedCIPInput) {d : Nat} (bs : List (Branch i d)) := bs.Pairwise fun a b => compare i a b = .gt

instance {i d} {bs : List (Branch i d)} : Decidable (Strict i bs) := by unfold Strict; infer_instance

/-- Recheck the proposed carrier order with the molecular projections. Real atoms have
equal Rule 1b priority across original depths. Each complete directed key is read once. -/
def chemicalOrder? (input : Input) {d : Nat} (bs : List (Branch input.certified d)) :
    Option (List RingRetainedChemicalTrace.Key) :=
  bs.mapM fun b => RingRetainedChemicalTrace.key? input b.1

def ChemicallyStrict (keys : List RingRetainedChemicalTrace.Key) :=
  keys.Pairwise fun a b => RingRetainedChemicalTrace.compareKeys a b = .gt

instance {keys} : Decidable (ChemicallyStrict keys) := by unfold ChemicallyStrict; infer_instance

/-- Independent physical and ordering requirements, before reading any coordinates. -/
structure Prepared (input : Input) {d : Nat} (q : Occurrence input.certified d) where
  fullCarrier : input.certified.certified.input.molecule.atomCount+1 ≤ d
  center : input.certified.TetrahedralCenter
  realCenter : input.certified.RealTetrahedralCenterNode q.val.node center
  ids : List Nat
  coordinates : (order input.certified q).mapM atom? = some ids
  carriers : ids.Perm (canonical input.certified center)
  strict : Strict input.certified (order input.certified q)
  molecularKeys : List RingRetainedChemicalTrace.Key
  fromMolecule : chemicalOrder? input (order input.certified q) = some molecularKeys
  chemicalPriorities : ChemicallyStrict molecularKeys

def prepare? (input : Input) {d : Nat} (q : Occurrence input.certified d) : Option (Prepared input q) :=
  if full : input.certified.certified.input.molecule.atomCount+1 ≤ d then do
    let i := input.certified
    let ⟨c,found⟩ ← (i.localizedOccurrenceDescriptorCenter? q).attach
    let bs := order i q
    let ⟨ids,bound⟩ ← (bs.mapM atom?).attach
    if ok : ids.Perm (canonical i c) ∧ Strict i bs then
      let ⟨keys,source⟩ ← (chemicalOrder? input bs).attach
      if higher : ChemicallyStrict keys then
        return ⟨full,c,(i.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mp found,ids,bound,ok.1,ok.2,keys,source,higher⟩
    none
  else none

private theorem prepare_of {input d} {q : Occurrence input.certified d} (w : Prepared input q) :
    prepare? input q = some w := by
  obtain ⟨full,c,real,ids,points,perm,strict,keys,source,higher⟩ := w
  have center := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mpr real
  have cseen := Option.attach_eq_some _ ⟨c,center⟩
  have pseen := Option.attach_eq_some _ ⟨ids,points⟩
  have kseen := Option.attach_eq_some _ ⟨keys,source⟩
  simp [prepare?,full,cseen,pseen,perm,strict,kseen,higher]

/-- A missing value leaves the later-rule and geometry cases open. -/
def read? (input : Input) {d : Nat} (q : Occurrence input.certified d) : Option RS := do
  let w ← prepare? input q
  readback? (inputGeometry input.certified) w.ids

theorem read_iff (input : Input) {d : Nat} (q : Occurrence input.certified d) (hand : RS) :
    read? input q = some hand ↔ ∃ w : Prepared input q, readback? (inputGeometry input.certified) w.ids = some hand := by
  constructor
  · intro got
    obtain ⟨w,_,raw⟩ := Option.bind_eq_some_iff.mp got
    exact ⟨w,raw⟩
  · rintro ⟨w,raw⟩
    simpa [read?,prepare_of w] using raw

private theorem calibrated (input : Input) (admit : LocalizedChemicalRing.coordinatesAdmitted input = true)
    (c : input.certified.TetrahedralCenter) (ids : List Nat) (covers : ids.Perm (canonical input.certified c)) :
    (readback? (inputGeometry input.certified) ids).isSome = true := by
  let i := input.certified
  let atom := fun k : Fin 4 => (i.canonicalLigandAtom c k).val
  obtain ⟨pt,points,nonzero,_⟩ := LocalizedChemicalRingPhysicalAdmission.canonical_all_calibrated i admit c
  have seen : (readback? (inputGeometry i) [atom 0,atom 1,atom 2,atom 3]).isSome = true := by
    have observe (k : Fin 4) : inputGeometry i (atom k) = some (pt k) := (inputGeometry_val i _).trans (points k)
    rcases lt_or_gt_of_ne nonzero with neg | pos
    · simp [readback?,observe,descriptorOfPriorityOrderedPoints?,descriptorOfOrientedVolume?,neg]
    · simp [readback?,observe,descriptorOfPriorityOrderedPoints?,descriptorOfOrientedVolume?,pos,not_lt.mpr pos.le]
  have distinct : (canonical i c).Nodup :=
    List.Nodup.map (Fin.val_injective.comp (i.canonicalLigandAtom_injective c)) (List.nodup_finRange 4)
  exact RingChemicalPriority.ReferenceFrame.readback_all_permutations distinct (by simp [canonical]) seen ids covers

/-- On an admitted geometry the only remaining prerequisites are a real tetrahedral target,
all four original physical carriers, and a strict constitutional order on that full frame. -/
theorem read_isSome_iff (input : Input) (admit : LocalizedChemicalRing.coordinatesAdmitted input = true)
    {d : Nat} (q : Occurrence input.certified d) :
    (read? input q).isSome = true ↔ Nonempty (Prepared input q) := by
  constructor
  · intro h
    obtain ⟨s,hs⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨w,_⟩ := (read_iff input q s).mp hs
    exact ⟨w⟩
  · rintro ⟨w⟩
    simp [read?,prepare_of w,calibrated input admit w.center w.ids w.carriers]

/-- Geometry and case of any returned occurrence publication. The second reading uses the
same ordered carriers after spatial reflection. -/
theorem read_source (input : Input) {d : Nat} (q : Occurrence input.certified d) (hand : RS)
    (found : read? input q = some hand) :
    ∃ w : Prepared input q, readback? (inputGeometry input.certified) w.ids = some hand ∧
      readback? (mirror (inputGeometry input.certified)) w.ids = some hand.swap ∧
      (RingChemicalPriority.Recursive.geometric (inputGeometry input.certified) w.ids w.ids).bind
        RingChemicalPriority.Recursive.Reading.label = some (.chiral hand) := by
  obtain ⟨w,raw⟩ := (read_iff input q hand).mp found
  have reflected : readback? (mirror (inputGeometry input.certified)) w.ids = some hand.swap := by rw [readback_mirror,raw]; rfl
  have geometric : RingChemicalPriority.Recursive.geometric (inputGeometry input.certified) w.ids w.ids = some ⟨hand,hand.swap⟩ := by
    simp [RingChemicalPriority.Recursive.geometric,raw,reflected]
  refine ⟨w,raw,reflected,?_⟩
  rw [geometric]
  exact (RingChemicalPriority.Recursive.constitutional_casing geometric).2.2

private theorem branch_source {i d} {q : Occurrence i d} {b : Branch i d} (mem : b ∈ order i q) :
    b.2 = RingRetainedConstitution.key i b.1 ∧ i.LocalizedRerootCursorValid b.1 ∧ b.1.previous? = some q := by
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ((order_perm i q).mem_iff.mp mem)
  have frameOk := i.executableLocalizedRerootChildren_declarative (⟨q,none⟩ : Cursor i d)
  exact ⟨rfl,i.localizedRerootChild_valid _ x _ frameOk hx,frameOk.2 x hx⟩

/-- Each pair used by the strict check is a comparison of keys expanded at the exact two
retained occurrences, both entered from the common target. -/
theorem pair_source (i : CertifiedLocalizedCIPInput) {d : Nat} (q : Occurrence i d) (a b : Branch i d)
    (ma : a ∈ order i q) (mb : b ∈ order i q) :
    a.1.previous? = some q ∧ b.1.previous? = some q ∧ RingRetainedConstitution.Expansion i a.1 a.2 ∧
      RingRetainedConstitution.Expansion i b.1 b.2 ∧
      cipTraceOutcome (RingRetainedConstitution.trace i a.1 b.1) = compare i a b := by
  obtain ⟨ka,va,fa⟩ := branch_source ma
  obtain ⟨kb,vb,fb⟩ := branch_source mb
  refine ⟨fa,fb,ka ▸ (RingRetainedConstitution.key_source i _ va).1,kb ▸ (RingRetainedConstitution.key_source i _ vb).1,?_⟩
  simp only [RingRetainedConstitution.trace,ExactOfficialRuleMajorKey.compareTraceObserved_eq_exact _ _ i.executableExactOfficialRule1aObservation_correct,
    ExactOfficialRuleMajorKey.compareTrace_outcome,compare,ka,kb,ExactOfficialRuleMajorKey.compareObserved_eq_exact _ _ i.executableExactOfficialRule1aObservation_correct]

/-- Distinct original directions are compared before any sorting. This relation depends only
on the complete retained source trace. -/
def Separated (i : CertifiedLocalizedCIPInput) {d : Nat} (q : Occurrence i d) :=
  (frame i q).Pairwise fun a b => cipTraceOutcome (RingRetainedConstitution.trace i a b) ≠ .eq

theorem strict_iff_separated (i : CertifiedLocalizedCIPInput) {d : Nat} (q : Occurrence i d) :
    Strict i (order i q) ↔ Separated i q := by
  let cmp := ExactOfficialRuleMajorKey.compare i.moleculeGraph
  letI : Std.TransCmp cmp := ExactOfficialRuleMajorKey.compare_transCmp _
  have value (a b : Branch i d) : compare i a b = cmp a.2 b.2 :=
    ExactOfficialRuleMajorKey.compareObserved_eq_exact _ _ i.executableExactOfficialRule1aObservation_correct _ _
  have original (a b : Cursor i d) : cipTraceOutcome (RingRetainedConstitution.trace i a b) =
      cmp (RingRetainedConstitution.key i a) (RingRetainedConstitution.key i b) := by
    rw [RingRetainedConstitution.trace,ExactOfficialRuleMajorKey.compareTraceObserved_eq_exact _ _ i.executableExactOfficialRule1aObservation_correct]
    exact ExactOfficialRuleMajorKey.compareTrace_outcome ..
  have oriented {a b : Branch i d} (ne : cmp a.2 b.2 ≠ .eq) : cmp b.2 a.2 ≠ .eq :=
    fun e => ne (Std.OrientedCmp.eq_symm e)
  have perm := (order_perm i q).pairwise_iff (R := fun (a b : Branch i d) => cmp a.2 b.2 ≠ .eq) (fun h => oriented h)
  have raw : Separated i q ↔ (order i q).Pairwise (fun a b => cmp a.2 b.2 ≠ .eq) := by
    rw [perm,List.pairwise_map]
    simp only [Separated,original]
  have trans (a b c : Branch i d) : (cmp a.2 b.2).isGE → (cmp b.2 c.2).isGE → (cmp a.2 c.2).isGE := Std.TransCmp.isGE_trans
  have total (a b : Branch i d) : ((cmp a.2 b.2).isGE || (cmp b.2 a.2).isGE) = true := by
    rw [Std.OrientedCmp.eq_swap (cmp := cmp) (a := a.2) (b := b.2)]
    cases cmp b.2 a.2 <;> rfl
  have descending : (order i q).Pairwise (fun a b => (cmp a.2 b.2).isGE = true) := by
    unfold order
    simp only [value]
    exact List.pairwise_mergeSort trans total _
  rw [raw]
  unfold Strict
  simp only [value]
  constructor
  · exact fun h => h.imp fun win => by rw [win]; decide
  · intro untied
    apply (List.pairwise_and_iff.mpr ⟨descending,untied⟩).imp
    intro a b h
    cases eqn : cmp a.2 b.2 <;> simp_all

/-- Distinguish a certified absent tetrahedral publication from an unresolved real occurrence. -/
def publication? (input : Input) {d : Nat} (q : Occurrence input.certified d) : Option (Option RS) :=
  if (input.certified.localizedOccurrenceDescriptorCenter? q).isNone then some none else (read? input q).map some

theorem absence_iff (input : Input) {d : Nat} (q : Occurrence input.certified d) :
    publication? input q = some none ↔ ∀ c, ¬input.certified.RealTetrahedralCenterNode q.val.node c := by
  cases h : input.certified.localizedOccurrenceDescriptorCenter? q with
  | none =>
    simp only [publication?,h,Option.isNone_none,if_true,true_iff]
    intro c present
    rw [(input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mpr present] at h
    contradiction
  | some c =>
    have real := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mp h
    cases v : read? input q <;> simp [publication?,h,v]
    all_goals exact ⟨c.1,c.2,real⟩

theorem publication_of_read {input d} {q : Occurrence input.certified d} {s : RS} (read : read? input q = some s) :
    publication? input q = some (some s) := by
  obtain ⟨w,_⟩ := (read_iff input q s).mp read
  rw [publication?,(input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q w.center).mpr w.realCenter]
  simp [read]

/-- All original unbounded descendants are present at every accepted positive reader depth. -/
theorem covers_descendant (i : CertifiedLocalizedCIPInput) {d : Nat}
    (full : i.certified.input.molecule.atomCount+1 ≤ d) (root : i.Atom) {path : List Nat} {node : OfficialCIPNode i.Atom}
    (reachable : i.UnboundedOfficialSubtree (OfficialCIPNode.root root) path node) :
    { root := root, address := path, node := node, remaining := d+1-path.length } ∈ i.localizedOccurrences d := by
  have bound := i.unboundedOfficialSubtree_address_length_le_of_complete _
    (i.executableOfficialExpansionCompleteWithin_root_default root) reachable
  have covered := i.mem_localizedOccurrenceSubtree_of_unbounded (root := root) (fuel := d+1) (path := []) reachable (by omega)
  unfold localizedOccurrences
  rw [List.mem_dedup,List.mem_flatMap]
  exact ⟨root,by simp,by simpa [localizedOccurrencesAtAtom] using covered⟩

private theorem points_carriers (i : CertifiedLocalizedCIPInput) {d : Nat} :
    ∀ (bs : List (Branch i d)) (ids : List Nat), bs.mapM atom? = some ids →
      bs.mapM (fun b => i.localizedRerootCursorSpatialPoint? b.1) = ids.mapM (inputGeometry i)
  | [],ids,got => by simp at got; subst ids; rfl
  | b::bs,ids,got => by
    rw [List.mapM_cons] at got
    cases h : b.1.occurrence.val.node.current? with
    | none => simp [atom?,h] at got
    | some x =>
      cases rest : bs.mapM atom? with
      | none => simp [atom?,h,rest] at got
      | some tail =>
        simp [atom?,h,rest] at got
        subst ids
        have head : i.localizedRerootCursorSpatialPoint? b.1 = inputGeometry i x.val := by
          simp [localizedRerootCursorSpatialPoint?,h,inputGeometry_val]
        simp only [List.mapM_cons,head,points_carriers i bs tail rest]

/-- Readback equals the existing semantic occurrence-geometry lookup on the exact sorted
cursor frame, including its incoming parent-facing ligand. -/
theorem Prepared.occurrence_geometry {input d} {q : Occurrence input.certified d} (w : Prepared input q) :
    ((order input.certified q).mapM (fun b => input.certified.localizedRerootCursorSpatialPoint? b.1)).bind
      descriptorOfPriorityOrderedPoints? = readback? (inputGeometry input.certified) w.ids := by
  rw [points_carriers input.certified _ _ w.coordinates]
  rfl

/-- Recognition of a structurally absent tetrahedral publication agrees with both existing
state-relative descriptor readers for every dependency view. A constitutional tie alone never
triggers this conclusion. -/
theorem absence_readers {input d} {q : Occurrence input.certified d} (absent : publication? input q = some none)
    (view : input.certified.LocalizedDependencyView q) :
    input.certified.localizedOccurrenceRule45Descriptor? q view = none ∧
    input.certified.localizedOccurrenceDescriptorBearingRule3Through5Descriptor? q view = none := by
  have noReal := (absence_iff input q).mp absent
  have miss : input.certified.localizedOccurrenceDescriptorCenter? q = none := by
    cases h : input.certified.localizedOccurrenceDescriptorCenter? q with
    | none => rfl
    | some c => exact False.elim (noReal c ((input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mp h))
  simp [localizedOccurrenceRule45Descriptor?,localizedOccurrenceRule45SpatialEvidence?,
    localizedOccurrenceDescriptorBearingRule3Through5Descriptor?,localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence?,miss]

/-- Each of the six ordered physical priorities comes from its retained source trace. -/
theorem Prepared.priorities {input d} {q : Occurrence input.certified d} (w : Prepared input q) :
    (order input.certified q).Pairwise fun a b => cipTraceOutcome (RingRetainedConstitution.trace input.certified a.1 b.1) = .gt := by
  apply List.pairwise_iff_getElem.mpr
  intro j k hj hk before
  rw [(pair_source _ q _ _ (List.getElem_mem hj) (List.getElem_mem hk)).2.2.2.2]
  exact List.pairwise_iff_getElem.mp w.strict j k hj hk before

/-- Extract the proved hand directly from a positive publication. -/
theorem publication_iff {input d} {q : Occurrence input.certified d} {s : RS} :
    publication? input q = some (some s) ↔ read? input q = some s := by
  refine ⟨?_,publication_of_read⟩
  intro got
  unfold publication? at got
  split at got
  · simp at got
  · simpa using got

end TetraStereo.Engine.RingRetainedAuxiliary

assert_kernel_only TetraStereo.Engine.RingRetainedAuxiliary.read_iff
assert_kernel_only TetraStereo.Engine.RingRetainedAuxiliary.read_isSome_iff
assert_kernel_only TetraStereo.Engine.RingRetainedAuxiliary.read_source
assert_kernel_only TetraStereo.Engine.RingRetainedAuxiliary.pair_source

assert_kernel_only TetraStereo.Engine.RingRetainedAuxiliary.strict_iff_separated
assert_kernel_only TetraStereo.Engine.RingRetainedAuxiliary.absence_iff
assert_kernel_only TetraStereo.Engine.RingRetainedAuxiliary.publication_of_read

assert_kernel_only TetraStereo.Engine.RingRetainedAuxiliary.covers_descendant
assert_kernel_only TetraStereo.Engine.RingRetainedAuxiliary.Prepared.occurrence_geometry
assert_kernel_only TetraStereo.Engine.RingRetainedAuxiliary.absence_readers
assert_kernel_only TetraStereo.Engine.RingRetainedAuxiliary.Prepared.priorities
assert_kernel_only TetraStereo.Engine.RingRetainedAuxiliary.publication_iff
