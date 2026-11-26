import TetraStereo.Engine.RingMolecularReport
import TetraStereo.Engine.RingHydrogenTotality
import TetraStereo.Engine.RingChemicalGraphProof

/-! Molecular reports on hydrogen-completed graphs, indexed by the source atoms. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalReport
open OneCenter
open LocalizedChemicalRing (Input)
open RingGroupedReport (Report)
open RingNestedActivePair (Labels)

def prepared? (source : Input) : Option Input := do
  guard (LocalizedChemicalRing.coordinatesAdmitted source)
  let (m,g) ← RingHydrogenCompletion.prepare? source.molecule source.spatial
  let i ← LocalizedChemicalRing.admitRawSpatial? m g
  guard (LocalizedChemicalRing.coordinatesAdmitted i)
  return i

def Prepared (source i : Input) : Prop :=
  LocalizedChemicalRing.coordinatesAdmitted source = true ∧ ∃ m g,
    RingHydrogenCompletion.prepare? source.molecule source.spatial = some (m,g) ∧
    LocalizedChemicalRing.admitRawSpatial? m g = some i ∧ LocalizedChemicalRing.coordinatesAdmitted i = true

theorem prepared_iff (source i : Input) : prepared? source = some i ↔ Prepared source i := by
  unfold prepared? Prepared
  cases hs : LocalizedChemicalRing.coordinatesAdmitted source <;> simp [guard]
  cases hp : RingHydrogenCompletion.prepare? source.molecule source.spatial with
  | none => simp
  | some pair =>
    rcases pair with ⟨m,g⟩
    simp only [Option.bind_some,Option.some.injEq,Prod.mk.injEq]
    cases ha : LocalizedChemicalRing.admitRawSpatial? m g with
    | none => simp [ha]
    | some j =>
      cases hc : LocalizedChemicalRing.coordinatesAdmitted j <;> simp_all <;> rintro rfl <;> assumption

/-- The graph used in every successful report comes from the original
atom/coordinate prefix by the certified addition of ordinary hydrogen leaves. -/
theorem Prepared.completion {source i : Input} (h : Prepared source i) :
    ∃ m g, RingHydrogenCompletion.Certified source.molecule source.spatial m g ∧
      LocalizedChemicalRing.admitRawSpatial? m g = some i := by
  obtain ⟨_,m,g,completed,admitted,_⟩ := h
  exact ⟨m,g,RingHydrogenCompletion.prepare?_certified completed,admitted⟩

private def row? {i : Input} (a : i.certified.Atom) :=
  (RingChemicalGraphProof.root i a).map fun v => (a.val,v)

def report? (i : Input) (atoms : List i.certified.Atom) : Option Report := atoms.mapM row?

def Correct (i : Input) (atoms : List i.certified.Atom) (rows : Report) : Prop :=
  List.Forall₂ (fun a (row : Nat × Option Labels) => row.1 = a.val ∧
    RingEligibleGraph.Derives (RingPyramidalPublication.eligible i) (RingChemicalGraphProof.Local i)
      a .origin row.2) atoms rows

theorem report_iff (i : Input) (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) (rows : Report) : report? i atoms = some rows ↔ Correct i atoms rows := by
  have one (a : i.certified.Atom) (p : Nat × Option Labels) : row? a = some p ↔
      p.1 = a.val ∧ RingEligibleGraph.Derives (RingPyramidalPublication.eligible i)
        (RingChemicalGraphProof.Local i) a .origin p.2 := by
    rcases p with ⟨n,v⟩
    rw [← RingChemicalGraphProof.root_iff geom]
    simp only [row?,Option.map_eq_some_iff,Prod.mk.injEq]
    constructor
    · rintro ⟨_,h,eqn,rfl⟩; exact ⟨eqn.symm,h⟩
    · rintro ⟨eqn,h⟩; exact ⟨_,h,eqn.symm,rfl⟩
  induction atoms generalizing rows with
  | nil => cases rows <;> simp [report?,Correct]
  | cons a as ih =>
    cases rows with
    | nil =>
      unfold report? Correct
      rw [List.mapM_cons]
      cases row? a <;> cases as.mapM row? <;> simp
    | cons p ps =>
      change (a::as).mapM _ = some _ ↔ List.Forall₂ _ _ _
      rw [List.mapM_cons,List.forall₂_cons]
      apply Iff.trans ?_ (and_congr (one a p) (ih ps))
      unfold report?
      cases row? a <;> cases as.mapM row? <;> simp

def forAtoms? (source : Input) (atoms : List source.certified.Atom) : Option Report := do
  let i ← prepared? source
  report? i (← RingMolecularReport.resolve i (atoms.map Fin.val))

theorem forAtoms_iff (source : Input) (atoms : List source.certified.Atom) (rows : Report) :
    forAtoms? source atoms = some rows ↔ ∃ i, Prepared source i ∧
      ∃ as : List i.certified.Atom, as.map Fin.val = atoms.map Fin.val ∧ Correct i as rows := by
  simp only [forAtoms?,Option.bind_eq_bind,Option.bind_eq_some_iff]
  constructor
  · rintro ⟨i,hi,as,ha,rows'⟩
    have p := (prepared_iff ..).mp hi
    obtain ⟨_,_,_,_,geom⟩ := p.2
    exact ⟨i,p,as,(RingMolecularReport.resolve_iff ..).mp ha,(report_iff i geom ..).mp rows'⟩
  · rintro ⟨i,p,as,ha,rows'⟩
    obtain ⟨_,_,_,_,geom⟩ := p.2
    exact ⟨i,(prepared_iff ..).mpr p,as,(RingMolecularReport.resolve_iff ..).mpr ha,(report_iff i geom ..).mpr rows'⟩

/-- Resolve user IDs against the original molecule before any hydrogen is appended. -/
def fromRaw? (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) : Option Report := do
  let source ← LocalizedChemicalRing.admitRawSpatial? m g
  forAtoms? source (← RingMolecularReport.resolve source ids)

theorem fromRaw_graph_iff (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) (rows : Report) :
    fromRaw? m g ids = some rows ↔ ∃ source : Input, LocalizedChemicalRing.admitRawSpatial? m g = some source ∧
      (∃ original : List source.certified.Atom, original.map Fin.val = ids) ∧
      ∃ i, Prepared source i ∧ ∃ as : List i.certified.Atom, as.map Fin.val = ids ∧ Correct i as rows := by
  simp only [fromRaw?,Option.bind_eq_bind,Option.bind_eq_some_iff,forAtoms_iff,RingMolecularReport.resolve_iff]
  constructor
  · rintro ⟨s,hs,atoms,ha,i,hp,as,he,hr⟩
    exact ⟨s,hs,⟨atoms,ha⟩,i,hp,as,he.trans ha,hr⟩
  · rintro ⟨s,hs,⟨atoms,ha⟩,i,hp,as,he,hr⟩
    exact ⟨s,hs,atoms,ha,i,hp,as,he.trans ha.symm,hr⟩

def centres? (source : Input) : Option Report := do
  let i ← prepared? source
  report? i ((List.finRange i.certified.certified.input.molecule.atomCount).filter fun a =>
    a.val < source.molecule.atoms.length && RingPyramidalPublication.eligible i a)

def carbons? (source : Input) := forAtoms? source (RingGroupedReport.carbons source)

theorem admission_fields {m : RawMolecule} {g : SpatialConfiguration} {i : Input}
    (h : LocalizedChemicalRing.admitRawSpatial? m g = some i) :
    i.molecule = m ∧ i.spatial = g := by
  unfold LocalizedChemicalRing.admitRawSpatial? at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i j hloc
  by_cases hs : j.certified.moleculeGraph.SimpleBonded
  · by_cases hc : ∀ a : j.certified.Atom, j.certified.moleculeGraph.formalCharge a =
        LocalizedChemicalRing.referenceCharge j.certified
    · simp only [dif_pos hs,dif_pos hc,Option.some.injEq] at h
      subst i
      exact ⟨rfl,rfl⟩
    · simp [hs,hc] at h
  · simp [hs] at h

theorem closed_certificate (m : RawMolecule) (g : SpatialConfiguration)
    (adm : m.StereochemicalAdmissible) (positions : g.positions.length = m.atomCount)
    (closed : RingHydrogenCompletion.plan m = []) :
    RingHydrogenCompletion.Certified m g m g := by
  have bonds (b : RawBond) (hb : b ∈ m.bonds) : RingHydrogenCompletion.originalBond m b = true :=
    decide_eq_true ⟨(adm.1.1 b hb).1,(adm.1.1 b hb).2.1⟩
  have originals := List.filter_eq_self.mpr bonds
  have fresh : (m.bonds.filter fun b => !RingHydrogenCompletion.originalBond m b) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro b hb
    simp [bonds b hb]
  simp [RingHydrogenCompletion.Certified,adm,positions,originals,fresh,
    RingHydrogenCompletion.addedParents,closed, List.all_eq_true, RawMolecule.atomCount]
  intro i hi
  exact (RawMolecule.WrittenNeighborExact.at m adm.2 ⟨i,hi⟩).2.1

private theorem typed_ids (i : Input) (ids : List Nat)
    (valid : ∀ n ∈ ids, n < i.molecule.atomCount) :
    ∃ atoms : List i.certified.Atom, atoms.map Fin.val = ids := by
  have size := i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1
  exact ⟨ids.attach.map (fun e => ⟨e.val,by rw [size]; exact valid _ e.property⟩),by simp⟩

theorem report_total {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) : ∃ rows, Correct i atoms rows := by
  induction atoms with
  | nil => exact ⟨[],.nil⟩
  | cons a as ih =>
    obtain ⟨tail,deriv⟩ := ih
    obtain ⟨v,hv,_⟩ := RingChemicalGraphProof.total geom (RingGroupedReport.origin i a)
    have got : RingChemicalGraphProof.root i a = some v := by
      rw [RingChemicalGraphProof.root,RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i)]
      exact hv
    exact ⟨(a.val,v)::tail,.cons ⟨rfl,(RingChemicalGraphProof.root_iff geom a v).mp got⟩ deriv⟩

/-- A report exists exactly when the input and its hydrogen completion are admitted
and every requested index belongs to the original molecule. -/
theorem fromRaw_domain_iff (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) :
    (∃ rows, fromRaw? m g ids = some rows) ↔
    (∀ n ∈ ids, n < m.atomCount) ∧ ∃ source i : Input,
      LocalizedChemicalRing.admitRawSpatial? m g = some source ∧ Prepared source i := by
  constructor
  · rintro ⟨rows,h⟩
    obtain ⟨s,hs,⟨atoms,rfl⟩,i,prep,_⟩ := (fromRaw_graph_iff ..).mp h
    refine ⟨?_,s,i,hs,prep⟩
    intro n hn
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hn
    rw [← (admission_fields hs).1,← s.molecule.toSemanticMolecule?_atomCount _ s.agreement.1]
    exact a.isLt
  · rintro ⟨bounds,s,i,hs,prep⟩
    have fields := admission_fields hs
    obtain ⟨original,ho⟩ := typed_ids s ids (fields.1 ▸ bounds)
    obtain ⟨_,_,cert,hi⟩ := prep.completion
    have inc := cert.atomCount_le
    rw [fields.1,← (admission_fields hi).1] at inc
    obtain ⟨atoms,ha⟩ := typed_ids i ids fun n hn => (bounds n hn).trans_le inc
    obtain ⟨_,_,_,_,geom⟩ := prep.2
    obtain ⟨rows,hrows⟩ := report_total geom atoms
    exact ⟨rows,(fromRaw_graph_iff ..).mpr ⟨s,hs,⟨original,ho⟩,i,prep,atoms,ha,hrows⟩⟩

/-- With a full coordinate row and all hydrogens already present, structural and
coordinate admission suffice for every in-range request, including repeated IDs. -/
theorem fromRaw_closed_total {m : RawMolecule} {g : SpatialConfiguration} {i : Input}
    (h : LocalizedChemicalRing.admitRawSpatial? m g = some i)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (positions : g.positions.length = m.atomCount) (closed : RingHydrogenCompletion.plan m = [])
    (ids : List Nat) (bounds : ∀ n ∈ ids, n < m.atomCount) :
    ∃! rows, fromRaw? m g ids = some rows := by
  obtain ⟨hm,hg⟩ := admission_fields h
  have prepared : Prepared i i := by
    refine ⟨geom,m,g,?_,h,geom⟩
    rw [hm,hg]
    exact RingHydrogenCompletion.prepare?_of_complete m g closed
      (closed_certificate m g (hm ▸ i.admissible) positions closed)
  obtain ⟨rows,hr⟩ := (fromRaw_domain_iff ..).mpr ⟨bounds,i,i,h,prepared⟩
  exact ⟨rows,hr,fun _ other => Option.some.inj (other.symm.trans hr)⟩

/-- Resubmitting the graph and positions constructed from an admitted source gives exactly
the same public response for every list of original atom IDs. Both calls also agree when
the constructed tetrahedral coordinates fail admission. -/
theorem fromRaw_materialized_eq {m out : RawMolecule} {g pos : SpatialConfiguration}
    {source : Input} (hs : LocalizedChemicalRing.admitRawSpatial? m g = some source)
    (geom : LocalizedChemicalRing.coordinatesAdmitted source = true)
    (hc : RingHydrogenCompletion.prepare? m g = some (out,pos))
    (ids : List Nat) (valid : ∀ n ∈ ids, n < m.atomCount) :
    fromRaw? m g ids = fromRaw? out pos ids := by
  obtain ⟨hm,hg⟩ := admission_fields hs
  obtain ⟨as, ha⟩ := typed_ids source ids (hm ▸ valid)
  have ra := (RingMolecularReport.resolve_iff source ids as).mpr ha
  have cert := RingHydrogenCompletion.prepare?_certified hc
  have self := RingHydrogenCompletion.prepare?_of_complete out pos
    (RingHydrogenCompletion.prepare?_closed hc)
    (closed_certificate out pos cert.output_admissible cert.positions_length
      (RingHydrogenCompletion.prepare?_closed hc))
  unfold fromRaw?
  rw [hs]
  cases ho : LocalizedChemicalRing.admitRawSpatial? out pos with
  | none => simp [ra,forAtoms?,prepared?,geom,guard,hm,hg,hc,ho]
  | some i =>
    obtain ⟨om,og⟩ := admission_fields ho
    obtain ⟨bs,hb⟩ := typed_ids i ids (fun n hn => om ▸ (valid n hn).trans_le cert.atomCount_le)
    have rb := (RingMolecularReport.resolve_iff i ids bs).mpr hb
    cases gi : LocalizedChemicalRing.coordinatesAdmitted i <;>
      simp [ra,rb,forAtoms?,prepared?,geom,gi,guard,hm,hg,om,og,hc,self,ho,ha,hb]

end TetraStereo.Engine.RingChemicalReport
assert_kernel_only TetraStereo.Engine.RingChemicalReport.Prepared.completion
assert_kernel_only TetraStereo.Engine.RingChemicalReport.fromRaw_graph_iff
assert_kernel_only TetraStereo.Engine.RingChemicalReport.forAtoms_iff
assert_kernel_only TetraStereo.Engine.RingChemicalReport.fromRaw_domain_iff
assert_kernel_only TetraStereo.Engine.RingChemicalReport.fromRaw_closed_total
assert_kernel_only TetraStereo.Engine.RingChemicalReport.fromRaw_materialized_eq
