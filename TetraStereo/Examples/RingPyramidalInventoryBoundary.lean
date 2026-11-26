import TetraStereo.Engine.RingTerminalTwinRefusal
import TetraStereo.Engine.RingPhosphorusAtomicFrame

/-! # Regression for the neutral P/As pyramidal inventory

This mathematical raw-admission witness is not an assertion that the exact
As-O-S three-membered compound has been experimentally isolated. Neutral As0
has distinct bonded ligands S > F > O. Both nonzero mirrored pyramidal readings
are now recognized by the native public evaluator. The former P-only selector
skipped this center; that was an inventory omission, not a comparison-rule error.

IUPAC Blue Book P-93.3.3.2/P-93.3.4.1 supplies the low-priority phantom:
https://iupac.qmul.ac.uk/BlueBook/P9.html#P-93.3.4.1
Experimental class evidence, distinct from this graph: Roberts and Wild,
J. Chem. Soc., Dalton Trans. 1979, 2015-2021, resolved tertiary arsines with
asymmetric As and determined absolute configuration crystallographically:
https://doi.org/10.1039/DT9790002015 -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (frozen)

def molecule : RawMolecule where
  atoms := [.As,.O,.S,.F].map AtomSpec.aliphatic
  bonds := [⟨0,1,.single⟩,⟨1,2,.single⟩,⟨2,0,.single⟩,⟨0,3,.single⟩]

/-- Reflect x, keeping atom identities and priority order fixed. -/
def positions (reflected : Bool) : SpatialConfiguration :=
  ⟨[⟨0,0,1⟩,⟨if reflected then -1 else 1,0,0⟩,⟨0,1,0⟩,
    ⟨if reflected then 1 else -1,-1,0⟩]⟩

abbrev IDs := Fin 4
def atomEquiv (i : Input) (raw : i.molecule = molecule) : i.certified.Atom ≃ IDs := rawVertices i raw
def atom (i : Input) (raw : i.molecule = molecule) (n : IDs) : i.certified.Atom := (atomEquiv i raw).symm n
@[simp] theorem atom_val (i : Input) (raw : i.molecule = molecule) (n : IDs) : (atom i raw n).val = n.val := rfl
@[simp] theorem atom_equiv (i : Input) (raw : i.molecule = molecule) (a : i.certified.Atom) :
    atom i raw (atomEquiv i raw a) = a := (atomEquiv i raw).symm_apply_apply a

private theorem raw_adj (i : Input) (raw : i.molecule = molecule) (n m : IDs) :
    i.certified.moleculeGraph.Adj (atom i raw n) (atom i raw m) ↔ 0 < molecule.bondOrder n.val m.val := by
  rw [LocalizedChemicalRingPhysicalSense.adj_iff i.molecule i.certified i.agreement
    i.admissible.1.1 i.admissible.1.2 i.supported,raw]
  rfl

private def neighborEquiv (i : Input) (raw : i.molecule = molecule) (n : IDs) :
    {m : IDs // 0 < molecule.bondOrder n.val m.val} ≃ i.certified.moleculeGraph.Neighbor (atom i raw n) where
  toFun m := ⟨atom i raw m.val,(raw_adj i raw n m.val).mpr m.property⟩
  invFun a := ⟨atomEquiv i raw a.val,(raw_adj i raw n _).mp (by simpa using a.property)⟩
  left_inv m := Subtype.ext ((atomEquiv i raw).apply_symm_apply m.val)
  right_inv a := Subtype.ext (atom_equiv i raw a.val)

private theorem degrees : ∀ n : IDs, Fintype.card {m : IDs // 0 < molecule.bondOrder n.val m.val} =
    (![3,2,2,1] n) := by decide +kernel

theorem other_ineligible (i : Input) (raw : i.molecule = molecule) (a : i.certified.Atom)
    (other : a.val ≠ 0) : RingPyramidalPublication.eligible i a = false := by
  obtain ⟨n,rfl⟩ := (atomEquiv i raw).symm.surjective a
  change RingPyramidalPublication.eligible i (atom i raw n) = false
  unfold RingPyramidalPublication.eligible RingPyramidalPublication.phosphorus
  rw [← Fintype.card_congr (neighborEquiv i raw n),degrees]
  simp only [atom_val] at other ⊢
  rw [raw]
  fin_cases n <;> first | contradiction | simp [molecule,AtomSpec.aliphatic]

noncomputable def rawAs : Fin 3 ≃ {m : IDs // 0 < molecule.bondOrder 0 m.val} :=
  Equiv.ofBijective (fun k => ⟨![2,3,1] k,by fin_cases k <;> decide +kernel⟩) (by decide +kernel)
noncomputable def asEnum (i : Input) (raw : i.molecule = molecule) :
    Fin 3 ≃ i.certified.moleculeGraph.Neighbor (atom i raw 0) :=
  rawAs.trans (neighborEquiv i raw 0)

theorem arsenic_selected (i : Input) (raw : i.molecule = molecule) :
    RingPyramidalPublication.phosphorus i (atom i raw 0) = true := by
  unfold RingPyramidalPublication.phosphorus
  rw [← Fintype.card_congr (neighborEquiv i raw 0),degrees]
  simp only [atom_val]
  rw [raw]
  simp [molecule,AtomSpec.aliphatic]

theorem native_as (i : Input) (raw : i.molecule = molecule)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    RingChemicalGraphProof.root i (atom i raw 0) = some
      ((readback? (RingWrittenPHReadings.geometry i.spatial) [2,3,1,0]).map fun h =>
        (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap)) := by
  let recs (k : Fin 3) := AtomSpec.aliphatic (![Element.S,Element.F,Element.O] k)
  have written (k : Fin 3) : i.molecule.atoms[(asEnum i raw k).val.val]? = some (recs k) := by
    change i.molecule.atoms[((![2,3,1] k : IDs)).val]? = _
    rw [raw]
    fin_cases k <;> rfl
  have descending : StrictAnti (fun k => (recs k).element.atomicNumber) := by decide +kernel
  have actual := RingPhosphorusAtomicFrame.state_strict_atomic admitted
    (RingGroupedReport.origin i (atom i raw 0)) (atom i raw 0) rfl rfl
    (arsenic_selected i raw) (asEnum i raw) recs written descending
  rw [RingChemicalGraphProof.root,RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i),
    ← RingChemicalGraphProof.state]
  rw [RingWrittenPHReadings.inputGeometry_eq] at actual
  exact actual

theorem native_other_refusal (i : Input) (raw : i.molecule = molecule) (a : i.certified.Atom)
    (other : a.val ≠ 0) : RingChemicalGraphProof.root i a = some none := by
  rw [RingChemicalGraphProof.root,RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i),
    ← RingChemicalGraphProof.state,RingChemicalGraphProof.state_eq]
  apply RingChemicalGraphProof.skips
  rintro ⟨_,b,current,on⟩
  have same : a = b := Option.some.inj current
  subst b
  rw [other_ineligible i raw a other] at on
  contradiction

theorem closed : RingHydrogenCompletion.plan molecule = [] := by decide +kernel

theorem admission_exists (reflected : Bool) :
    (LocalizedChemicalRing.admitRawSpatial? molecule (positions reflected)).isSome = true := by
  cases reflected <;> decide +kernel

def input (reflected : Bool) : Input :=
  (LocalizedChemicalRing.admitRawSpatial? molecule (positions reflected)).get (admission_exists reflected)

theorem input_raw (reflected : Bool) : (input reflected).molecule = molecule :=
  (RingChemicalReport.admission_fields (Option.some_get (admission_exists reflected)).symm).1

theorem input_spatial (reflected : Bool) : (input reflected).spatial = positions reflected :=
  (RingChemicalReport.admission_fields (Option.some_get (admission_exists reflected)).symm).2

theorem coordinates_admitted (reflected : Bool) : LocalizedChemicalRing.coordinatesAdmitted (input reflected) = true := by
  cases reflected <;> decide +kernel

theorem prepared (reflected : Bool) :
    RingHydrogenCompletion.prepare? molecule (positions reflected) = some (molecule,positions reflected) := by
  cases reflected <;> decide +kernel

/-- This is a nonzero physical readback, rather than a zero-coordinate carrier.
The phantom convention reads S > F > O > As, with the center as fourth point. -/
theorem physical_reading (reflected : Bool) :
    readback? (RingWrittenPHReadings.geometry (positions reflected)) [2,3,1,0] =
      some (if reflected then RS.S else RS.R) := by cases reflected <;> decide +kernel

theorem priority_Z : ((molecule.atoms[2]'(by decide))).element.atomicNumber > ((molecule.atoms[3]'(by decide))).element.atomicNumber ∧
    ((molecule.atoms[3]'(by decide))).element.atomicNumber > ((molecule.atoms[1]'(by decide))).element.atomicNumber := by decide +kernel

def labels (reflected : Bool) (n : Nat) : Option RingNestedActivePair.Labels :=
  if n = 0 then
    let h := if reflected then RS.S else RS.R
    some (.chiral h,.chiral h.swap)
  else none

/-- Exact original rows for every valid request, including repeated As queries. -/
theorem public_labels (reflected : Bool) (ids : List Nat) (bounds : ∀ n ∈ ids, n < 4) :
    RingHydrogenReport.fromRaw? molecule (positions reflected) ids = some (ids.map fun n => (n,labels reflected n)) := by
  have result : RingHydrogenReport.fromRaw? (input reflected).molecule (input reflected).spatial ids =
      some (ids.map fun n => (n,labels reflected n)) := by
    apply raw_of_root_labels (input reflected) (labels reflected)
      (by rw [input_raw]; exact closed) (coordinates_admitted reflected) ids
      (by simpa only [input_raw] using bounds)
    intro a _
    by_cases atAs : a.val = 0
    · have same : a = atom (input reflected) (input_raw reflected) 0 := Fin.ext atAs
      rw [same,native_as _ _ (coordinates_admitted reflected),input_spatial,physical_reading]
      simp [labels]
    · rw [native_other_refusal _ (input_raw reflected) a atAs]
      simp [labels,atAs]
  simpa only [input_raw,input_spatial] using result

theorem public_As_assigned (reflected : Bool) :
    RingHydrogenReport.fromRaw? molecule (positions reflected) [0] = some [(0,labels reflected 0)] :=
  public_labels reflected [0] (by simp)

/-- Complete public behavior for all Nat lists, including invalid-ID rejection. -/
theorem public_all_requests (reflected : Bool) (ids : List Nat) :
    RingHydrogenReport.fromRaw? molecule (positions reflected) ids =
      if ∀ n ∈ ids, n < 4 then some (ids.map fun n => (n,labels reflected n)) else none := by
  by_cases valid : ∀ n ∈ ids, n < 4
  · rw [if_pos valid]; exact public_labels reflected ids valid
  · rw [if_neg valid]
    have gate := RingSpatialTransport.closed_domain (input reflected)
      (by rw [input_raw]; exact closed) ids
    rw [input_raw,input_spatial] at gate
    cases computed : RingHydrogenReport.fromRaw? molecule (positions reflected) ids with
    | none => rfl
    | some rows => exact (valid (by simpa only [molecule,RawMolecule.atomCount,List.length_map] using
        (gate.mp ⟨rows,computed⟩).1)).elim

theorem mirror_As_reports_differ :
    RingHydrogenReport.fromRaw? molecule (positions false) [0] ≠
      RingHydrogenReport.fromRaw? molecule (positions true) [0] := by
  rw [public_As_assigned,public_As_assigned]
  decide +kernel

theorem distinct_physical_readings :
    readback? (RingWrittenPHReadings.geometry (positions false)) [2,3,1,0] ≠
      readback? (RingWrittenPHReadings.geometry (positions true)) [2,3,1,0] := by
  rw [physical_reading,physical_reading]
  decide

/-- The same two-bond source leaves one hydrogen unwritten at either P or As. -/
def implicitSource (arsenic : Bool) : RawMolecule where
  atoms := [AtomSpec.aliphatic (if arsenic then .As else .P),.aliphatic .O,.aliphatic .S]
  bonds := [⟨0,1,.single⟩,⟨1,2,.single⟩,⟨2,0,.single⟩]
def implicitPositions : SpatialConfiguration := ⟨[⟨0,0,1⟩,⟨1,0,0⟩,⟨0,1,0⟩]⟩

theorem implicit_plan (arsenic : Bool) :
    RingHydrogenCompletion.plan (implicitSource arsenic) = [(0,1)] := by
  cases arsenic <;> decide +kernel

theorem implicit_prepared (arsenic : Bool) :
    (RingHydrogenCompletion.prepare? (implicitSource arsenic) implicitPositions).isSome = true := by
  cases arsenic <;> decide +kernel

def implicitResult (arsenic : Bool) : RawMolecule × SpatialConfiguration :=
  (RingHydrogenCompletion.prepare? (implicitSource arsenic) implicitPositions).get (implicit_prepared arsenic)

/-- P and As each select one independently unwritten pyramidal hand and both
physical completions, rather than keeping the default coplanar added H. -/
theorem implicit_hand_coverage (arsenic : Bool) :
    (RingPyramidalChoices.sites (implicitSource arsenic) implicitPositions
      (implicitResult arsenic).1 (implicitResult arsenic).2).length = 1 ∧
    (RingPyramidalChoices.variants (implicitSource arsenic) implicitPositions
      (implicitResult arsenic).1 (implicitResult arsenic).2).length = 2 := by
  cases arsenic <;> decide +kernel

theorem implicit_opposite_readings (arsenic : Bool) :
    ((RingPyramidalChoices.variants (implicitSource arsenic) implicitPositions
      (implicitResult arsenic).1 (implicitResult arsenic).2).map
      (fun g => readback? (RingWrittenPHReadings.geometry g) [2,1,3,0])).Perm [some RS.R,some RS.S] := by
  cases arsenic <;> decide +kernel

end TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary.other_ineligible
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary.arsenic_selected
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary.native_as
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary.native_other_refusal
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary.coordinates_admitted
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary.prepared
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary.physical_reading
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary.priority_Z
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary.public_labels
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary.public_As_assigned
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary.public_all_requests
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary.mirror_As_reports_differ
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary.distinct_physical_readings
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary.implicit_plan
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary.implicit_prepared
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary.implicit_hand_coverage
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PyramidalInventoryBoundary.implicit_opposite_readings
