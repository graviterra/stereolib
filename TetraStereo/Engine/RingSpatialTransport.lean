import TetraStereo.Engine.RingHydrogenReport

set_option autoImplicit false
namespace TetraStereo.Engine.RingSpatialTransport
open OneCenter
open LocalizedChemicalRing (Input)
abbrev size (i : Input) := i.certified.certified.input.molecule.atomCount

/-- Preserve every structural field while replacing the exact coordinate table. -/
def atGeometry (i : Input) (g : SpatialConfiguration) (full : g.positions.length = size i) : Input :=
  let base := i.certified.certified
  let auth : AuthoritativeChemicalInput := {base.input with spatial? := some g}
  let cert : CertifiedAuthoritativeChemicalInput :=
    ⟨auth,base.structurallyWellFormed.1,full,base.structurallyWellFormed.2.2⟩
  ⟨⟨cert,i.certified.graphReady⟩,i.molecule,g,i.agreement,rfl,i.admissible,i.supported,i.single,i.charge⟩

theorem full_original (i : Input) : i.spatial.positions.length = size i := by
  have h := i.certified.certified.structurallyWellFormed.2.1
  simpa [AuthoritativeChemicalInput.SpatialIndicesWellFormed,i.spatial_eq] using h

theorem atGeometry_self (i : Input) : atGeometry i i.spatial (full_original i) = i := by
  rcases i with ⟨⟨⟨⟨sem,spatial,diagram⟩,wf⟩,graph⟩,m,g,agree,hs,rest⟩
  cases hs
  rfl

private theorem charge_reference (i : Input) : ∀ a : i.certified.Atom,
    i.certified.moleculeGraph.formalCharge a = LocalizedChemicalRing.referenceCharge i.certified := by
  intro a
  obtain ⟨k,h⟩ := i.charge
  have pos : 0 < size i := Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt
  simp only [LocalizedChemicalRing.referenceCharge,dif_pos pos]
  exact (h a).trans (h ⟨0,pos⟩).symm

/-- Structural admission depends on coordinate count alone. In particular, the
atom indices, semantic graph, parsed diagram and all retained bond orders are the
same at each coordinate table of the required length. -/
theorem admit_atGeometry (i : Input) (g : SpatialConfiguration) (full : g.positions.length = size i) :
    LocalizedChemicalRing.admitRawSpatial? i.molecule g = some (atGeometry i g full) := by
  let j := atGeometry i g full
  have source : i.molecule.toAuthoritativeChemicalInputWithSpatial? g = some j.certified.certified.input := by
    simp [RawMolecule.toAuthoritativeChemicalInputWithSpatial?,i.agreement.1,j,atGeometry,i.agreement.2]
  have cert : j.certified.certified.input.certify? = some j.certified.certified := by
    have ok := j.certified.certified.input.structurallyWellFormed?_eq_true_iff.mpr j.certified.certified.structurallyWellFormed
    simp [AuthoritativeChemicalInput.certify?,ok]
  have loc : j.certified.certified.certifyLocalizedCIP? = some j.certified := by
    have ok := j.certified.certified.input.molecule.localizedCIPGraphReady?_eq_true_iff.mpr j.certified.graphReady
    simp [CertifiedAuthoritativeChemicalInput.certifyLocalizedCIP?,ok]
  have hl : LocalizedReference.admitRawSpatial? i.molecule g = some ⟨j.certified⟩ := by
    simp [LocalizedReference.admitRawSpatial?,LocalizedReference.admitSource?,source,cert,loc]
  have ha := i.molecule.stereochemicalAdmissible?_eq_true_iff.mpr i.admissible
  have hb : (i.molecule.bonds.all fun b => b.kind.localizedBondOrder?.isSome) = true :=
    List.all_eq_true.mpr fun b h => b.kind.localizedBondOrder?_isSome_iff.mpr (i.supported b h)
  unfold LocalizedChemicalRing.admitRawSpatial?
  simp only [dif_pos ha,dif_pos hb]
  split
  · rename_i hnone
    rw [hl] at hnone
    contradiction
  · rename_i v hv
    have eqv := Option.some.inj (hv.symm.trans hl)
    subst v
    simp only [dif_pos j.single,dif_pos (charge_reference j)]
    rfl


/-- Admitting an input again recovers the entire typed input, even when it was
constructed directly from its certification fields. -/
theorem readmit (i : Input) : LocalizedChemicalRing.admitRawSpatial? i.molecule i.spatial = some i :=
  (admit_atGeometry i i.spatial (full_original i)).trans (congrArg some (atGeometry_self i))

theorem same_graph {i j : Input} (raw : i.molecule = j.molecule) :
    i.certified.certified.input.molecule = j.certified.certified.input.molecule :=
  Option.some.inj (i.agreement.1.symm.trans (raw ▸ j.agreement.1))

theorem full_at_other {i j : Input} (raw : i.molecule = j.molecule) :
    j.spatial.positions.length = size i :=
  (full_original j).trans (congrArg SemanticMolecule.atomCount (same_graph raw).symm)

/-- Two inputs on the same raw graph differ only by replacement of the coordinate
table. There is no additional comparison or relabelling assumption. -/
theorem eq_atGeometry {i j : Input} (raw : i.molecule = j.molecule) :
    atGeometry i j.spatial (full_at_other raw) = j := by
  apply Option.some.inj
  rw [← admit_atGeometry,raw,readmit]

theorem admission_iff_length {m : RawMolecule} {g : SpatialConfiguration} {i : Input}
    (admitted : LocalizedChemicalRing.admitRawSpatial? m g = some i)
    (other : SpatialConfiguration) :
    (∃ j, LocalizedChemicalRing.admitRawSpatial? m other = some j) ↔
      other.positions.length = m.atomCount := by
  obtain ⟨hm,_⟩ := RingChemicalReport.admission_fields admitted
  rw [← hm]
  have sizeEq := i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1
  constructor
  · rintro ⟨j,h⟩
    obtain ⟨jm,jg⟩ := RingChemicalReport.admission_fields h
    have len := full_original j
    rw [← jg]
    exact len.trans (by rw [size,j.molecule.toSemanticMolecule?_atomCount _ j.agreement.1,jm])
  · intro length
    exact ⟨_,admit_atGeometry i other (length.trans sizeEq.symm)⟩

open LocalizedActualPhysicalBranchDecision LocalizedChemicalRingPhysicalAdmission
open CertifiedLocalizedCIPInput (descriptorOfOrientedVolume?)

def pointVolume (g : SpatialConfiguration) (ids : Fin 4 → Nat) : Option ℚ := do
  let a ← g.positions[ids 0]?
  let b ← g.positions[ids 1]?
  let c ← g.positions[ids 2]?
  let d ← g.positions[ids 3]?
  return CartesianPoint3.orientedVolume a b c d

abbrev centerIds (i : Input) (c : (actualCanonicalMolecule i.certified).Center) (k : Fin 4) :=
  ((actualCanonicalMolecule i.certified).ligandAtomAt c k).val

theorem coordinateVolume_eq (i : Input) (c : (actualCanonicalMolecule i.certified).Center) :
    coordinateVolume? i.certified c = pointVolume i.spatial (centerIds i c) := by
  simp only [coordinateVolume?,CertifiedLocalizedCIPInput.spatialPointAt?,i.spatial_eq]
  rfl

/-- Only the four neighboring ligand coordinates enter tetrahedral admission.
This also applies to degeneracy and rejection. -/
theorem coordinates_of_same_ligands {i : Input} {g : SpatialConfiguration}
    (full : g.positions.length = size i)
    (same : ∀ (c : (actualCanonicalMolecule i.certified).Center) (k : Fin 4),
      g.positions[centerIds i c k]? = i.spatial.positions[centerIds i c k]?) :
    LocalizedChemicalRing.coordinatesAdmitted (atGeometry i g full) =
      LocalizedChemicalRing.coordinatesAdmitted i := by
  have center (c : (actualCanonicalMolecule i.certified).Center) :
      centerAdmitted (atGeometry i g full).certified c = centerAdmitted i.certified c := by
    have volume : coordinateVolume? (atGeometry i g full).certified c = coordinateVolume? i.certified c := by
      rw [coordinateVolume_eq (atGeometry i g full),coordinateVolume_eq i]
      change pointVolume g (centerIds i c) = pointVolume i.spatial (centerIds i c)
      simp only [pointVolume,same]
    unfold centerAdmitted
    rw [volume]
  unfold LocalizedChemicalRing.coordinatesAdmitted allCentersAdmitted
  congr 1
  apply propext
  constructor <;> intro h c
  · exact (center c) ▸ h c
  · exact (center c).symm ▸ h c

open RingHydrogenCompletion (plan)
open RingGroupedReport (Report)

/-- A closed graph with a typed structural admission does not change on preparation.
The coordinate check can still reject the geometry. -/
theorem prepared_closed (i : Input) (closed : plan i.molecule = []) :
    RingChemicalReport.prepared? i = if LocalizedChemicalRing.coordinatesAdmitted i then some i else none := by
  have len : i.spatial.positions.length = i.molecule.atomCount :=
    (full_original i).trans (i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1)
  have completed := RingHydrogenCompletion.prepare?_of_complete i.molecule i.spatial closed
    (RingChemicalReport.closed_certificate _ _ i.admissible len closed)
  cases geo : LocalizedChemicalRing.coordinatesAdmitted i <;>
    simp [RingChemicalReport.prepared?,geo,guard,completed,readmit]

theorem empty_closed (i : Input) (closed : plan i.molecule = []) :
    RingChemicalReport.fromRaw? i.molecule i.spatial [] =
      if LocalizedChemicalRing.coordinatesAdmitted i then some [] else none := by
  cases geo : LocalizedChemicalRing.coordinatesAdmitted i <;>
    simp [RingChemicalReport.fromRaw?,readmit,RingChemicalReport.forAtoms?,RingMolecularReport.resolve,
      prepared_closed i closed,geo,RingChemicalReport.report?]

/-- For a structurally admitted closed graph, coordinate admission and original
ID bounds exhaust the domain of the fixed-geometry public report. -/
theorem closed_domain (i : Input) (closed : plan i.molecule = []) (ids : List Nat) :
    (∃ rows, RingChemicalReport.fromRaw? i.molecule i.spatial ids = some rows) ↔
    (∀ n ∈ ids, n < i.molecule.atomCount) ∧ LocalizedChemicalRing.coordinatesAdmitted i = true := by
  rw [RingChemicalReport.fromRaw_domain_iff]
  apply and_congr_right'
  constructor
  · rintro ⟨source,p,admit,ready⟩
    rw [readmit] at admit
    cases admit
    exact ready.1
  · intro geo
    refine ⟨i,i,readmit i,(RingChemicalReport.prepared_iff i i).mp ?_⟩
    simp [prepared_closed i closed,geo]

end TetraStereo.Engine.RingSpatialTransport
assert_kernel_only TetraStereo.Engine.RingSpatialTransport.admit_atGeometry
