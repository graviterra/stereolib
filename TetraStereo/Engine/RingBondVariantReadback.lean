import TetraStereo.Engine.RingBondRecordPublic
import TetraStereo.Engine.RingSpatialTransport

/-! Per-geometry public readback is invariant under bond-table permutations.
Structural readmission of the completed base graphs is the only admission premise;
variant coordinates need no assumed admission result or stereochemical outcome. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingBondVariantReadback
open OneCenter
open LocalizedChemicalRing (Input)
open RingHydrogenCompletion (plan)

private theorem no_admission (i : Input) (g : SpatialConfiguration)
    (bad : g.positions.length ≠ i.molecule.atomCount) :
    LocalizedChemicalRing.admitRawSpatial? i.molecule g = none := by
  cases hit : LocalizedChemicalRing.admitRawSpatial? i.molecule g with
  | none => rfl
  | some k => exact (bad ((RingSpatialTransport.admission_iff_length
      (RingSpatialTransport.readmit i) g).mp ⟨k,hit⟩)).elim

/-- Literal per-geometry rows agree for every coordinate table, including wrong
lengths, physical-admission failures, refusals, and repeated requested IDs. -/
theorem at_coordinates (i j : Input)
    (atoms : i.molecule.atoms = j.molecule.atoms)
    (bonds : i.molecule.bonds.Perm j.molecule.bonds)
    (closed : plan i.molecule = []) (closed' : plan j.molecule = [])
    (g : SpatialConfiguration) (ids : List Nat) :
    RingChemicalReport.fromRaw? j.molecule g ids =
      RingChemicalReport.fromRaw? i.molecule g ids := by
  have counts : i.molecule.atomCount = j.molecule.atomCount := congrArg List.length atoms
  by_cases full : g.positions.length = i.molecule.atomCount
  · have full' : g.positions.length = j.molecule.atomCount := full.trans counts
    let u := RingSpatialTransport.atGeometry i g
      (full.trans (i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1).symm)
    let v := RingSpatialTransport.atGeometry j g
      (full'.trans (j.molecule.toSemanticMolecule?_atomCount _ j.agreement.1).symm)
    have p : RingBondRecordOrder.Presentation u v := ⟨atoms,bonds,rfl⟩
    have eqn := RingBondRecordOrder.closed_raw_public p closed closed' ids
    change RingHydrogenReport.fromRaw? j.molecule g ids =
      RingHydrogenReport.fromRaw? i.molecule g ids at eqn
    simpa only [RingHydrogenReport.fromRaw_closed_eq closed,
      RingHydrogenReport.fromRaw_closed_eq closed'] using eqn
  · have bad' : g.positions.length ≠ j.molecule.atomCount := by
      simpa only [← counts] using full
    simp only [RingChemicalReport.fromRaw?,no_admission i g full,no_admission j g bad']

/-- Independently certified preparation outputs can be compared after successful
structural readmission of their base graphs. Every generated variant is covered;
indeed the result holds for arbitrary coordinates. -/
theorem completed_outputs {s t : Input} {out out' : RawMolecule}
    {pos pos' : SpatialConfiguration} {i j : Input}
    (prepared : RingHydrogenCompletion.prepare? s.molecule s.spatial = some (out,pos))
    (prepared' : RingHydrogenCompletion.prepare? t.molecule t.spatial = some (out',pos'))
    (admitted : LocalizedChemicalRing.admitRawSpatial? out pos = some i)
    (admitted' : LocalizedChemicalRing.admitRawSpatial? out' pos' = some j)
    (atoms : out.atoms = out'.atoms) (bonds : out.bonds.Perm out'.bonds)
    (g : SpatialConfiguration) (ids : List Nat) :
    RingChemicalReport.fromRaw? out' g ids = RingChemicalReport.fromRaw? out g ids := by
  obtain ⟨im,_⟩ := RingChemicalReport.admission_fields admitted
  obtain ⟨jm,_⟩ := RingChemicalReport.admission_fields admitted'
  have closed := RingHydrogenCompletion.prepare?_closed prepared
  have closed' := RingHydrogenCompletion.prepare?_closed prepared'
  rw [← im] at atoms bonds closed
  rw [← jm] at atoms bonds closed'
  simpa only [im,jm] using at_coordinates i j atoms bonds closed closed' g ids

/-- Search depends only on the set of possible coordinate tables and their
per-geometry public rows. Enumeration order and multiplicity are unrestricted. -/
theorem search_eq (i j : Input)
    (atoms : i.molecule.atoms = j.molecule.atoms)
    (bonds : i.molecule.bonds.Perm j.molecule.bonds)
    (closed : plan i.molecule = []) (closed' : plan j.molecule = [])
    (sites sites' : List RingPyramidalChoices.Site)
    (base base' : List RingHydrogenCompletion.Point) (ids : List Nat)
    (members : ∀ ps, ps ∈ RingPyramidalChoices.choices sites base ↔
      ps ∈ RingPyramidalChoices.choices sites' base') :
    RingHydrogenReport.search? (fun ps => RingChemicalReport.fromRaw? j.molecule ⟨ps⟩ ids) sites' base' =
      RingHydrogenReport.search? (fun ps => RingChemicalReport.fromRaw? i.molecule ⟨ps⟩ ids) sites base := by
  apply Option.ext
  intro rows
  rw [RingHydrogenReport.search?_iff,RingHydrogenReport.search?_iff]
  constructor
  · intro all ps member
    rw [← at_coordinates i j atoms bonds closed closed' ⟨ps⟩ ids]
    exact all ps ((members ps).mp member)
  · intro all ps member
    rw [at_coordinates i j atoms bonds closed closed' ⟨ps⟩ ids]
    exact all ps ((members ps).mpr member)

end TetraStereo.Engine.RingBondVariantReadback
assert_kernel_only TetraStereo.Engine.RingBondVariantReadback.at_coordinates
assert_kernel_only TetraStereo.Engine.RingBondVariantReadback.completed_outputs
assert_kernel_only TetraStereo.Engine.RingBondVariantReadback.search_eq
