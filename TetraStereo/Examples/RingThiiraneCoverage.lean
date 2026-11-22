import TetraStereo.Engine.PublicAPI
import TetraStereo.Engine.RingConfiguredPriorities

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

namespace TetraStereo.Examples.RingThiiraneCoverage
open OneCenter Engine RingChemicalPriority LocalizedGenericMarkedRecalculation
open CertifiedLocalizedCIPInput LocalizedChemicalRingPhysicalAdmission LocalizedActualPhysicalBranchDecision

/-- 2-Methylthiirane (propylene sulfide). Carbons 1, 2 and sulfur 3 form
the three-membered ring. Methyl carbon 0 is attached to stereogenic carbon 1. -/
def molecule : RawMolecule where
  atoms := List.replicate 3 (.aliphatic .C) ++ [.aliphatic .S] ++ List.replicate 6 (.aliphatic .H)
  bonds := ([(0,1),(1,2),(2,3),(3,1),(0,4),(0,5),(0,6),(1,7),(2,8),(2,9)] :
    List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

private def moment (t : ℚ) : CartesianPoint3 := ⟨t,t*t,t*t*t⟩

/-- Rational test coordinates; four distinct sites always give nonzero volume. -/
def spatial : SpatialConfiguration := ⟨(List.range 10).map fun i => moment i⟩

def input := (LocalizedChemicalRing.admitRawSpatial? molecule spatial).get (by decide +kernel)

theorem admitted : LocalizedChemicalRing.admitRawSpatial? molecule spatial = some input :=
  (Option.some_get _).symm

private theorem points (a : input.certified.Atom) :
    input.certified.spatialPointAt? a = some (moment a.val) := by
  revert a
  decide +kernel

private theorem volume (a b c d : ℚ) :
    CartesianPoint3.orientedVolume (moment a) (moment b) (moment c) (moment d) =
      (d-a)*(a-b)*(a-c)*(b-c)*(b-d)*(c-d) := by
  unfold moment CartesianPoint3.orientedVolume
  ring

private theorem coordinates_of_points (acceptedInput : LocalizedChemicalRing.Input)
    (points : ∀ a : acceptedInput.certified.Atom, acceptedInput.certified.spatialPointAt? a = some (moment a.val)) :
    LocalizedChemicalRing.coordinatesAdmitted acceptedInput = true := by
  apply decide_eq_true
  intro center
  let lig := (actualCanonicalMolecule acceptedInput.certified).ligandAtomAt center
  let x (i : Fin 4) : ℚ := (lig i).val
  have distinct (i j : Fin 4) (ne : i ≠ j) : x i ≠ x j := by
    intro eqn
    apply ne
    apply (actualCanonicalMolecule acceptedInput.certified).ligandAtomAt_injective center
    apply Fin.ext
    change ((lig i).val : ℚ) = ((lig j).val : ℚ) at eqn
    exact_mod_cast eqn
  apply (centerAdmitted_iff _ _).mpr
  refine ⟨CartesianPoint3.orientedVolume (moment (x 0)) (moment (x 1))
    (moment (x 2)) (moment (x 3)),?_,?_⟩
  · simp [coordinateVolume?,points,x,lig]
  · change CartesianPoint3.orientedVolume (moment (x 0)) (moment (x 1))
      (moment (x 2)) (moment (x 3)) ≠ 0
    rw [volume]
    repeat' apply mul_ne_zero
    all_goals exact sub_ne_zero.mpr (distinct _ _ (by decide))

theorem coordinates : LocalizedChemicalRing.coordinatesAdmitted input = true := coordinates_of_points input points

theorem center_configured : 1 ∈ CentresRing.inventory input := by
  let atom : input.certified.Atom := ⟨1,by decide +kernel⟩
  have detected : atom ∈ input.certified.tetrahedralCenterSet := by decide +kernel
  exact List.mem_map.mpr ⟨⟨atom,detected⟩,(input.certified.mem_canonicalTetrahedralCenters_iff _).mpr detected,rfl⟩

/-- The three ring edges and the substituted carbon's independently
ranked incident atoms are exposed at the same site as the physical reading. -/
theorem cycle_and_priority :
    molecule.bondOrder 1 2 = 1 ∧ molecule.bondOrder 2 3 = 1 ∧ molecule.bondOrder 3 1 = 1 ∧
    atomicOrder? molecule [1] 2 = some [3,2,0,7] ∧
    readback? (fun i => spatial.positions[i]?) [3,2,0,7] = some .S := by
  decide +kernel

/-- A strict full atom-number order and its two geometric readings already
supply an independent molecular derivation for a publicly admitted input.
No restriction on elements in the rest of the molecule is used. -/
theorem strict_rule1a_derives (i : LocalizedChemicalRing.Input) {p order depth r}
    (ranking : atomicOrder? i.molecule p depth = some order)
    (spatialReading : Recursive.geometric (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
      order order = some r) :
    ReferenceDerivation.Derives i.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
      [] p (some r) := .atomic ranking spatialReading

theorem chemical_reading : ReferenceDerivation.Derives input.molecule
    (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified) [] [1] (some ⟨.S,.R⟩) := by
  apply strict_rule1a_derives input (depth := 2) (order := [3,2,0,7])
  · exact cycle_and_priority.2.2.2.1
  · decide +kernel

/-- The element-independent Rule 1a report covers the complete carbon
inventory. Carbon 1 reads S; the methyl and ring methylene have certified
pairs of identical terminal hydrogens. -/
theorem all_carbon_verdicts :
    (AtomicCarbonReport.check input 2).map AtomicCarbonReport.Report.labels =
      some [(0,none),(1,some (.chiral .S)),(2,none)] := by decide +kernel

theorem outside : saturatedWithHalogens molecule = false := by decide +kernel

theorem no_carbon_report_object (g : Geometry) : ¬ Nonempty (ReferenceCarbonReport molecule g) := by
  rintro ⟨report⟩
  have required := report.domain
  simp [outside] at required

/-- The independent carbon-report route has an elemental gate in addition
to public structural and physical admission. More comparison depth or
recursion fuel cannot discharge this gate. -/
theorem no_full_report (g : Geometry) (depth fuel : Nat) :
    deriveRingReferenceCarbons? molecule g depth fuel = none := by
  simp [deriveRingReferenceCarbons?,outside]

theorem no_derivation (g : Geometry) (depth fuel : Nat) (p : List Nat) :
    ReferenceDerivation.derive? molecule g depth fuel p = none := by
  cases fuel <;> simp [ReferenceDerivation.derive?,outside]

/-- The configured ranker also checks the same chemical domain before
assembling a four-ligand frame, regardless of the configuration inventory. -/
theorem no_configured_rank (g : Geometry) (cs : List Nat) (depth fuel : Nat) (p : List Nat) :
    CentresRing.ConfiguredPriority.rank? molecule g cs depth fuel p = none :=
  CentresRing.ConfiguredPriority.rank?_of_outside outside g cs depth fuel p

/-- Public admission and all-center calibration do not suffice for
returning an independent carbon report, even at the atom-count bound. -/
theorem exists_admitted_without_report :
    ∃ i : LocalizedChemicalRing.Input, LocalizedChemicalRing.coordinatesAdmitted i = true ∧
      (∀ depth, (deriveRingReferenceCarbonsAtBound? i.molecule
        (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) depth).isNone = true) := by
  refine ⟨input,coordinates,?_⟩
  intro depth
  change (deriveRingReferenceCarbons? molecule _ depth molecule.atomCount).isNone = true
  rw [no_full_report]
  rfl

/-- Rule 1a cannot give a strict four-ligand order when two distinct
incident cursors have the same atomic-number tree. -/
private theorem tied_trees {m : RawMolecule} {p : List Nat} {d : Nat}
    {f : RawMolecule.CanonicalBranchNode} {l r : CanonicalRerootCursor}
    (atFocus : occurrence? m p = some f)
    (left : l ∈ occurrenceLigandCursors m f) (right : r ∈ occurrenceLigandCursors m f)
    (distinct : l ≠ r) (tied : atomicTree m 3 d l = atomicTree m 3 d r) :
    atomicOrder? m p d = none := by
  unfold atomicOrder?
  cases h : atomicRanking? m p d with
  | none => rfl
  | some ranking =>
    exfalso
    have site : ranking.focus = f := Option.some.inj (ranking.reached.symm.trans atFocus)
    have ls := ranking.complete.mem_iff.mpr (show l ∈ occurrenceLigandCursors m ranking.focus by simpa [site] using left)
    have rs := ranking.complete.mem_iff.mpr (show r ∈ occurrenceLigandCursors m ranking.focus by simpa [site] using right)
    obtain ⟨a,ha,la⟩ := List.mem_map.mp ls
    obtain ⟨b,hb,rb⟩ := List.mem_map.mp rs
    rw [← la,← rb] at tied
    have trees := Option.some.inj (a.molecular.symm.trans (tied.trans b.molecular))
    have keys : a.key = b.key := by rw [a.exactKey,b.exactKey,trees]
    have unique : (ranking.arms.map AtomicArm.key).Nodup :=
      List.pairwise_map.mpr (ranking.strict.imp fun less => ne_of_gt less)
    have equal := List.inj_on_of_nodup_map unique ha hb keys
    exact distinct (la.symm.trans ((congrArg AtomicArm.cursor equal).trans rb))

def deuterated : RawMolecule := { molecule with
  atoms := molecule.atoms.set 8 { AtomSpec.aliphatic .H with isotope? := some 2 } }

def isotopeInput := (LocalizedChemicalRing.admitRawSpatial? deuterated spatial).get (by decide +kernel)

theorem isotope_admitted : LocalizedChemicalRing.admitRawSpatial? deuterated spatial = some isotopeInput :=
  (Option.some_get _).symm

theorem isotope_coordinates : LocalizedChemicalRing.coordinatesAdmitted isotopeInput = true :=
  coordinates_of_points isotopeInput (by decide +kernel)

private def chd := (occurrence? deuterated [2]).get (by decide +kernel)
private def h8 := ((occurrenceLigandCursors deuterated chd).find? fun c => c.node.atom == 8).get (by decide +kernel)
private def h9 := ((occurrenceLigandCursors deuterated chd).find? fun c => c.node.atom == 9).get (by decide +kernel)

/-- The two specific terminal occurrences give strictly ordered Rule 2 masses. -/
theorem isotope_mass_distinct :
    ∃ d h : AtomSpec, deuterated.atoms[h8.node.atom]? = some d ∧
      deuterated.atoms[h9.node.atom]? = some h ∧
      (CIPRule2MassData.rule2MassPico? h.element.atomicNumber h.isotope?).getD 0 <
        (CIPRule2MassData.rule2MassPico? d.element.atomicNumber d.isotope?).getD 0 := by
  exact ⟨{ AtomSpec.aliphatic .H with isotope? := some 2 },AtomSpec.aliphatic .H,
    by decide +kernel,by decide +kernel,CIPRule2MassData.ordinary_hydrogen_lt_deuterium⟩

private theorem equal_z (d : Nat) : atomicTree deuterated 3 d h8 = atomicTree deuterated 3 d h9 := by
  have left : deuterated.atoms[h8.node.atom]? = some {AtomSpec.aliphatic .H with isotope? := some 2} := by decide +kernel
  have right : deuterated.atoms[h9.node.atom]? = some (AtomSpec.aliphatic .H) := by decide +kernel
  have leaf : h8.children deuterated = [] := by decide +kernel
  have other : h9.children deuterated = [] := by decide +kernel
  cases d <;> simp [atomicTree,left,right,leaf,other,AtomSpec.aliphatic]

theorem isotope_priority_tie (d : Nat) : atomicOrder? deuterated [2] d = none :=
  tied_trees (Option.some_get _).symm (by decide +kernel : h8 ∈ occurrenceLigandCursors deuterated chd)
    (by decide +kernel : h9 ∈ occurrenceLigandCursors deuterated chd) (by decide +kernel) (equal_z d)

/-- At the ring CHD site, the two hydrogen sites have identical Rule 1a
trees at every depth but different isotopes. This substitution puts an
admitted molecule beyond both public whole-carbon constructors. -/
theorem isotope_reports_unresolved (d fuel : Nat) :
    (AtomicCarbonReport.check isotopeInput d).isNone = true ∧
    (deriveRingReferenceCarbons? isotopeInput.molecule
      (LocalizedChemicalRingPhysicalSense.inputGeometry isotopeInput.certified) d fuel).isNone = true := by
  constructor
  · cases found : AtomicCarbonReport.check isotopeInput d with
    | none => rfl
    | some report =>
      have hits := (AtomicCarbonReport.check_isSome_iff isotopeInput d).mp (by rw [found]; rfl)
      have missing : RingCarbonReport.hydrogens? isotopeInput.molecule 2 = none := by decide +kernel
      rcases hits 2 (by decide +kernel) with equalPair | ⟨order,r,ranked,_⟩
      · simp [missing] at equalPair
      · change atomicOrder? deuterated [2] d = some order at ranked
        simp [isotope_priority_tie] at ranked
  · have excluded : saturatedWithHalogens isotopeInput.molecule = false := by decide +kernel
    simp [deriveRingReferenceCarbons?,excluded]

end TetraStereo.Examples.RingThiiraneCoverage

assert_kernel_only TetraStereo.Examples.RingThiiraneCoverage.admitted
assert_kernel_only TetraStereo.Examples.RingThiiraneCoverage.coordinates
assert_kernel_only TetraStereo.Examples.RingThiiraneCoverage.cycle_and_priority
assert_kernel_only TetraStereo.Examples.RingThiiraneCoverage.no_derivation
assert_kernel_only TetraStereo.Examples.RingThiiraneCoverage.no_configured_rank
assert_kernel_only TetraStereo.Examples.RingThiiraneCoverage.exists_admitted_without_report

assert_kernel_only TetraStereo.Examples.RingThiiraneCoverage.chemical_reading
assert_kernel_only TetraStereo.Examples.RingThiiraneCoverage.center_configured
assert_kernel_only TetraStereo.Examples.RingThiiraneCoverage.all_carbon_verdicts
assert_kernel_only TetraStereo.Examples.RingThiiraneCoverage.isotope_coordinates
assert_kernel_only TetraStereo.Examples.RingThiiraneCoverage.isotope_mass_distinct
assert_kernel_only TetraStereo.Examples.RingThiiraneCoverage.isotope_reports_unresolved
